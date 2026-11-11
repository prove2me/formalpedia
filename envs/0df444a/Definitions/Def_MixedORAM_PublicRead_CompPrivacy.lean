-- Prove2me | Definitions.Def_MixedORAM_PublicRead_CompPrivacy
-- name    : MixedORAM_PublicRead_CompPrivacy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:48:15.320202+00:00
-- url     : https://prove2.me/theorems/32826902-99e1-4d54-b172-6c532ff8f953
-- title:
--   Encodings, samplers, truncated traces and computational trace privacy of implementation families
-- statement:
--   An **implementation family** $A$ gives, for each security parameter $\kappa$ and public parameters $P=(n,w,m,a,N,p,Q)$, an implementation $A_\kappa(P)$. Parameters lie in the **polynomial range** $d$ at $\kappa$ when $n,w,m,a,N,1/p,Q\le(\kappa+2)^d$.
--
--   A **sampler** for a parameter sequence $\pi$ is a multi-output Boolean circuit family $S_\kappa$ on uniform random coins together with the object $(A_0,u_0,u_1,z)$ it outputs (an initial array, two request lists and auxiliary information $z$); it is **valid** for a leakage if its coin count and circuit size are at most $(\kappa+2)^c$, its circuit outputs the fixed injective code of the object on every coin string, and every sampled pair $u_0,u_1$ is comparable.
--
--   The **truncated trace** $\mathrm{Tr}_{\le b}$ is the whole trace with the flag $0$ if it has at most $b$ probes, and otherwise its prefix up to the $b$-th probe with the overflow flag $1$.
--
--   A family is **computationally trace private** under a leakage if for every parameter sequence $\pi$ in a polynomial range, every valid sampler, every polynomial cutoff $b(\kappa)\le(\kappa+2)^c$ and every polynomial-size distinguisher $D$,
--   $$\Big|\Pr[D(z,\mathrm{Tr}_{\le b}(A_\kappa(u_1)))=1]-\Pr[D(z,\mathrm{Tr}_{\le b}(A_\kappa(u_0)))=1]\Big|$$
--   is negligible in $\kappa$, both inputs running from the sampled initial array. The module also defines, for a sampler and an event $E(\kappa,z,\mathrm{tr})$, the probability of $E$ on the trace of $u_0$ or $u_1$, and the expected probe count (preprocessing included) of those executions.
--
--   **Formalization Note** Distinguishers are the published `NoisyOWMPC.Distinguisher` (polynomial-size circuits, deterministic: the best coins of a nonuniform distinguisher can be hard-wired), negligibility is the published `NoisyOWMPC.Negligible`, samplers use the published `LaconicBarrier.MCircuit`. Codes: self-delimiting binary codes for numbers, strings and request lists; words least significant bit first; a trace symbol is $0$ for a boundary and $1$, the direction bit and the $a$ address bits for a probe.
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 5, §2.2; pp. 75–76, Appendix G

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_NoisyOWMPC_Distinguisher
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_MixedORAM_PublicRead_Workload

set_option autoImplicit false

namespace MixedORAM.PublicRead

/-! Bit-string codes. The paper fixes no encoding; any polynomial-time, injective one serves. -/

/-- Self-delimiting code of a bit string: each bit `b` becomes `1b`, and a final `0` ends it. -/
def encStr (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false]

/-- Self-delimiting binary code of a natural number. -/
def encNat (x : ℕ) : List Bool := encStr (Nat.bits x)

/-- The `w` bits of a word, least significant first. -/
def encWord {w : ℕ} (v : BitVec w) : List Bool := List.ofFn (fun i : Fin w => v.getLsbD i)

/-- Code of one request: mode bit (`true` = private), kind bit (`true` = write), the address, and
the written word for a write. -/
def encReq {n w : ℕ} (r : Request n w) : List Bool :=
  [decide (r.mode = .priv), decide (r.op.kind = .write)] ++ encNat r.op.addr.val ++
    (match r.op with
      | .write _ v => encWord v
      | .read _ => [])

/-- Code of a request list: its length, then every request. -/
def encReqs {n w : ℕ} (u : List (Request n w)) : List Bool :=
  encNat u.length ++ u.flatMap encReq

/-- Code of an initial array: its `n` words in order. -/
def encArray {n w : ℕ} (A₀ : Fin n → BitVec w) : List Bool := (List.ofFn A₀).flatMap encWord

/-- The public parameters of one instance (§2.3, p. 5; Appendix G, p. 76): array size `n`, word
size `w`, client words `m`, physical address width `a`, horizon `N`, private probability `p` and
private budget `Q`. -/
structure Params where
  n : ℕ
  w : ℕ
  m : ℕ
  a : ℕ
  N : ℕ
  p : ℝ
  Q : ℝ

/-- The parameters lie in the polynomial range `(κ + 2)^d` (Appendix G, p. 76: "fixed polynomial
parameter bounds"; §2.3, p. 5: "In the computational setting, parameters, horizons, budgets, and
1/p are polynomially bounded"). -/
def Params.Within (d κ : ℕ) (P : Params) : Prop :=
  P.n ≤ (κ + 2) ^ d ∧ P.w ≤ (κ + 2) ^ d ∧ P.m ≤ (κ + 2) ^ d ∧ P.a ≤ (κ + 2) ^ d ∧
    P.N ≤ (κ + 2) ^ d ∧ 1 / P.p ≤ ((κ + 2 : ℕ) : ℝ) ^ d ∧ P.Q ≤ ((κ + 2 : ℕ) : ℝ) ^ d

/-- An **implementation family** `A = (A_κ)`: for each security parameter `κ` and public parameters
`P`, an implementation with those parameters (Appendix G, p. 75: "let A_κ denote the randomized ORAM
implementation at that security parameter"; "Public parameters may be part of z"). -/
abbrev Family := (κ : ℕ) → (P : Params) → Impl P.n P.w P.m P.a

/-- A sampled object: an initial array, two request lists and auxiliary information `z`. -/
structure InputPair (n w : ℕ) where
  A₀ : Fin n → BitVec w
  u₀ : List (Request n w)
  u₁ : List (Request n w)
  z : List Bool

/-- The code of a sampled object. -/
def InputPair.enc {n w : ℕ} (x : InputPair n w) : List Bool :=
  encArray x.A₀ ++ encReqs x.u₀ ++ encReqs x.u₁ ++ encStr x.z

/-- A **sampler** for the parameter sequence `π`: at security parameter `κ`, a multi-output circuit
`circ κ` (published `LaconicBarrier.MCircuit`) on `coins κ` uniform random bits, and the object
`gen κ ρ` it outputs on the coins `ρ`. -/
structure Sampler (π : ℕ → Params) where
  coins : ℕ → ℕ
  circ : (κ : ℕ) → LaconicBarrier.MCircuit (coins κ)
  gen : (κ : ℕ) → (Fin (coins κ) → Bool) → InputPair (π κ).n (π κ).w

/-- A **nonuniform polynomial-time sampler of comparable input pairs** (Appendix G, p. 75: "every
nonuniform polynomial-time sampler that produces comparable inputs (u₀, u₁) and polynomial-length
auxiliary information z independently of the implementation's coins"): polynomially many coins and
polynomial circuit size, the circuit outputs the code of `gen κ ρ` on every coin string, and every
sampled pair is comparable under the leakage `k` (both lists run from the same initial array). -/
def Sampler.Valid {π : ℕ → Params} (k : LeakKind) (S : Sampler π) : Prop :=
  (∃ c : ℕ, ∀ κ, S.coins κ ≤ (κ + 2) ^ c ∧ (S.circ κ).size ≤ (κ + 2) ^ c) ∧
    ∀ (κ : ℕ) (ρ : Fin (S.coins κ) → Bool),
      (S.circ κ).eval (List.ofFn ρ) = (S.gen κ ρ).enc ∧
        Comparable k (S.gen κ ρ).u₀ (S.gen κ ρ).u₁

/-- A trace as one sequence of symbols: `some q` for a probe, `none` for the end of the
preprocessing and for the end of each request. -/
def flatTrace {a : ℕ} (tr : Trace a) : List (Option (Probe a)) :=
  tr.1.map some ++ [none] ++ tr.2.flatMap (fun ps => ps.map some ++ [none])

/-- The number of probes in a symbol sequence. -/
def symProbes {a : ℕ} (s : List (Option (Probe a))) : ℕ := (s.filter Option.isSome).length

/-- The symbols up to and including the `b`-th probe. -/
def upToProbes {a : ℕ} : ℕ → List (Option (Probe a)) → List (Option (Probe a))
  | _, [] => []
  | 0, _ => []
  | b + 1, none :: s => none :: upToProbes (b + 1) s
  | b + 1, some q :: s => some q :: upToProbes b s

/-- The **truncated trace** `Tr_{≤b}` (Appendix G, p. 75: "the trace truncated after b probes, with
a marked overflow if the execution exceeds the cutoff"): the whole trace and the flag `false` if it
has at most `b` probes; otherwise its symbols up to the `b`-th probe and the flag `true`. -/
def truncTrace {a : ℕ} (b : ℕ) (s : List (Option (Probe a))) : List (Option (Probe a)) × Bool :=
  if symProbes s ≤ b then (s, false) else (upToProbes b s, true)

/-- Code of one trace symbol: `0` for a request boundary; `1`, the direction bit and the `a` address
bits for a probe. -/
def encSym {a : ℕ} : Option (Probe a) → List Bool
  | none => [false]
  | some q => true :: q.isWrite :: List.ofFn (fun i : Fin a => q.addr.getLsbD i)

/-- Code of a truncated trace: the overflow flag, then the symbols. -/
def encTrunc {a : ℕ} (t : List (Option (Probe a)) × Bool) : List Bool :=
  t.2 :: t.1.flatMap encSym

/-- The probability that the distinguisher `D` accepts `(z, Tr_{≤b(κ)}(A_κ(u_j)))` when the
sampler `S` draws `(A₀, u₀, u₁, z)` from uniform coins (`j = false`: `u₀`; `j = true`: `u₁`). -/
noncomputable def accProb (A : Family) {π : ℕ → Params} (S : Sampler π)
    (D : NoisyOWMPC.Distinguisher) (b : ℕ → ℕ) (κ : ℕ) (j : Bool) : ℝ :=
  ∑ ρ : Fin (S.coins κ) → Bool, (1 / 2 ^ S.coins κ : ℝ) *
    (((A κ (π κ)).traceDist (S.gen κ ρ).A₀
        (if j then (S.gen κ ρ).u₁ else (S.gen κ ρ).u₀)).toOuterMeasure
      {tr | D.acc κ (encStr (S.gen κ ρ).z ++ encTrunc (truncTrace (b κ) (flatTrace tr))) = true}
    ).toReal

/-- **Computational trace privacy** of a family under the leakage `k` (Appendix G, p. 75): for every
polynomially bounded parameter sequence, every nonuniform polynomial-time sampler of comparable input
pairs with auxiliary information, every polynomial probe cutoff `b(κ)` and every nonuniform
polynomial-size distinguisher (published `NoisyOWMPC.Distinguisher`), the distinguishing advantage
on `(z, Tr_{≤b}(A_κ(u₀)))` versus `(z, Tr_{≤b}(A_κ(u₁)))` is negligible (published
`NoisyOWMPC.Negligible`). -/
def CompPrivate (k : LeakKind) (A : Family) : Prop :=
  ∀ (d : ℕ) (π : ℕ → Params), (∀ κ, (π κ).Within d κ) →
    ∀ S : Sampler π, S.Valid k →
      ∀ b : ℕ → ℕ, (∃ c : ℕ, ∀ κ, b κ ≤ (κ + 2) ^ c) →
        ∀ D : NoisyOWMPC.Distinguisher, D.IsPoly →
          NoisyOWMPC.Negligible (fun κ => |accProb A S D b κ true - accProb A S D b κ false|)

/-- The probability, over the sampler's coins and the implementation's randomness, that the event
`E κ z tr` holds for the auxiliary information `z` and the observed trace `tr` of `A_κ` on the input
`(A₀, u_j)` drawn by `S` (`j = false`: `u₀`; `j = true`: `u₁`). -/
noncomputable def samplerEventProb (A : Family) {π : ℕ → Params} (S : Sampler π)
    (E : (κ : ℕ) → List Bool → Trace (π κ).a → Bool) (κ : ℕ) (j : Bool) : ℝ :=
  ∑ ρ : Fin (S.coins κ) → Bool, (1 / 2 ^ S.coins κ : ℝ) *
    (((A κ (π κ)).traceDist (S.gen κ ρ).A₀
        (if j then (S.gen κ ρ).u₁ else (S.gen κ ρ).u₀)).toOuterMeasure
      {tr | E κ (S.gen κ ρ).z tr = true}).toReal

/-- The expected number of probes, preprocessing included, of `A_κ` on the input `(A₀, u_j)` drawn
by `S`, over the sampler's coins and the implementation's randomness (the expected length of the
exact trace). -/
noncomputable def samplerExpProbes (A : Family) {π : ℕ → Params} (S : Sampler π) (κ : ℕ)
    (j : Bool) : ENNReal :=
  ∑ ρ : Fin (S.coins κ) → Bool, (1 / 2 ^ S.coins κ : ENNReal) *
    pexp ((A κ (π κ)).run (S.gen κ ρ).A₀ (if j then (S.gen κ ρ).u₁ else (S.gen κ ρ).u₀))
      (fun x => ((x.1.length + totalProbes x.2 : ℕ) : ENNReal))

end MixedORAM.PublicRead


