-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_SECProtocol
-- name    : NoisyOWMPC_Supplement_SECProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:18.235294+00:00
-- url     : https://prove2.me/theorems/6e6c7cb3-1d8b-4ad7-8a86-df68b2866977
-- title:
--   One-way protocols over the string erasure channel, and random string OT
-- statement:
--   **Random string OT** $\mathrm{ROT}^\ell$ is the one-receiver randomized functionality
--   $$
--   \mathrm{ROT}^\ell(m_0, m_1) = (b, m_b), \qquad b \leftarrow \{0,1\}, \quad (m_0, m_1) \in (\{0,1\}^\ell)^2 ,
--   $$
--   written as a target circuit whose coin is the bit $b$; the sender receives no output.
--
--   The **string erasure channel** $\mathrm{SEC}^{N,L}_{1/2}$ delivers each of $N$ strings $x_v \in \{0,1\}^{L}$ independently with probability $1/2$: the receiver obtains $(V, x|_V)$ for a uniform subset $V \subseteq [N]$, where $x|_V$ has $\perp$ outside $V$. A one-way protocol over it consists of a randomized sender $S(1^\lambda, x) \to (\tau, x)$ with a public message $\tau \in \{0,1\}^{L_\tau}$ and $N$ strings, and a deterministic receiver $R(1^\lambda, \tau, x|_V)$ with output in $\mathcal O \cup \{\mathsf{fail}\}$.
--
--   For such a protocol the module defines, exactly as Definition 4.2 does for a fixed alphabet:
--
--   1. the **correctness error**: $\mathrm{SD}(y, F(x)) \le \varepsilon_{\mathrm{cor}}$ for every input;
--   2. the **receiver security error** $\varepsilon_{\{1\}}$: a PPT simulator with $(x, \mathrm{view}_1) \approx^c_{\varepsilon_{\{1\}}} (x, \mathrm{Sim}(1^\lambda, \perp, \bar y))$;
--   3. the **statistical sender security error** $\varepsilon_S$: the statistical distance between $(x, y, \mathrm{view}_S)$ and $(x, \bar y, \mathrm{view}'_S)$, where $\mathrm{view}'_S$ is a fresh run of the sender independent of the ideal output $\bar y$;
--   4. the **Las Vegas** property and **efficiency** (polynomial lengths, a sender implementable within $2^{-\lambda}$, a polynomial-time receiver).
--
--   These are the notions in which Theorem D.4 is stated.
--
--   **Formalization Note** The string length grows with $\lambda$ (Remark D.7), so the channel alphabet is indexed by $\lambda$; the receiver's observation is the partial word $x|_V$, from which $V$ is read off. The statistical sender simulator is the paper's rerun of the sender with its exact reference coin law.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §4.2 Special cases (ROT^ℓ), p.19; Definition 4.2, pp.18–19; App. D (SEC^{N,L}_{1/2}), p.57; Remark D.7, p.60

import Mathlib
import Definitions.Def_NoisyOWMPC_SecErr

namespace NoisyOWMPC.Supplement

open LaconicBarrier

/-- **Random string OT** `ROT^ℓ` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), §4.2 Special cases, p.19: "Random string OT is the single-receiver functionality
`ROT^ℓ(m₀, m₁) = (b, m_b)`, `b ←r {0,1}`, `(m₀, m₁) ∈ ({0,1}^ℓ)²`"), as a one-receiver functionality
with target circuit `f(m₀m₁; b) = (b, m_b)`: the input is `m₀` followed by `m₁`, the coin is the one
bit `b`, and the output is `b` followed by `m_b`. The sender receives no output. -/
def rotF (ℓ : ℕ → ℕ) : Functionality 1 where
  lx lam := ℓ lam + ℓ lam
  r _ _ := 1
  lo _ lam := ℓ lam + 1
  f lam _ x ρ := Fin.cons (α := fun _ => Bool) (ρ 0)
    (fun j => if ρ 0 then x (Fin.natAdd (ℓ lam) j) else x (Fin.castAdd (ℓ lam) j))

/-- A **one-way protocol over a string erasure channel** for a one-receiver functionality `F`
(STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 4.2, pp.18–19, over the channel of
App. D, p.57: "Write `SEC^{N,L}_{1/2}` for `N` independent uses of an `L`-bit string erasure channel
with erasure probability `1/2`"): the sender `S(1^λ, x; r_S) → (τ, x)` with exact coin law `wS λ`
outputs a public message `τ ∈ {0,1}^{L_τ}` and `N` strings `x_v ∈ {0,1}^{L_s}`; the receiver
`R(1^λ, τ, x|_V)` decodes the public message and its partial word (`none` is `fail`).

**Formalization Note** The string length `L_s(λ)` grows with `λ` (Remark D.7, p.60), so the
channel alphabet `{0,1}^{L_s} ∪ {⊥}` is indexed by `λ`; this is the one-receiver protocol syntax of
the published `Protocol` with that alphabet. The receiver's observation `(V, x|_V)` is the partial
word `x|_V` (`none` is `⊥`), from which `V` is read off. -/
structure SECProtocol (F : Functionality 1) where
  /-- the sender's coin space -/
  RS : ℕ → Type
  [finRS : ∀ lam, Fintype (RS lam)]
  /-- the law of the sender's coins -/
  wS : (lam : ℕ) → RS lam → ℝ
  /-- the encoding of the sender's coins -/
  encRS : (lam : ℕ) → RS lam → List Bool
  /-- the noiseless message length -/
  L : ℕ → ℕ
  /-- the number `N` of string-erasure channel uses -/
  N : ℕ → ℕ
  /-- the string length `L_s` -/
  Ls : ℕ → ℕ
  /-- the sender -/
  send : (lam : ℕ) → (Fin (F.lx lam) → Bool) → RS lam →
    (Fin (L lam) → Bool) × (Fin (N lam) → Fin (Ls lam) → Bool)
  /-- the receiver -/
  recv : (lam : ℕ) → (Fin (L lam) → Bool) → (Fin (N lam) → Option (Fin (Ls lam) → Bool)) →
    Option (Fin (F.lo 0 lam) → Bool)

attribute [instance] SECProtocol.finRS

/-- The partial word `x|_V`: `x_v` at the delivered positions `v ∈ V`, `⊥` (`none`) elsewhere (p.57). -/
def eraseOut {N : ℕ} {S : Type} (x : Fin N → S) (V : Finset (Fin N)) : Fin N → Option S :=
  fun p => if p ∈ V then some (x p) else none

/-- The encoding of a string-erasure output symbol: `⊥` is `0` followed by `L` zeros, a delivered
string `u` is `1u` (fixed width `L + 1`). -/
def secSym {L : ℕ} : Option (Fin L → Bool) → List Bool
  | none => false :: List.replicate L false
  | some u => true :: bits u

/-- The encoding of a partial word: its symbols' codes in order. -/
def secObsEnc {N L : ℕ} (u : Fin N → Option (Fin L → Bool)) : List Bool :=
  (List.ofFn fun p => secSym (u p)).flatten

/-- The encoding of a channel input word `x ∈ ({0,1}^L)^N`: its strings in order. -/
def secInEnc {N L : ℕ} (x : Fin N → Fin L → Bool) : List Bool :=
  (List.ofFn fun p => bits (x p)).flatten

variable {F : Functionality 1}

/-- The **real execution** over `SEC^{N,L}_{1/2}` (p.57: "the receiver obtains `(V, x|_V)` for a
uniform subset `V ⊆ [N]` of non-erased positions"; "The sender fixes the channel inputs and public
message before the erasure bits are sampled"): the weight `w_S(r_S) · 2^{−N}` of the sender's coins
`r_S` and the delivered set `V`. -/
noncomputable def SECProtocol.realW (P : SECProtocol F) (lam : ℕ) (_x : Fin (F.lx lam) → Bool)
    (ω : P.RS lam × Finset (Fin (P.N lam))) : ℝ :=
  P.wS lam ω.1 * (1 / 2 : ℝ) ^ (P.N lam)

/-- The receiver's decoded output `y = R(1^λ, τ, x|_V)` in the real execution. -/
def SECProtocol.out (P : SECProtocol F) (lam : ℕ) (x : Fin (F.lx lam) → Bool)
    (ω : P.RS lam × Finset (Fin (P.N lam))) : Option (Fin (F.lo 0 lam) → Bool) :=
  P.recv lam (P.send lam x ω.1).1 (eraseOut (P.send lam x ω.1).2 ω.2)

/-- **Correctness error** `ε_cor` (Definition 4.2, p.19): `SD(y, F(x)) ≤ ε_cor(λ)` for every `λ`
and `x`. -/
def SECProtocol.CorrErr (P : SECProtocol F) (ε : ℕ → ℝ) : Prop :=
  ∀ lam (x : Fin (F.lx lam) → Bool),
    sdPush (P.realW lam x) (fun ω => P.out lam x ω)
      (unifW (Fin (F.r 0 lam) → Bool)) (fun ρ => some (F.f lam 0 x ρ)) ≤ ε lam

/-- The encoding of the real tuple `(x, view_1)` for the receiver coalition `{1}` (Definition 4.2,
(4.1), p.19), in the layout of the published `Protocol.realTuple`: `x`, the (empty) outputs of the
honest receivers, and the view `(τ, x|_V)`. -/
noncomputable def SECProtocol.realTupleR (P : SECProtocol F) (lam : ℕ) (x : Fin (F.lx lam) → Bool)
    (ω : P.RS lam × Finset (Fin (P.N lam))) : List Bool :=
  QAdvFew.PoQOracle.tup [bits x, QAdvFew.PoQOracle.tup [],
    QAdvFew.PoQOracle.tup [QAdvFew.PoQOracle.tup [bits (P.send lam x ω.1).1,
      secObsEnc (eraseOut (P.send lam x ω.1).2 ω.2)]]]

/-- The encoding of the ideal tuple `(x, Sim_{1}(1^λ, ⊥, ȳ))` with ideal coins `ρ` and simulator
coins `σ` (Definition 4.2, (4.1), p.19), in the layout of the published `idealTuple`. -/
def idealTupleR (F : Functionality 1) (Sim : CoinAlg) (lam : ℕ) (x : Fin (F.lx lam) → Bool)
    (ω : (Fin (F.r 0 lam) → Bool) × (Fin (Sim.coins lam) → Bool)) : List Bool :=
  QAdvFew.PoQOracle.tup [bits x, QAdvFew.PoQOracle.tup [],
    Sim.run lam (QAdvFew.PoQOracle.tup [[false],
      QAdvFew.PoQOracle.tup [optEnc (some (F.f lam 0 x ω.1))]]) ω.2]

/-- **Receiver security error** `ε_{1}` (Definition 4.2, (4.1), p.19): a PPT simulator `Sim_{1}`
with `(x, view_1) ≈^c_{ε_{1}} (x, Sim_{1}(1^λ, ⊥, ȳ))` for every `x`, `ȳ ← F(x)`. -/
def SECProtocol.SecErrRecv (P : SECProtocol F) (ε : ℕ → ℝ) : Prop :=
  ∃ Sim : CoinAlg, Sim.IsPPT ∧
    CompClose (I := fun lam => Fin (F.lx lam) → Bool) P.realW P.realTupleR
      (fun lam _ => unifW ((Fin (F.r 0 lam) → Bool) × (Fin (Sim.coins lam) → Bool)))
      (idealTupleR F Sim) ε

/-- The encoding of the sender's view `view_S = (r_S, τ, x)` (Definition 4.2, p.18). -/
noncomputable def SECProtocol.viewS (P : SECProtocol F) (lam : ℕ) (x : Fin (F.lx lam) → Bool)
    (r : P.RS lam) : List Bool :=
  QAdvFew.PoQOracle.tup [QAdvFew.PoQOracle.tup [P.encRS lam r, bits (P.send lam x r).1,
    secInEnc (P.send lam x r).2]]

/-- **Statistical sender security error** `ε_S` (Definition 4.2, (4.1), p.19, with `≈_s` in place
of `≈^c`; App. D, p.60: "For the sender, the simulator runs the sender on `(m₀, m₁)` and outputs its
random coins, the strings `x`, and the program `P̃`"): for every `λ` and `x`,
`SD((x, y, view_S), (x, ȳ, view′_S)) ≤ ε_S(λ)`, where `view′_S` is a fresh run of the sender,
independent of the ideal output `ȳ ← F(x)`.

**Formalization Note** The simulator is the rerun of the sender with its exact reference coin law
(§5 Conventions, p.21; Sampling convention, p.24); its polynomial-time implementation within
`2^{−λ}` is the sender clause of `SECProtocol.IsEfficient`. The bound holds against every
distinguisher. -/
def SECProtocol.SecErrStatS (P : SECProtocol F) (ε : ℕ → ℝ) : Prop :=
  ∀ lam (x : Fin (F.lx lam) → Bool),
    sdPush (P.realW lam x)
      (fun ω => QAdvFew.PoQOracle.tup [bits x, QAdvFew.PoQOracle.tup [optEnc (P.out lam x ω)],
        P.viewS lam x ω.1])
      (fun ω : (Fin (F.r 0 lam) → Bool) × P.RS lam => unifW (Fin (F.r 0 lam) → Bool) ω.1 * P.wS lam ω.2)
      (fun ω => QAdvFew.PoQOracle.tup [bits x,
        QAdvFew.PoQOracle.tup [optEnc (some (F.f lam 0 x ω.1))], P.viewS lam x ω.2]) ≤ ε lam

/-- **Las Vegas** (Definition 4.3, p.19): every output other than `fail` lies in the support of
`f(x; ρ)`. -/
def SECProtocol.LasVegas (P : SECProtocol F) : Prop :=
  ∀ lam (x : Fin (F.lx lam) → Bool) (ω : P.RS lam × Finset (Fin (P.N lam))),
    P.realW lam x ω ≠ 0 → P.out lam x ω = none ∨ ∃ ρ, P.out lam x ω = some (F.f lam 0 x ρ)

/-- **Efficiency** (Definition 4.2, p.18; §3, p.15; §5 Conventions, p.21): `L`, `N`, `L_s` are
polynomially bounded, the sender is implementable in polynomial time within statistical distance
`2^{−λ}` (its output being its view), and the receiver is deterministic polynomial time. -/
def SECProtocol.IsEfficient (P : SECProtocol F) : Prop :=
  PolyBounded P.L ∧ PolyBounded P.N ∧ PolyBounded P.Ls ∧
  Samplable (I := fun lam => Fin (F.lx lam) → Bool) (fun lam _ => P.wS lam)
    (fun lam x r => QAdvFew.PoQOracle.tup [P.encRS lam r, bits (P.send lam x r).1,
      secInEnc (P.send lam x r).2]) (fun _ x => bits x) ∧
  PolyTimeOn (ι := (lam : ℕ) × (Fin (P.L lam) → Bool) × (Fin (P.N lam) → Option (Fin (P.Ls lam) → Bool)))
    (fun z => [unary z.1, bits z.2.1, secObsEnc z.2.2]) (fun z => optEnc (P.recv z.1 z.2.1 z.2.2))

end NoisyOWMPC.Supplement


