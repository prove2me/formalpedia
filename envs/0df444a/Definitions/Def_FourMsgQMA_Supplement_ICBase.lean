-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_ICBase
-- name    : FourMsgQMA_Supplement_ICBase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:23:06.495256+00:00
-- url     : https://prove2.me/theorems/98007643-efa6-41e9-8cbf-db2e0e001ee2
-- title:
--   Independent-challenge base protocols with short keys (Def 3.8, §7.1)
-- statement:
--   An **independent-challenge base protocol** (Definition 3.8) for a QMA promise problem $L$ has an instance-dependent setup $(PK_0,r)\leftarrow\mathrm{Gen}(1^\lambda,x,T)$, a first response $\mu$, a uniform challenge $c\in\{0,1\}^m$ independent of setup and of the response, with $m=\mathrm{poly}(\lambda,|x|,\log T)$, a last response $z$, and a deterministic verdict $V(x,PK_0,r,\mu,c,z)$.
--
--   1. **Uniformity and size bounds**: all algorithms are polynomial time; keys, state, accepted responses, the verdict circuit, the honest prover and its copy count are $\mathrm{poly}(\lambda,T)$, and $m\le\mathrm{poly}(\lambda,|x|,\log(T+1))$.
--   2. **Completeness**: overwhelming acceptance for every $x\in L_{\mathrm{yes}}$ and the honest resource of $N(\lambda,T)$ copies of any $\rho\in W_Q(x,2/3)$.
--   3. **Selective soundness** $s$: for every fixed sequence $x_\lambda\in L_{\mathrm{no}}$ and every QPT adversary, acceptance is at most $s(\lambda)+\nu(\lambda)$ for a negligible $\nu$.
--   4. **Short keys** (§7.1): $PK_0$ and the first component of $r$ are the public and secret keys output by a key generator $\mathrm{KGen}(1^\lambda)$ whose coins, key lengths and running time are $\mathrm{poly}(\lambda)$, independent of $x$ and $T$.
--
--   This is the base of the six-message compiler (Theorems 7.1 and 7.5).
--
--   **Formalization Note** As for the published `FourMsgQMA.BaseProtocol`: $T=t_L(x)$; adversaries are `IsQPT` strategies; the honest prover is a uniformly generated quantum core.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Definition 3.8, pp.13–14 (PDF 15–16); §7.1, pp.49–50 (PDF 51–52)

import Mathlib
import Definitions.Def_FourMsgQMA_WQ
import Definitions.Def_FourMsgQMA_Core

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), Definition 3.8 (pp.13–14, PDF 15–16) and
§7.1 (pp.49–50, PDF 51–52): independent-challenge base protocols. "Allow setup
`(PK₀, r) ← Gen(1^λ, x, T)` to depend on the fixed instance. The second verifier message is a
uniform string `c ∈ {0,1}^m` independent of setup and the prover's response, where
`m = poly(λ, |x|, log T)`. The deterministic verdict is `V(x, PK₀, r, µ, c, z)` … The remaining
syntax is as above."

Pinned-down version (operator request), as for the published `FourMsgQMA.BaseProtocol`: the
resource parameter `T` is `t_L(x)` (`localCost`); the honest resource is `N(λ, T)` copies of a
witness `ρ ∈ W_Q(x, 2/3)`; the honest prover is a uniformly generated quantum core; adversaries
are the published `IsQPT` strategies.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- An independent-challenge base protocol (Definition 3.8). -/
structure ICBase where
  /-- The number of coins of `Gen` at `(λ, |x|, T)`. -/
  genCoins : ℕ → ℕ → ℕ → ℕ
  /-- `(PK₀, r) ← Gen(1^λ, x, T)`, with coins. -/
  gen : ℕ → Bits → ℕ → Bits → Bits × Bits
  /-- The challenge length `m(λ, |x|, T)`. -/
  chalLen : ℕ → ℕ → ℕ → ℕ
  /-- The verdict `V(x, PK₀, r, µ, c, z)` (first argument `λ`). -/
  verdict : ℕ → Bits → Bits → Bits → Bits → Bits → Bits → Bool
  /-- The number `N(λ, T)` of witness copies in the honest resource. -/
  copies : ℕ → ℕ → ℕ
  /-- The honest prover's quantum core, generated from `(λ, x)`. -/
  core : ℕ → Bits → Core
  /-- The honest controller writing into the core: `(λ, x, j, view)`. -/
  toCore : ℕ → Bits → ℕ → Bits → Bits
  /-- The honest controller computing `µ` (round 0) and `z` (round 1): `(λ, x, j, view)`. -/
  toVerifier : ℕ → Bits → ℕ → Bits → Bits

/-- The experiment of Definition 3.8 on the instance sequence `x` with resource parameter `T`, as a
published `TightPQRepetition.Main.Verifier` (semantic carrier): the prover receives `PK₀` and
answers `µ`, then receives the uniform `c ∈ {0,1}^m` and answers `z`; the verdict is
`V(x, PK₀, r, µ, c, z)`. -/
def ICBase.verifierSeq (B : ICBase) (x : ℕ → Str) (T : ℕ → ℕ) : Verifier where
  rounds := fun _ => 2
  coins := fun lam => B.genCoins lam (x lam).length (T lam) + B.chalLen lam (x lam).length (T lam)
  qLen := fun _ _ => 0
  query := fun lam r j _ =>
    let g := B.gen lam (x lam) (T lam) (r.take (B.genCoins lam (x lam).length (T lam)))
    if j = 0 then g.1 else r.drop (B.genCoins lam (x lam).length (T lam))
  verdict := fun lam r τ =>
    let g := B.gen lam (x lam) (T lam) (r.take (B.genCoins lam (x lam).length (T lam)))
    B.verdict lam (x lam) g.1 g.2 (τ.getD 0 ([], [])).2 (r.drop (B.genCoins lam (x lam).length (T lam)))
      (τ.getD 1 ([], [])).2

/-- The acceptance probability of the honest execution on `x` with the resource
`ρ^{⊗N(λ, t_L(x))}` on the first wires of the honest core (all other wires `|0⟩`). -/
noncomputable def ICBase.honestAccept (B : ICBase) (F : QMAFamily) (lam : ℕ) (x : Str)
    (ρ : Matrix (Qubits (F.wit x.length)) (Qubits (F.wit x.length)) ℂ) : ℝ :=
  let S := B.core lam x
  S.acceptMixed (B.toCore lam x) (B.toVerifier lam x)
    (B.verifierSeq (fun _ => x) (fun _ => localCost F x)) lam
    (loadedState (fun _ : Unit => F.wit x.length) (fun _ => ρ)
      (List.replicate (B.copies lam (localCost F x)) ()) S.n)

/-- Uniformity (§3.4, p.13, "The remaining syntax is as above"): the coin and challenge lengths,
`Gen`, `V`, the honest core, its controllers and the copy count are polynomial-time computable. -/
def ICBase.IsUniform (B : ICBase) : Prop :=
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam m T,
      g (pack [unary lam, unary m, unary T]) =
        pack [unary (B.genCoins lam m T), unary (B.chalLen lam m T), unary (B.copies lam T)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x T r,
      g (pack [unary lam, x, unary T, r]) = pack [(B.gen lam x T r).1, (B.gen lam x T r).2]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x pk r μ c z,
      g (pack [unary lam, x, pk, r, μ, c, z]) = [B.verdict lam x pk r μ c z]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x, g (pack [unary lam, x]) = (B.core lam x).encode) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x j v,
      g (pack [unary lam, x, unary j, v]) = B.toCore lam x j v) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam x j v,
      g (pack [unary lam, x, unary j, v]) = B.toVerifier lam x j v)

/-- Size bounds (§3.4, p.13, and Definition 3.8): one polynomial `p` bounds, with `T = t_L(x)` and
`P = p(λ, T, 0, 0)`: `PK₀` and `r` for every coin outcome, the accepted responses (`V` rejects longer
`µ`, `z`), the size of circuits computing `V` on the inputs that occur, the size of the honest core,
the copy count and every honest response; and the challenge length is at most
`p(λ, |x|, ⌈log₂(T + 1)⌉, 0)` ("`m = poly(λ, |x|, log T)`"). -/
def ICBase.Bounded (B : ICBase) (F : QMAFamily) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ,
    (∀ lam (x : Str) (r : Bits), r.length = B.genCoins lam x.length (localCost F x) →
      (B.gen lam x (localCost F x) r).1.length ≤ eval4 p lam (localCost F x) 0 0 ∧
      (B.gen lam x (localCost F x) r).2.length ≤ eval4 p lam (localCost F x) 0 0) ∧
    (∀ lam (x : Str), B.chalLen lam x.length (localCost F x) ≤
      eval4 p lam x.length (clog2 (localCost F x + 1)) 0) ∧
    (∀ lam (x : Str) pk r μ c z, B.verdict lam x pk r μ c z = true →
      μ.length ≤ eval4 p lam (localCost F x) 0 0 ∧ z.length ≤ eval4 p lam (localCost F x) 0 0) ∧
    (∀ lam T n, ComputedOn
      (fun w => let l := unpack w
        [B.verdict lam (l.getD 0 []) (l.getD 1 []) (l.getD 2 []) (l.getD 3 []) (l.getD 4 []) (l.getD 5 [])])
      {w | ∃ (x : Str) (r : Bits) (μ c z : Bits), localCost F x ≤ T ∧
        r.length = B.genCoins lam x.length (localCost F x) ∧ μ.length ≤ eval4 p lam T 0 0 ∧
        c.length = B.chalLen lam x.length (localCost F x) ∧ z.length ≤ eval4 p lam T 0 0 ∧
        w = pack [x, (B.gen lam x (localCost F x) r).1, (B.gen lam x (localCost F x) r).2, μ, c, z]}
      n (eval4 p lam T 0 0)) ∧
    (∀ lam (x : Str), (B.core lam x).size ≤ eval4 p lam (localCost F x) 0 0) ∧
    (∀ lam T, B.copies lam T ≤ eval4 p lam T 0 0) ∧
    (∀ lam (x : Str) (j : ℕ) (v : Bits),
      (B.toVerifier lam x j v).length ≤ eval4 p lam (localCost F x) 0 0)

/-- Short public and secret commitment keys (§7.1, pp.49–50: "`(PK_QC, SK_QC) ← QC.Gen(1^λ)` … The
key lengths and generation time are `poly(λ)`, independent of `N`"; "The base first message is
`PK₀ = PK_QC`"): there is a key generator `(PK, SK) ← KGen(1^λ)`, polynomial time in `(1^λ, coins)`,
with coin length and key lengths at most `p(λ)`, such that `Gen(1^λ, x, T)` uses its first coins for
`KGen`, publishes `PK₀ = PK` and keeps `SK` as the first component of its private state
`r = (SK, …)`, whatever `x` and `T`. -/
def ICBase.ShortKeys (B : ICBase) : Prop :=
  ∃ (kc : ℕ → ℕ) (kg : ℕ → Bits → Bits × Bits) (p : Polynomial ℕ),
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam r, g (pack [unary lam, r]) = pack [(kg lam r).1, (kg lam r).2]) ∧
    (∀ lam, kc lam ≤ p.eval lam) ∧
    (∀ lam (r : Bits), r.length = kc lam → (kg lam r).1.length ≤ p.eval lam ∧ (kg lam r).2.length ≤ p.eval lam) ∧
    ∀ lam (x : Str) (T : ℕ) (r : Bits), r.length = B.genCoins lam x.length T →
      kc lam ≤ r.length ∧ (B.gen lam x T r).1 = (kg lam (r.take (kc lam))).1 ∧
        ((unpack (B.gen lam x T r).2).headD []) = (kg lam (r.take (kc lam))).2

/-- Overwhelming acceptance completeness (Definition 3.8): for every polynomial bound `B'` on the
instance length there is a negligible `ν` such that for every `λ`, every `x ∈ L_yes` with
`|x| ≤ B'(λ)` and every `ρ ∈ W_Q(x, 2/3)`, the honest execution with `ρ^{⊗N}` accepts with probability
at least `1 − ν(λ)`. -/
def ICBase.Complete (B : ICBase) (L : PromiseProblem) (F : QMAFamily) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ (lam : ℕ) (x : Str), x ∈ L.yes → x.length ≤ B' lam →
    ∀ ρ ∈ WQ F x (2 / 3), 1 - ν lam ≤ B.honestAccept F lam x ρ

/-- Selective soundness `s(λ)` (Definition 3.8 with Definition 3.7): for every polynomial bound
`B'`, every sequence of fixed no-instances `x_λ ∈ L_no` with `|x_λ| ≤ B'(λ)` and every QPT adversary
`(A₁, A₂)` (one `IsQPT` strategy, with quantum advice), there is a negligible `ν` with acceptance
probability at most `s(λ) + ν(λ)` for every `λ`. -/
def ICBase.Sound (B : ICBase) (L : PromiseProblem) (F : QMAFamily) (s : ℕ → ℝ) : Prop :=
  ∀ B' : ℕ → ℕ, PolyBound B' → ∀ x : ℕ → Str, (∀ lam, x lam ∈ L.no ∧ (x lam).length ≤ B' lam) →
    ∀ Adv : ℕ → Strategy, IsQPT Adv →
      ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
        (Adv lam).acceptProb (B.verifierSeq x fun lam => localCost F (x lam)) lam ≤ s lam + ν lam

end Supplement

end FourMsgQMA


