-- Prove2me | Definitions.Def_ReplParity_Supplement_PnRateLearners
-- name    : ReplParity_Supplement_PnRateLearners
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:55:47.671738+00:00
-- url     : https://prove2.me/theorems/afb6eee4-b0be-429a-8a61-e503112cbce8
-- title:
--   Statements 1 and 3 of Theorem 5.3 — uniform polynomial-time learners for $P_n$ with $n^2\,\mathrm{polylog}/(\varepsilon\rho^2)+O(\log(1/\delta)/\varepsilon)$ samples
-- statement:
--   For a flag $\mathrm{every}\in\{\mathrm{false},\mathrm{true}\}$, $\mathrm{PnRateLearners}(\mathrm{every})$ is the proposition that there are a constant $C$, an exponent $k$, a sample size $m(n,\varepsilon,\delta,\rho)$, a seed length $R(n,\varepsilon,\delta,\rho)$ and one algorithm $A$ such that:
--
--   1. $A$ runs in polynomial time in the finite-bit model (a Turing machine on the base mission's fixed binary encoding);
--   2. $R$ is bounded by a polynomial in $n+m$ and the encoding lengths of $\varepsilon,\delta,\rho$;
--   3. for every $n\ge1$ and all rationals $0<\varepsilon,\delta,\rho<1/2$, the learner $A$ for $P_n$ with $m$ samples and a uniform $R$-bit seed outputs $\bot$ or an $n$-bit truth table, uses
--   $$m\le \frac{Cn^2}{\varepsilon\rho^2}\big(1+\log n+\log(1/\varepsilon)+\log(1/\rho)\big)^k+\frac{C\log(1/\delta)}{\varepsilon}$$
--   samples, is realizably $(\varepsilon,\delta)$-PAC for $P_n$, and is $\rho$-replicable on realizable distributions (if $\mathrm{every}=\mathrm{false}$: statement 1) or on every labeled distribution on $[n]\times\{0,1\}$ (if $\mathrm{every}=\mathrm{true}$: statement 3).
--
--   These are the two learning sides of the characterization in Theorem 5.3.
--
--   **Formalization Note** One machine serves all $n,\varepsilon,\delta,\rho$, and $C,k,m,R,A$ are chosen before them, as in the base goal. A factor $\mathrm{polylog}(n,1/\varepsilon,1/\rho)$ bounded by a fixed polynomial in the logarithms is written $(1+\log n+\log(1/\varepsilon)+\log(1/\rho))^k$; these logarithms are nonnegative here, so every such polynomial is at most a constant times this power.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Theorem 5.3 statements 1 and 3, p.26 (PDF p.28); finite-bit model §2.2, p.11 (PDF p.13); polylog convention §2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ReplParity_IsReplicable
import Definitions.Def_ReplParity_IsRealizablyPAC
import Definitions.Def_ReplParity_runLearner
import Definitions.Def_ReplParity_Supplement_IsReplicableOnRealizable
import Definitions.Def_ReplParity_Supplement_pnLearner

set_option autoImplicit false

namespace ReplParity

namespace Supplement

/-- **Statements 1 and 3 of Theorem 5.3: uniform polynomial-time learners for `P_n` at the rate
`n² polylog/(ερ²) + O(log(1/δ)/ε)`.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample
Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…),
Theorem 5.3, p.26 (PDF p.28):
"1. For every n ≥ 1 and all rational 0 < ε, δ, ρ < 1/2, there is a uniform polynomial-time
finite-bit learner for P_n with m ≤ Cn²/(ερ²) polylog(n, 1/ε, 1/ρ) + C log(1/δ)/ε samples, which is
realizably (ε, δ)-PAC and ρ-replicable on realizable distributions. …
3. The learners of statement 1 exist with ρ-replicability on every labeled distribution."

`PnRateLearners every` asserts: there are a constant `C`, an exponent `k`, a sample size
`m(n, ε, δ, ρ)`, a seed length `R(n, ε, δ, ρ)` and one total function `A` such that
1. `A` is computed in polynomial time by a Mathlib `TM2` machine on the base mission's fixed binary
   encodings `encIn`, `encOut`;
2. `R ≤ c (n + m + |ε| + |δ| + |ρ|)^{k′} + c` (encoding lengths `|·| = ratSize`);
3. for every `n ≥ 1` and rationals `0 < ε, δ, ρ < 1/2`:
   * `m ≤ C n²/(ερ²) · (1 + log n + log(1/ε) + log(1/ρ))^k + C log(1/δ)/ε`;
   * every output is `⊥` or an `n`-bit truth table;
   * the learner `pnLearner A n ε δ ρ` is realizably `(ε, δ)`-PAC for `P_n` (all functions
     `Fin n → ZMod 2`);
   * if `every = false` it is ρ-replicable on the distributions realizable by `P_n`
     (statement 1); if `every = true` it is ρ-replicable on every labeled distribution on
     `Fin n × ZMod 2` (statement 3).

**Formalization Note.** "Uniform" is one machine for all `n, ε, δ, ρ` (they are part of its
input), and `C, k, m, R, A` are chosen before `n, ε, δ, ρ`, as in the base goal
`ReplParity.theorem_3_6`. A factor `polylog(n, 1/ε, 1/ρ)` bounded by a fixed polynomial in
`log n, log(1/ε), log(1/ρ)` (§2, p.10) is written `(1 + log n + log(1/ε) + log(1/ρ))^k`: these logs
are nonnegative in the parameter range, so every such polynomial is at most a constant times this
power, and the constant goes into `C`. -/
def PnRateLearners (every : Bool) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∃ m R : ℕ → ℚ → ℚ → ℚ → ℕ, ∃ A : LInput → Option (List Bool),
    Nonempty (Turing.TM2ComputableInPolyTime encIn encOut A) ∧
    (∃ k' c : ℕ, ∀ (n : ℕ) (ε δ ρ : ℚ),
      R n ε δ ρ ≤ c * (n + m n ε δ ρ + ratSize ε + ratSize δ + ratSize ρ) ^ k' + c) ∧
    ∀ n : ℕ, 1 ≤ n → ∀ ε δ ρ : ℚ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 → 0 < ρ → ρ < 1 / 2 →
      ((m n ε δ ρ : ℝ) ≤
          C * (n : ℝ) ^ 2 / ((ε : ℝ) * (ρ : ℝ) ^ 2) *
              (1 + Real.log n + Real.log (1 / (ε : ℝ)) + Real.log (1 / (ρ : ℝ))) ^ k +
            C * Real.log (1 / (δ : ℝ)) / ε) ∧
      (∀ (S : Fin (m n ε δ ρ) → Fin n × ZMod 2) (r : Fin (R n ε δ ρ) → Bool),
        runLearner A n ε δ ρ (fun i => toExample (S i)) r = none ∨
          ∃ l : List Bool, runLearner A n ε δ ρ (fun i => toExample (S i)) r = some l ∧
            l.length = n) ∧
      IsRealizablyPAC (Set.univ : Set (Fin n → ZMod 2))
        (fun (S : Fin (m n ε δ ρ) → Fin n × ZMod 2) (r : Fin (R n ε δ ρ) → Bool) =>
          pnLearner A n ε δ ρ S r) (ε : ℝ) (δ : ℝ) ∧
      (if every then
        IsReplicable
          (fun (S : Fin (m n ε δ ρ) → Fin n × ZMod 2) (r : Fin (R n ε δ ρ) → Bool) =>
            pnLearner A n ε δ ρ S r) (ρ : ℝ)
      else
        IsReplicableOnRealizable (Set.univ : Set (Fin n → ZMod 2))
          (fun (S : Fin (m n ε δ ρ) → Fin n × ZMod 2) (r : Fin (R n ε δ ρ) → Bool) =>
            pnLearner A n ε δ ρ S r) (ρ : ℝ))

end Supplement

end ReplParity


