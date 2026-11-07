-- Prove2me | Definitions.Def_MixScale_Laws
-- name    : MixScale_Laws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:11:38.268607+00:00
-- url     : https://prove2.me/theorems/aecc83ed-3dc8-4607-9f26-f32a7387354e
-- title:
--   The learning guarantee and the upper and lower sample-complexity laws
-- statement:
--   `LearnsOn` says that one program, fixed in advance, satisfies `RunGuarantee` for all $d,k\ge1$ in which $\chi$ is a radial characteristic function, all $B,\kappa\ge1$, $0<w_\star\le1/k$, $0<\gamma\le1$, $0<\varepsilon\le\varepsilon_{\max}(\gamma)$, $0<\delta<1/2$, every $\Theta$ satisfying (2) (and $w_j=1/k$ for equal weights), every family of component laws and every admissible oracle.
--
--   The **upper law** for weight class $W$ says that there are such a program and constants with budgets, with $\mathcal C=dkB\kappa/w_\star$,
--
--   $$N\le C_0\mathcal C^{D}\,\ell_q(\gamma)\gamma^{-E_W}\varepsilon^{-2}\log\big(C_0'\mathcal C^{D'}/\delta\big),\qquad\text{work}\le C_T\big(\mathcal C\gamma^{-1}\varepsilon^{-1}\log(2/\delta)\big)^{D_T}.$$
--
--   The **lower law** with $k_0$ components says that there are fixed $B,\kappa,w_\star$ and $c,c^*>0$ such that for all $0<\gamma\le c^*$, $0<\varepsilon\le\gamma/8$ there is a hard pair forcing
--
--   $$N\ge c\,\ell_q(\gamma)\gamma^{-E_W}\varepsilon^{-2}.$$
--
--   **Formalization Note** Every variable of $\mathcal C$ is at least $1$ on the inputs, so a positive polynomial in $(d,k,B,\kappa,w_\star^{-1})$ is bounded by $C_0\mathcal C^D$, which is itself such a polynomial. The constants are chosen after the profile and the weight class and before every other parameter. Since $\log$ is monotone, $C_0'$ may be taken large, so positivity of the logarithm is no extra condition. "Polynomial time" is read with the confidence variable $\log(2/\delta)$, because the paper's operation count is $O(dNQ)$ with $N,Q\propto\log(1/\delta)$ (p.48).
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Theorem 1.1, p.3 (PDF p.5); p.3 (polynomials); Appendix G, p.48

import Mathlib
import Definitions.Def_MixScale_Machine
import Definitions.Def_MixScale_Estimator

open MeasureTheory

namespace MixScale

/-!
# The learning guarantee and the two sample-complexity laws

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). Theorem 1.1, p.3 (PDF p.5): "there is a
global polynomial-time algorithm under the conditions (2) that uses `N ≤ P ℓ_q(γ)γ^{−E_W}ε^{−2}
log(P′/δ)`, `0 < ε ≤ γ/8`, samples and returns `Θ̂` satisfying `D_par(Θ̂, Θ) ≤ ε` with probability at
least `1 − δ`"; "there exists a fixed-size one-dimensional subclass with fixed valid condition bounds
on which every estimator succeeding with probability at least `2/3` requires `N ≥ c
ℓ_q(γ)γ^{−E_W}ε^{−2}`, `0 < γ ≤ c∗`, `0 < ε ≤ γ/8`". p.3: "`P, P′, P₁, …` denote positive,
constructible fixed-degree polynomials in `C = (d, k, B, κ, w★⁻¹)`, independent of `γ, ε`, and the
failure probability `δ`".

**Formalization Note.**
* Every variable of `C` is at least `1` on the inputs, so a positive polynomial in `C` is bounded by
  `C₀ · (d k B κ / w★)^D`, and this expression is itself such a polynomial. So "`∃ P`" is
  `∃ C₀ > 0, ∃ D : ℕ` with `C₀ · (condC)^D`. The degree `D` and the program are chosen before `d` and
  `k`. `P′` inside the logarithm is the same form; since the logarithm is monotone, the existential
  `C₀′` may be taken as large as needed, so positivity of the logarithm is no extra condition.
* "Polynomial time" (a reading): on every run, work at most `C_T (C γ⁻¹ ε⁻¹ log(2/δ))^{D_T}`, with
  `log(2/δ)` the confidence variable (the paper's count is `O(dNQ)` with `N, Q ∝ log(1/δ)`, p.48).
  Since `δ < 1/2`, `log(2/δ) > 1`.
* `LearnsOn` fixes the program first, then quantifies over `d, k ≥ 1` in which `χ` is a radial
  characteristic function, the bounds, `γ`, `ε ≤ εmax γ`, `δ`, the truth, its component laws and the
  oracle.
* `LowerLaw` fixes `k₀, B, κ, w★, c, c∗` first; `HardPair` supplies the two alternatives for each
  `γ, ε`.
-/

/-- The condition quantity `d k B κ / w★`. -/
noncomputable def condC (d k : ℕ) (B κ wstar : ℝ) : ℝ := (d : ℝ) * k * B * κ / wstar

/-- The program `P` learns weight class `W` over all legitimate inputs with `ε ≤ εmax γ`, within the
work budget `T` and the sample budget `Nmax` (functions of the inputs `d, k, B, κ, w★, γ, ε, δ`), on
every truth `Θ` satisfying (2) (and `w_j = 1/k` if `W = eq`), every family of component laws of `Θ`
and every admissible oracle. -/
def LearnsOn (S : ProfileSpec) (W : WeightClass) (P : Program) (εmax : ℝ → ℝ)
    (T Nmax : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ (d k : ℕ) (B κ wstar γ ε δ : ℝ) (Θ : Params d k) (Pc : Fin k → Measure (Vec d)) (O : Oracle),
    0 < d → 0 < k → IsRadialCF S.χ d → 1 ≤ B → 1 ≤ κ → 0 < wstar → wstar ≤ 1 / (k : ℝ) →
    0 < γ → γ ≤ 1 → 0 < ε → ε ≤ εmax γ → 0 < δ → δ < 1 / 2 →
    Valid B κ wstar γ Θ → (W = .eq → EqualWeights Θ) → IsCompFamily S.χ Θ Pc →
    AdmissibleOracle S O →
    RunGuarantee S P W B κ wstar γ ε δ Θ Pc O
      (T d k B κ wstar γ ε δ) (Nmax d k B κ wstar γ ε δ)

/-- The upper-bound law for weight class `W`, for `ε ≤ εmax γ`: a global polynomial-time program using
`N ≤ P ℓ_q(γ) γ^{−E_W} ε^{−2} log(P′/δ)` samples, with `P = C₀ (condC)^D`, `P′ = C₀′ (condC)^{D′}`. -/
def UpperLaw (S : ProfileSpec) (W : WeightClass) (εmax : ℝ → ℝ) : Prop :=
  ∃ (P : Program) (C₀ C₀' CT : ℝ) (D D' DT : ℕ),
    Admissible P ∧ 0 < C₀ ∧ 0 < C₀' ∧ 0 < CT ∧
    LearnsOn S W P εmax
      (fun d k B κ wstar γ ε δ =>
        CT * (condC d k B κ wstar / γ / ε * Real.log (2 / δ)) ^ DT)
      (fun d k B κ wstar γ ε δ =>
        C₀ * condC d k B κ wstar ^ D * ellq S.q γ * γ ^ (-W.exponent S.q S.α) * ε ^ (-2 : ℝ) *
          Real.log (C₀' * condC d k B κ wstar ^ D' / δ))

/-- The lower-bound law for weight class `W` with `k₀` components: fixed valid condition bounds and
constants `c > 0`, `c∗ ∈ (0, 1]`, such that for all `0 < γ ≤ c∗`, `0 < ε ≤ γ/8` there is a two-point
hard pair forcing `N ≥ c ℓ_q(γ) γ^{−E_W} ε^{−2}`. -/
def LowerLaw (S : ProfileSpec) (W : WeightClass) (k₀ : ℕ) : Prop :=
  ∃ B κ wstar c cstar : ℝ,
    1 ≤ B ∧ 1 ≤ κ ∧ 0 < wstar ∧ wstar ≤ 1 / (k₀ : ℝ) ∧ 0 < c ∧ 0 < cstar ∧ cstar ≤ 1 ∧
    ∀ γ ε : ℝ, 0 < γ → γ ≤ cstar → 0 < ε → ε ≤ γ / 8 →
      HardPair S.χ W k₀ B κ wstar γ ε
        (c * ellq S.q γ * γ ^ (-W.exponent S.q S.α) * ε ^ (-2 : ℝ))

end MixScale


