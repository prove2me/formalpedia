-- Prove2me | Definitions.Def_Disjunctive_SimplexTableau_Eval
-- name    : Disjunctive_SimplexTableau_Eval
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:51:23.365611+00:00
-- url     : https://prove2.me/theorems/f3f9dbc8-6a44-4bed-a9a7-7a9dd8e431fb
-- title:
--   γ_l and the evaluation functions f⁺, f⁻
-- statement:
--   This definition fixes `γ_l` and the two evaluation functions `f⁺,f⁻` of Theorem
--   9.3, needed to state the goal theorem's pivot-selection criterion.
--
--   `GammaOf k i l := -ā_kl/ā_il` is the multiplier of row `i` added to row `k` when pivoting on
--   column `l` of row `i`. `FPlus`/`FMinus` are `f⁺(γ),f⁻(γ)` (defined for `γ≥0`/`γ≤0` respectively),
--   the objective value of the simple disjunctive cut obtained from the composite row `xk+γxi+Σ(ākj+
--   γāij)sj = āk0+γāi0`, after eliminating the `γ²` terms and scaling by the sum of multipliers.
--   `FEval` selects `f⁺` or `f⁻` according to the sign of `ā_kl·ā_il`, matching the theorem's own "if
--   `ā_kl ā_il < 0`... or `f⁻(γ_l)` if `ā_kl ā_il > 0`."
--
--   **Formalization Note.** Uses `SurplusM` in place of the book's own "`x̄_j`" for `j∈J`, per this
--   chapter's own identification of nonbasic structural variables with their corresponding surplus
--   (Balas §9, p. 108: "we will identify the nonbasic variables `x_{N∩J}` with the corresponding
--   `s_J`"), the same convention `08-cut-correspondence`'s `Surplus` already used for `s̄_j`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 113-114, Section 9.2

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Tableau

namespace Disjunctive.SimplexTableau

/-- `γ_l := -ā_kl/ā_il`, the multiplier of row `i` added to row `k` when pivoting on column `l`
of row `i` (Balas §9.2, p. 113). -/
noncomputable def GammaOf {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) (k i l : Fin n) : ℝ :=
  -(Abar Atil ι k l) / Abar Atil ι i l

/-- `f⁺(γ)`, the evaluation function for `γ ≥ 0` (Balas §9.2, Theorem 9.3, p. 113-114). -/
noncomputable def FPlus {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n)
    (J : Finset (Fin n)) (xbar : Fin n → ℝ) (γ : ℝ) : ℝ :=
  ((∑ j ∈ J, (-(Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i) * Abar Atil ι k j +
        max (Abar Atil ι k j) (-γ * Abar Atil ι i j)) * SurplusM Atil btil (ι j) xbar) -
      (1 - Abar0 Atil btil ι k - γ * Abar0 Atil btil ι i) * Abar0 Atil btil ι k) /
    (1 + |γ| + ∑ j ∈ J, |Abar Atil ι k j + γ * Abar Atil ι i j|)

/-- `f⁻(γ)`, the evaluation function for `γ ≤ 0` (Balas §9.2, Theorem 9.3, p. 113-114). -/
noncomputable def FMinus {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n)
    (J : Finset (Fin n)) (xbar : Fin n → ℝ) (γ : ℝ) : ℝ :=
  ((∑ j ∈ J, (-(Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i) * Abar Atil ι k j +
        max (Abar Atil ι k j + γ * Abar Atil ι i j) 0) * SurplusM Atil btil (ι j) xbar) -
      (1 - Abar0 Atil btil ι k) * (Abar0 Atil btil ι k + γ * Abar0 Atil btil ι i)) /
    (1 + |γ| + ∑ j ∈ J, |Abar Atil ι k j + γ * Abar Atil ι i j|)

/-- The evaluation of pivot column `l` (row `i`): `f⁺(γ_l)` if `ā_kl ā_il < 0`, `f⁻(γ_l)` if
`ā_kl ā_il > 0` (Balas §9.2, Theorem 9.3, p. 113). -/
noncomputable def FEval {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (k i : Fin n)
    (J : Finset (Fin n)) (xbar : Fin n → ℝ) (l : Fin n) : ℝ :=
  if Abar Atil ι k l * Abar Atil ι i l < 0 then
    FPlus Atil btil ι k i J xbar (GammaOf Atil ι k i l)
  else
    FMinus Atil btil ι k i J xbar (GammaOf Atil ι k i l)

end Disjunctive.SimplexTableau


