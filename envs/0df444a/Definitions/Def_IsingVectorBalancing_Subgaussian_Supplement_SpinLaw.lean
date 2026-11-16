-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_SpinLaw
-- name    : IsingVectorBalancing_Subgaussian_Supplement_SpinLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:16:58.094209+00:00
-- url     : https://prove2.me/theorems/86a865c0-fcf3-4c8d-ba57-2cfbca3142e5
-- title:
--   Complete-graph color Gibbs law and standing matrix conditions
-- statement:
--   Configurations are maps $\sigma:[n]\to[q]$. For an interaction matrix $A$ and site activities $\lambda_i(a)$, define
--
--   $$w_{A,\lambda}(\sigma)=\prod_i\lambda_i(\sigma_i)\prod_{i<j}A_{\sigma_i\sigma_j},\qquad Z_A(\lambda)=\sum_\sigma w_{A,\lambda}(\sigma),\qquad\mu_{A,\lambda}=w_{A,\lambda}/Z_A(\lambda).$$
--
--   The interaction predicate means symmetric, entrywise nonnegative, at most one positive eigenvalue, and no all-zero row. The first three conditions reuse the published Lorentzian predicate exactly. The theorem hypotheses separately impose nonnegative activities and positive partition function. No assumption of positive activities, irreducibility or a spectral gap is built into the law. Expectations, variance, Poincaré inequalities, single-site conditional averages and the random-scan kernel reuse published finite interfaces.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 17 (PDF 18), Section 8, (21)–(22)

import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz
import Definitions.Def_mm_mcmc
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_SubsetConvFPRAS_ReversibleChain

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

abbrev ColorConfiguration (n q : ℕ) := Fin n → Fin q

/-- Equation (21): each unordered pair occurs once. -/
noncomputable def colorWeight {n q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (activity : Fin n → Fin q → ℝ) (σ : ColorConfiguration n q) : ℝ :=
  (∏ i, activity i (σ i)) *
    ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), A (σ i) (σ j)

noncomputable def colorPartition {n q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (activity : Fin n → Fin q → ℝ) : ℝ :=
  ∑ σ : ColorConfiguration n q, colorWeight A activity σ

noncomputable def colorLaw {n q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (activity : Fin n → Fin q → ℝ) (σ : ColorConfiguration n q) : ℝ :=
  colorWeight A activity σ / colorPartition A activity

/-- Only the standing matrix assumptions of Section 8, before (21). -/
noncomputable def ColorInteraction {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  IsLorentzian A ∧ ∀ a, ∃ b, A a b ≠ 0

end IsingVectorBalancing.Subgaussian.Supplement


