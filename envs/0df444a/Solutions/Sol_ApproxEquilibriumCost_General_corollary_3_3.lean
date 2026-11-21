-- Prove2me | solution 1 for ApproxEquilibriumCost.General.corollary_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:34.271439+00:00
-- url     : https://prove2.me/submissions/a1f888ef-0afe-4495-91a5-94d54fb59e03

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_PolynomialLatencies
import Definitions.Def_ApproxEquilibriumCost_General_Parameters
import Theorems.Thm_ApproxEquilibriumCost_General_theorem_3_2

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.General

theorem chk_corollary_3_3 {n k : ℕ} (G : Game n k) (d : ℕ) (hd : 1 ≤ d)
    (hpoly : HasPolynomialLatencies G d) (f : Flow G)
    (hf : IsNash G f) (hcost : 0 < cost G f)
    (ε : ℝ) (hε : 0 ≤ ε) (f' : Flow G) (hf' : IsApproxNash G ε f') :
    let θ := min (rho d ε) (criticalPoint d)
    1 - θ + mu d θ ≤ cost G f' / cost G f := by
  intro θ
  have hnn : ∀ (g : Flow G), (∀ r, 0 ≤ g r) → ∀ e, 0 ≤ load G g e := by
    intro g hg e
    unfold load KellyStochasticNetworks.linkFlow
    apply Finset.sum_nonneg
    intro r _
    apply mul_nonneg _ (hg r)
    unfold incidence
    split_ifs <;> norm_num
  have hx : ∀ e, 0 ≤ load G f e := hnn f hf.1.1
  have hy : ∀ e, 0 ≤ load G f' e := hnn f' hf'.1.1
  have hcr : 0 ≤ crossCost G f' f :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hx e) (G.latency_nonnegative e _ (hy e)))
  have hcrit : criticalPoint d < 1 := by
    unfold criticalPoint
    have : (0 : ℝ) < d := by exact_mod_cast hd
    rw [div_lt_one (by linarith)]; linarith
  have hgap : (cost G f - crossCost G f' f) / cost G f ≤ 1 := by
    rw [div_le_one hcost]; linarith
  have := theorem_3_2 G d hd hpoly f f' hf hcost ε hε hf' 1 zero_le_one hgap
  have hm : min (1 : ℝ) (min (rho d ε) (criticalPoint d)) = θ :=
    min_eq_right (le_trans (min_le_right _ _) hcrit.le)
  simpa [hm] using this

end ApproxEquilibriumCost.General
end

theorem solution : type_of% @ApproxEquilibriumCost.General.chk_corollary_3_3 := @ApproxEquilibriumCost.General.chk_corollary_3_3
