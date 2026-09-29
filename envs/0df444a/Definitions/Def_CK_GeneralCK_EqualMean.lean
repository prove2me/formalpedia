-- Prove2me | Definitions.Def_CK_GeneralCK_EqualMean
-- name    : CK_GeneralCK_EqualMean
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:17:08.371405+00:00
-- url     : https://prove2.me/theorems/1e3090e7-2293-464c-94b3-8a5519574aea
-- title:
--   Courtade–Kumar proof module `GeneralCK.EqualMean` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EqualMean` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EqualMean` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EqualMean (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EqualMean.lean)

import Definitions.Def_CK_GeneralCK_PhiEntropyConvexity
import Definitions.Def_CK_GeneralCK_BellmanAssembly
import Definitions.Def_CK_GeneralCK_LogSum

namespace GeneralCK
open Set

theorem psi_entropy_convexOn {m : ℝ} : ConvexOn ℝ (Ioc 0 (H m)) (psi m) := by
  refine ⟨convex_Ioc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcap := H_le_one m
  have h := Scalar.eta_convexOn_Ioc.2
    (show x+1-H m ∈ Ioc 0 1 by constructor <;> linarith [hx.1,hx.2])
    (show y+1-H m ∈ Ioc 0 1 by constructor <;> linarith [hy.1,hy.2]) ha hb hab
  simp only [smul_eq_mul,psi] at h ⊢
  convert! h using 1
  congr 1
  nlinarith

/-- Taking the maximum preserves entropy convexity of both candidates. -/
theorem B_entropy_convexOn {m : ℝ} (hm : 0 < m) (hm' : m < 1) :
    ConvexOn ℝ (Ioc 0 (H m)) (B m) :=
  (phi_entropy_convexOn hm hm').sup psi_entropy_convexOn

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

/-- At equal means the complete hybrid gap is nonpositive, for arbitrary entropy splits. -/
theorem equal_mean_gap_nonpos (μ : InteriorLaw ι) (heq : μ.a = μ.b) : μ.gap ≤ 0 := by
  have hj := (B_entropy_convexOn μ.a_interior.1 μ.a_interior.2).2
    (show μ.e ∈ Ioc 0 (H μ.a) from ⟨μ.e_pos,μ.e_le_cap⟩)
    (show μ.f ∈ Ioc 0 (H μ.a) from ⟨μ.f_pos,by rw [heq]; exact μ.f_le_cap⟩)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hj
  unfold gap
  rw [← heq,show (μ.a+μ.a)/2=μ.a by ring]
  have hmid : (1/2:ℝ)*μ.e+(1/2)*μ.f=(μ.e+μ.f)/2 := by ring
  rw [hmid] at hj
  linarith

theorem equal_mean_phi_gap_nonpos (μ : InteriorLaw ι) (heq : μ.a = μ.b) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ 0 := by
  have hj := (phi_entropy_convexOn μ.a_interior.1 μ.a_interior.2).2
    (show μ.e ∈ Ioc 0 (H μ.a) from ⟨μ.e_pos,μ.e_le_cap⟩)
    (show μ.f ∈ Ioc 0 (H μ.a) from ⟨μ.f_pos,by rw [heq]; exact μ.f_le_cap⟩)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hj
  unfold candidateGap
  rw [← heq,show (μ.a+μ.a)/2=μ.a by ring]
  have hmid : (1/2:ℝ)*μ.e+(1/2)*μ.f=(μ.e+μ.f)/2 := by ring
  rw [hmid] at hj
  linarith

/-- The equal-mean case of the full hybrid Bellman inequality has no active-branch premise. -/
theorem equal_mean_hybrid (μ : InteriorLaw ι) (heq : μ.a = μ.b) : μ.gap ≤ μ.cost := by
  have hc : 0 ≤ μ.cost := by simpa [← heq,interiorCost] using LogSum.cost_lower_bound μ
  exact (μ.equal_mean_gap_nonpos heq).trans hc

end InteriorLaw
end GeneralCK


