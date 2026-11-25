-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:00.954242+00:00
-- url     : https://prove2.me/theorems/38c43234-c458-46f8-a194-5d49623e0cc3
-- title:
--   Assembly TB
-- statement:
--   Definitions and structural lemmas for Assembly TB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTB.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_sub_one_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
theorem gip_integrable (hP : Pos) [Fintype A] [Fintype B] (f g : PV ι A B) :
    Integrable (fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  have hG : Continuous fun z : (ι × A) ⊕ (ι × B) → ℂ => Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) := by fun_prop
  have hc : ∀ f g : PV ι A B, Continuous fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) := fun f g =>
    ((MvPolynomial.continuous_eval f).mul ((MvPolynomial.continuous_eval g).star)).mul hG
  have h1 : ∀ f : PV ι A B, Integrable (fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z f) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro f
    by_cases hf : f = 0
    · subst hf; simp
    · by_contra hn
      have h := (hP ι A B 1 Matrix.PosSemidef.one f).2.2 Matrix.PosDef.one hf
      rw [sub_one_one, gip, integral_undef hn] at h
      simp at h
  refine Integrable.mono' ((h1 f).norm.add (h1 g).norm) (hc f g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [norm_mul, norm_star, Pi.add_apply]
  have ha := norm_nonneg (eval z f)
  have hb := norm_nonneg (eval z g)
  have hcn := norm_nonneg (Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)))
  nlinarith [mul_nonneg hcn (sq_nonneg (‖eval z f‖ - ‖eval z g‖)), mul_nonneg (mul_nonneg ha hb) hcn]
def gipL (hP : Pos) [Fintype A] [Fintype B] (p : PV ι A B) : PV ι A B →ₗ[ℂ] ℂ where
  toFun q := gip q p
  map_add' q1 q2 := by
    simp only [gip, map_add, add_mul]
    exact integral_add (gip_integrable hP q1 p) (gip_integrable hP q2 p)
  map_smul' c q := by
    simp only [gip, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring
end PositivityTheory.Rg.Sw.FFTSteps.AsmA


