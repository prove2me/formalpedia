-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
-- name    : ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:17.872662+00:00
-- url     : https://prove2.me/theorems/f25dc929-0d84-404a-9021-9dd4861a7b98
-- title:
--   Taylor Levi St
-- statement:
--   Definitions and structural lemmas for Taylor Levi St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/TaylorLeviSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open Complex
section
variable {D : ℕ}
lemma pgtl_smul_decomp (c : ℂ) (z : Fin D → ℂ) : c • z = c.re • z + c.im • (I • z) := by
  ext j
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring
lemma pgtl_clin {F : Type*} [AddCommGroup F] [Module ℂ F] (f : (Fin D → ℂ) → F)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hr : ∀ (r : ℝ) x, f (r • x) = (r : ℂ) • f x)
    (hI : ∀ x, f (I • x) = I • f x) (c : ℂ) (x : Fin D → ℂ) : f (c • x) = c • f x := by
  rw [pgtl_smul_decomp c x, hadd, hr, hr, hI]
  conv_rhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul]
noncomputable def pgtlCx (d : (Fin D → ℂ) →L[ℝ] ℝ) : (Fin D → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
  { toFun := fun z => (d z : ℂ) - I * (d (I • z) : ℂ)
    map_add' := by intro x y; simp only [smul_add, map_add, ofReal_add]; ring
    map_smul' := by
      intro c z
      simp only [RingHom.id_apply, smul_eq_mul]
      refine pgtl_clin (fun z => (d z : ℂ) - I * (d (I • z) : ℂ)) ?_ ?_ ?_ c z
      · intro x y; simp only [smul_add, map_add, ofReal_add]; ring
      · intro r x
        rw [smul_comm I r x, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        push_cast; ring
      · intro x
        rw [smul_smul, I_mul_I, neg_one_smul, map_neg, smul_eq_mul]
        push_cast
        ring_nf
        rw [I_sq]; ring }
lemma pgtlCx_apply (d : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    pgtlCx d z = (d z : ℂ) - I * (d (I • z) : ℂ) := rfl
noncomputable def pgtlJ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) :=
  (I • ContinuousLinearMap.id ℂ (Fin D → ℂ)).restrictScalars ℝ
lemma pgtlJ_apply (w : Fin D → ℂ) : pgtlJ w = I • w := rfl
noncomputable def pgtlDz (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (Fin D → ℂ) →L[ℝ] ℝ :=
  (1 / 4 : ℝ) • (B z - (B (I • z)).comp pgtlJ)
lemma pgtlDz_apply (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z w : Fin D → ℂ) :
    pgtlDz B z w = (B z w - B (I • z) (I • w)) / 4 := by
  simp only [pgtlDz, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, pgtlJ_apply, smul_eq_mul]
  ring
noncomputable def pgtlBil (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
  { toFun := fun z => pgtlCx (pgtlDz B z)
    map_add' := by
      intro x y
      refine ContinuousLinearMap.ext fun w => ?_
      simp only [ContinuousLinearMap.add_apply, pgtlCx_apply, pgtlDz_apply, smul_add, map_add]
      apply Complex.ext <;> simp <;> ring
    map_smul' := by
      intro c z
      simp only [RingHom.id_apply]
      refine pgtl_clin (fun z => pgtlCx (pgtlDz B z)) ?_ ?_ ?_ c z
      · intro x y
        refine ContinuousLinearMap.ext fun w => ?_
        simp only [ContinuousLinearMap.add_apply, pgtlCx_apply, pgtlDz_apply, smul_add, map_add]
        apply Complex.ext <;> simp <;> ring
      · intro r x
        refine ContinuousLinearMap.ext fun w => ?_
        simp only [ContinuousLinearMap.smul_apply, pgtlCx_apply, pgtlDz_apply, smul_comm I r x,
          map_smul, smul_eq_mul]
        apply Complex.ext <;> simp <;> ring
      · intro x
        refine ContinuousLinearMap.ext fun w => ?_
        simp only [ContinuousLinearMap.smul_apply, pgtlCx_apply, pgtlDz_apply, smul_smul, I_mul_I,
          neg_one_smul, map_neg, ContinuousLinearMap.neg_apply, smul_eq_mul]
        apply Complex.ext <;> simp <;> ring }
end
end ReciprocityTheory.GeometryOfNumbersTheory


