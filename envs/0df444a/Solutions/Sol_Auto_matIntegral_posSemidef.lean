-- Prove2me | solution 1 for Auto.matIntegral_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:07:47.54507+00:00
-- url     : https://prove2.me/submissions/785acdfb-b0b1-4149-9f53-6f958cd5043c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matIntegral_apply

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
omit [DecidableEq n] [Fintype n]
namespace Auto
theorem _root_.solution [Finite n] {M : Z → Matrix n n ℂ} (hM : ∀ z, (M z).PosSemidef)
    (hMi : ∀ i j, Integrable (fun z => M z i j) ν) :
    (matIntegral ν M).PosSemidef := by
  let := Fintype.ofFinite n
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hint : ∀ x : n → ℂ, Integrable (fun z => star x ⬝ᵥ (M z *ᵥ x)) ν := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((hMi i j).mul_const _).const_mul _
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, matIntegral_apply, RCLike.star_def]
    rw [← integral_conj]
    congr 1; funext z
    rw [← RCLike.star_def, ← Matrix.conjTranspose_apply, (hM z).1.eq]
  · have hq : ∀ z, 0 ≤ star x ⬝ᵥ (M z *ᵥ x) := fun z =>
      (Matrix.posSemidef_iff_dotProduct_mulVec.1 (hM z)).2 x
    have e : star x ⬝ᵥ (matIntegral ν M *ᵥ x) = ∫ z, star x ⬝ᵥ (M z *ᵥ x) ∂ν := by
      simp only [dotProduct, Matrix.mulVec, matIntegral_apply, Finset.mul_sum]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        ((hMi i j).mul_const _).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => ((hMi i j).mul_const _).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_mul_const]
    rw [e, Complex.nonneg_iff]
    have hre := integral_re (hint x)
    have him := integral_im (hint x)
    simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hre him
    constructor
    · rw [← hre]; exact integral_nonneg fun z => (Complex.nonneg_iff.1 (hq z)).1
    · rw [← him]
      rw [show (fun z => (star x ⬝ᵥ (M z *ᵥ x)).im) = fun _ => (0 : ℝ) from
        funext fun z => ((Complex.nonneg_iff.1 (hq z)).2).symm]
      simp
end Auto
