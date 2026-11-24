-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:50.659288+00:00
-- url     : https://prove2.me/theorems/9a3ed172-be79-45d6-8a54-77bf0fb0f67e
-- title:
--   Statements Line Degree Dual
-- statement:
--   Definitions and structural lemmas for Statements Line Degree Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsLineDegreeDual.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
open scoped ComplexOrder
noncomputable section
def dualLattice {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    Submodule ℤ (Fin i → K) where
  carrier := {φ | ∀ x ∈ F.lattice, φ ⬝ᵥ x ∈ (algebraMap (𝓞 K) K).range}
  add_mem' {φ ψ} hφ hψ x hx := by
    rw [add_dotProduct]
    exact add_mem (hφ x hx) (hψ x hx)
  zero_mem' x _ := by
    rw [zero_dotProduct]
    exact zero_mem _
  smul_mem' c φ hφ x hx := by
    rw [smul_dotProduct]
    exact zsmul_mem (hφ x hx) c
abbrev dualBlocks (T : Type) : Unit → Type := fun _ => T
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
def dualLatticeCoord (b : Module.Basis T ℤ (dualLattice F)) : (Σ _ : Unit, T) → ProjField K i :=
  fun p => algebraMap (MvPolynomial (Fin i) K) (ProjField K i)
    (∑ j, C ((b p.2 : Fin i → K) j) * X j)
def dualIdeal (b : Module.Basis T ℤ (dualLattice F)) : Ideal (MRing (dualBlocks T)) :=
  mCoordIdeal (dualLatticeCoord b)
def dualEmbMatrix (b : Module.Basis T ℤ (dualLattice F)) : Matrix T ((K →+* ℂ) × Fin i) ℂ :=
  fun t p => p.1 ((b t : Fin i → K) p.2)
def dualRecover (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    (T → ℂ) ≃ₗ[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
  (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).symm
def dualNormSq (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) : ℝ :=
  ∑ σ : K →+* ℂ, (star (fun j => dualRecover b hb z (σ, j)) ⬝ᵥ
    (F.metric σ *ᵥ fun j => dualRecover b hb z (σ, j))).re
theorem dualNormSq_term_nonneg (σ : K →+* ℂ) (w : Fin i → ℂ) :
    0 ≤ (star w ⬝ᵥ (F.metric σ *ᵥ w)).re := by
  by_cases hw : w = 0
  · simp [hw]
  · exact ((Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hw)).1).le
def dualLine (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : HermLine (dualBlocks T) where
  a := fun _ => 1
  h z := Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  pos z hz := by
    apply Real.sqrt_pos.mpr
    obtain ⟨t, ht⟩ := hz ()
    have hne : dualRecover b hb (fun t => z ⟨(), t⟩) ≠ 0 := by
      intro h0
      apply ht
      have := congrArg (fun v => v t) ((dualRecover b hb).map_eq_zero_iff.mp h0)
      simpa using this
    obtain ⟨⟨σ, j⟩, hσj⟩ := Function.ne_iff.mp hne
    have hσ : (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j)) ≠ 0 := by
      intro h0
      exact hσj (congrFun h0 j)
    have hpos := (Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hσ)).1
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun σ =>
      (star (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j)) ⬝ᵥ
        (F.metric σ *ᵥ fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j))).re)
      (fun σ _ => dualNormSq_term_nonneg σ _) (Finset.mem_univ σ))
  smul c z hc := by
    have hz : (fun t => (fun p : Σ _ : Unit, T => c p.1 * z p) ⟨(), t⟩) =
        c () • fun t => z ⟨(), t⟩ := by
      funext t; rfl
    simp only [hz, dualNormSq, map_smul, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    have : ∀ σ : K →+* ℂ,
        (star (fun j => (c () • dualRecover b hb fun t => z ⟨(), t⟩) (σ, j)) ⬝ᵥ
          (F.metric σ *ᵥ fun j => (c () • dualRecover b hb fun t => z ⟨(), t⟩) (σ, j))).re =
        ‖c ()‖ ^ 2 * (star (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j)) ⬝ᵥ
          (F.metric σ *ᵥ fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j))).re := by
      intro σ
      have hs : (fun j => (c () • dualRecover b hb fun t => z ⟨(), t⟩) (σ, j)) =
          c () • fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := by
        funext j; rfl
      rw [hs, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
    simp only [this, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
def DualLatticeBasisExists.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i),
    ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T), Nonempty (Module.Basis T ℤ (dualLattice F))
def DualEmbBijective.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))
def DualArithVar.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)), 1 ≤ i → IsArithVar (dualIdeal b) i
def DualLineSemipositive.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    IsSemipositiveRel ⊥ (dualIdeal b) (dualLine F b hb)
def DualLineConj.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    IsConjInvariantH (dualLine F b hb)
def DualPointLineDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    IsIntersectionSystem II → ∀ W : Ideal (MRing (dualBlocks T)), IsArithVar W 1 →
      dualIdeal b ≤ W → 0 < degC W ∧
        ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
          v ≠ 0 ∧ F.lineDegree K' v = -II Unit (dualBlocks T) W 1 ![dualLine F b hb] / degC W
def DualTopBound.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type)
    [Fintype T] [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) * geomDeg (dualIdeal b) (dualLine F b hb) (i - 1)
def DualGeomDegPos.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    0 < geomDeg (dualIdeal b) (dualLine F b hb) (i - 1)
theorem one_mem_dualLattice_standard :
    (fun _ : Fin 1 => (1 : ℚ)) ∈ dualLattice (HermLattice.standard ℚ 1) := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => (fun _ : Fin 1 => (1 : ℚ)) ⬝ᵥ x ∈
    (algebraMap (𝓞 ℚ) ℚ).range) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    exact ⟨1, by fin_cases j; simp [dotProduct]⟩
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨a, ha⟩ ⟨c, hc⟩
    exact ⟨a + c, by rw [dotProduct_add, map_add, ha, hc]⟩
  · rintro r x _ ⟨a, ha⟩
    refine ⟨r * a, ?_⟩
    rw [dotProduct_smul, map_mul, ha]
    rfl
def oneDual : dualLattice (HermLattice.standard ℚ 1) := ⟨fun _ => 1, one_mem_dualLattice_standard⟩
theorem oneDual_ne_zero : oneDual ≠ 0 := by
  intro h
  have h1 : ((oneDual : dualLattice (HermLattice.standard ℚ 1)) : Fin 1 → ℚ) 0 = 0 := by
    rw [h]; rfl
  exact one_ne_zero h1
theorem oneDual_linearIndependent : LinearIndependent ℤ (fun _ : Unit => oneDual) :=
  linearIndependent_unique_iff.mpr oneDual_ne_zero
theorem oneDual_span : ⊤ ≤ Submodule.span ℤ (Set.range fun _ : Unit => oneDual) := by
  rintro ⟨φ, hφ⟩ -
  have hx : (fun j : Fin 1 => if j = 0 then (1 : ℚ) else 0) ∈ (HermLattice.standard ℚ 1).lattice := by
    apply Submodule.subset_span
    refine ⟨0, ?_⟩
    funext j
    fin_cases j
    rfl
  obtain ⟨a, ha⟩ := hφ _ hx
  have h0 : φ 0 = algebraMap (𝓞 ℚ) ℚ a := by
    rw [ha]
    simp [dotProduct]
  rw [Set.range_const]
  refine Submodule.mem_span_singleton.mpr ⟨Rat.ringOfIntegersEquiv a, ?_⟩
  apply Subtype.ext
  funext j
  fin_cases j
  show ((Rat.ringOfIntegersEquiv a : ℤ) : ℚ) * 1 = φ 0
  rw [mul_one, Rat.ringOfIntegersEquiv_apply_coe, h0]
def dualBasisStandard : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)) :=
  Module.Basis.mk oneDual_linearIndependent oneDual_span
theorem dualBasisStandard_apply (t : Unit) : dualBasisStandard t = oneDual := by
  simp [dualBasisStandard]
theorem dualEmbMatrix_standard_bijective :
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix dualBasisStandard)) := by
  let hU : Unique ((ℚ →+* ℂ) × Fin 1) :=
    { default := (Rat.castHom ℂ, 0)
      uniq := fun p => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) }
  have hM : ∀ (t : Unit) (p : (ℚ →+* ℂ) × Fin 1), dualEmbMatrix dualBasisStandard t p = 1 := by
    intro t p
    simp [dualEmbMatrix, dualBasisStandard_apply, oneDual]
  have hv : ∀ w : (ℚ →+* ℂ) × Fin 1 → ℂ, Matrix.mulVecLin (dualEmbMatrix dualBasisStandard) w =
      fun _ => w default := by
    intro w
    funext t
    rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_unique, hM, one_mul]
  constructor
  · intro w w' h
    rw [hv, hv] at h
    have h1 := congrFun h ()
    funext p
    rw [Unique.eq_default p]
    exact h1
  · intro z
    refine ⟨fun _ => z (), ?_⟩
    rw [hv]
example : HermLine (dualBlocks Unit) :=
  dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective
end
end GroundTheory.Heights₂.Heights


