-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.continuous_and_hasCompactSupport_and_contDiff_integral_archWord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/94c8df6a-2b61-5aba-bb3e-078fd6dbf38d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_contDiff_top_and_hasCompactSupport_integral_comp_affine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_continuous_and_hasCompactSupport_and_contDiff_integral_archWord

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm

noncomputable section

namespace SlAR

open scoped Classical

section Topology

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_completion (v : InfinitePlace L) : SecondCountableTopology v.Completion :=
  (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing L) := by
  haveI := secondCountableTopology_completion L
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace L) → v.Completion))

theorem secondCountableTopology_units : SecondCountableTopology (InfiniteAdeleRing L)ˣ := by
  haveI := secondCountableTopology_infiniteAdeleRing L
  haveI : SecondCountableTopology (InfiniteAdeleRing L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := InfiniteAdeleRing L)).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem secondCountableTopology_matrix : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) := by
  haveI := secondCountableTopology_infiniteAdeleRing L
  exact inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing L))

theorem secondCountableTopology_gl : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing L)) := by
  haveI := secondCountableTopology_matrix L
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_matrix : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing L))

theorem t2Space_matrix : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing L))

theorem locallyCompactSpace_gl : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing L)) := by
  haveI := locallyCompactSpace_matrix L
  haveI := t2Space_matrix L
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem locallyCompactSpace_units : LocallyCompactSpace (InfiniteAdeleRing L)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem t2Space_gl : T2Space (GL (Fin 2) (InfiniteAdeleRing L)) := by
  haveI := t2Space_matrix L
  exact Units.isEmbedding_embedProduct.t2Space

theorem continuous_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (unipotentGL2 : R → GL (Fin 2) R) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · have : ∀ x : R, ((unipotentGL2 x)⁻¹ : GL (Fin 2) R) = unipotentGL2 (-x) := fun x => by
      apply inv_eq_of_mul_eq_one_right
      rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]
    simp_rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop

theorem continuous_diagOne {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (diagOne : Rˣ → GL (Fin 2) R) := by
  have h1 : Continuous (fun u : Rˣ => ((diagOne u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) := by
    refine continuous_matrix fun i j => ?_
    simp only [diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> first | exact Units.continuous_val | exact continuous_const
  refine Units.continuous_iff.mpr ⟨h1, ?_⟩
  have : (fun u : Rˣ => (((diagOne u)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) =
      fun u => ((diagOne u⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    funext u; rw [map_inv]
  rw [this]
  exact h1.comp continuous_inv

theorem continuous_scalar {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) : Rˣ → GL (Fin 2) R) := by
  refine Continuous.units_map _ ?_
  show Continuous (fun x : R => Matrix.scalar (Fin 2) x)
  have : (fun x : R => Matrix.scalar (Fin 2) x) = fun x => Matrix.diagonal (fun _ : Fin 2 => x) := by
    funext x; exact Matrix.scalar_apply x
  rw [this]
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

theorem continuous_glMap {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (A : R ≃+* R) (hA : Continuous A) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) A.toRingHom) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hA)

open scoped Classical in
theorem continuous_archEntries : Continuous (archEntries L) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace L).comp (Units.continuous_val.matrix_elem i j)

theorem continuous_of_isArchTestFactor {φ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hφ : IsArchTestFactor L φ) :
    Continuous φ := by
  obtain ⟨⟨Φ, hΦ, hφΦ⟩, -⟩ := hφ
  have : φ = Φ ∘ archEntries L := funext hφΦ
  rw [this]
  exact hΦ.continuous.comp (continuous_archEntries L)

noncomputable def word (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (y : InfiniteAdeleRing L)
    (p : (InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ) :
    GL (Fin 2) (InfiniteAdeleRing L) :=
  p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
    diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
    Matrix.GeneralLinearGroup.map A.toRingHom p.2.1

theorem continuous_word (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (hA : Continuous A) :
    Continuous (fun q : InfiniteAdeleRing L × (InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) ×
      (InfiniteAdeleRing L)ˣ => word L A q.1 q.2) := by
  have hAu : Continuous (Units.map A.toRingHom.toMonoidHom : (InfiniteAdeleRing L)ˣ → (InfiniteAdeleRing L)ˣ) :=
    Continuous.units_map _ hA
  unfold word
  refine ((((Continuous.inv ?_).mul ?_).mul ?_).mul ?_).mul ?_
  · exact continuous_fst.comp (continuous_snd.comp continuous_snd)
  · refine continuous_unipotentGL2.comp (continuous_fst.mul ?_)
    exact Units.continuous_coe_inv.comp (continuous_fst.comp continuous_snd)
  · refine continuous_diagOne.comp ?_
    exact (hAu.comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_fst.comp continuous_snd).inv)
  · exact continuous_scalar.comp (hAu.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  · exact (continuous_glMap A hA).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))

end Topology

section Mixed

variable (L : Type) [Field L] [NumberField L]

omit [NumberField L] in
theorem continuous_e : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace L) :=
  NumberField.AdelicBox.continuous_ringEquiv_mixedSpace L

omit [NumberField L] in
theorem continuous_e_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace L).symm := by
  apply continuous_pi
  intro v
  by_cases hv : InfinitePlace.IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace L => (InfiniteAdeleRing.ringEquiv_mixedSpace L).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace L => z.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace L).apply_symm_apply y)
      exact h
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace L => (InfiniteAdeleRing.ringEquiv_mixedSpace L).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace L => z.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace L).apply_symm_apply y)
      exact h
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

omit [NumberField L] in

def mixedHomeo : InfiniteAdeleRing L ≃ₜ mixedEmbedding.mixedSpace L where
  toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace L).toEquiv
  continuous_toFun := continuous_e L
  continuous_invFun := continuous_e_symm L

end Mixed

section Affine

variable (L : Type) [Field L] [NumberField L] (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L)

abbrev Pm : Type := (InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ

abbrev Fm : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L

def Dm (p : Pm L) : GL (Fin 2) (InfiniteAdeleRing L) :=
  diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
    Matrix.GeneralLinearGroup.map A.toRingHom p.2.1

theorem word_eq (y : InfiniteAdeleRing L) (p : Pm L) :
    word L A y p = p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) * Dm L A p := by
  simp only [word, Dm, mul_assoc]

theorem word_apply (y : InfiniteAdeleRing L) (p : Pm L) (i j : Fin 2) :
    ((word L A y p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j =
      ((p.2.1⁻¹ * Dm L A p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j +
        y * (((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) *
          ((p.2.1⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i 0 *
          ((Dm L A p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 j) := by
  rw [word_eq]
  generalize p.2.1⁻¹ = ki
  generalize p.1⁻¹ = ti
  generalize Dm L A p = D
  simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.unipotentGL2_coe]
  ring

def coefA (p : Pm L) (i j : Fin 2) : mixedEmbedding.mixedSpace L :=
  InfiniteAdeleRing.ringEquiv_mixedSpace L
    (((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) *
      ((p.2.1⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i 0 *
      ((Dm L A p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 j)

def bvec (p : Pm L) : Fm L :=
  archEntries L (p.2.1⁻¹ * Dm L A p)

def coefL (p : Pm L) (a b : Fin 2) : mixedEmbedding.mixedSpace L :=
  InfiniteAdeleRing.ringEquiv_mixedSpace L
    (((p.1 : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) *
      ((p.2.1 : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 0 a *
      (((Dm L A p)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) b 1)

def AopL (p : Pm L) : mixedEmbedding.mixedSpace L →ₗ[ℝ] Fm L where
  toFun x := fun i j => x * coefA L A p i j
  map_add' x x' := by
    funext i j
    exact add_mul _ _ _
  map_smul' r x := by
    funext i j
    exact smul_mul_assoc _ _ _

def LopL (p : Pm L) : Fm L →ₗ[ℝ] mixedEmbedding.mixedSpace L where
  toFun W := ∑ a, ∑ b, W a b * coefL L A p a b
  map_add' W W' := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r W := by
    simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, RingHom.id_apply]

def Aop (p : Pm L) : mixedEmbedding.mixedSpace L →L[ℝ] Fm L :=
  LinearMap.toContinuousLinearMap (AopL L A p)

def Lop (p : Pm L) : Fm L →L[ℝ] mixedEmbedding.mixedSpace L :=
  LinearMap.toContinuousLinearMap (LopL L A p)

theorem Aop_apply (p : Pm L) (x : mixedEmbedding.mixedSpace L) :
    Aop L A p x = fun i j => x * coefA L A p i j := rfl

theorem Lop_apply (p : Pm L) (W : Fm L) :
    Lop L A p W = ∑ a, ∑ b, W a b * coefL L A p a b := rfl

theorem key_sum (p : Pm L) :
    ∑ a : Fin 2, ∑ b : Fin 2,
      (((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) *
        ((p.2.1⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) a 0 *
        ((Dm L A p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 b) *
      (((p.1 : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) *
        ((p.2.1 : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 0 a *
        (((Dm L A p)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) b 1) = 1 := by
  have hk : ∑ a : Fin 2, ((p.2.1 : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 0 a *
      ((p.2.1⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) a 0 = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L) => M 0 0) (Units.mul_inv p.2.1)
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq] using this
  have hD : ∑ b : Fin 2, ((Dm L A p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 b *
      (((Dm L A p)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) b 1 = 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L) => M 1 1) (Units.mul_inv (Dm L A p))
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq] using this
  have ht : (((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) * ((p.1 : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) = 1 :=
    Units.inv_mul p.1
  generalize ((p.2.1 : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) = kM at hk
  generalize ((p.2.1⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) = kI at hk
  generalize ((Dm L A p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) = DM at hD
  generalize (((Dm L A p)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) = DI at hD
  generalize (((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) = tI at ht
  generalize ((p.1 : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) = tM at ht
  simp only [Fin.sum_univ_two] at hk hD ⊢
  linear_combination ((kM 0 0 * kI 0 0 + kM 0 1 * kI 1 0) * (DM 1 0 * DI 0 1 + DM 1 1 * DI 1 1)) * ht +
    (DM 1 0 * DI 0 1 + DM 1 1 * DI 1 1) * hk + hD

theorem Lop_Aop (p : Pm L) (x : mixedEmbedding.mixedSpace L) : Lop L A p (Aop L A p x) = x := by
  rw [Lop_apply, Aop_apply]
  have h1 : ∑ a : Fin 2, ∑ b : Fin 2, (x * coefA L A p a b) * coefL L A p a b =
      x * ∑ a : Fin 2, ∑ b : Fin 2, coefA L A p a b * coefL L A p a b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 : ∑ a : Fin 2, ∑ b : Fin 2, coefA L A p a b * coefL L A p a b =
      InfiniteAdeleRing.ringEquiv_mixedSpace L (∑ a : Fin 2, ∑ b : Fin 2,
        (((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) *
          ((p.2.1⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) a 0 *
          ((Dm L A p : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 1 b) *
        (((p.1 : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L) *
          ((p.2.1 : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) 0 a *
          (((Dm L A p)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) b 1)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    rfl
  rw [h1, h2, key_sum, map_one, mul_one]

theorem archEntries_word (y : InfiniteAdeleRing L) (p : Pm L) :
    archEntries L (word L A y p) = Aop L A p (InfiniteAdeleRing.ringEquiv_mixedSpace L y) + bvec L A p := by
  rw [Aop_apply]
  funext i j
  rw [Pi.add_apply, Pi.add_apply, archEntries_apply, word_apply, bvec, archEntries_apply, coefA, map_add, map_mul,
    add_comm]

variable (hA : Continuous A)
include hA

theorem continuous_Dm : Continuous (Dm L A) := by
  have hAu : Continuous (Units.map A.toRingHom.toMonoidHom : (InfiniteAdeleRing L)ˣ → (InfiniteAdeleRing L)ˣ) :=
    Continuous.units_map _ hA
  unfold Dm
  refine ((continuous_diagOne.comp ?_).mul ?_).mul ?_
  · exact (hAu.comp continuous_fst).mul continuous_fst.inv
  · exact continuous_scalar.comp (hAu.comp (continuous_snd.comp continuous_snd))
  · exact (continuous_glMap A hA).comp (continuous_fst.comp continuous_snd)

theorem continuous_kinv_Dm : Continuous fun p : Pm L => p.2.1⁻¹ * Dm L A p :=
  (continuous_fst.comp continuous_snd).inv.mul (continuous_Dm L A hA)

theorem continuous_bvec : Continuous (bvec L A) :=
  (continuous_archEntries L).comp (continuous_kinv_Dm L A hA)

theorem continuous_coefA (i j : Fin 2) : Continuous fun p : Pm L => coefA L A p i j := by
  unfold coefA
  refine (continuous_e L).comp ((?_ : Continuous _).mul ?_)
  · refine (Units.continuous_coe_inv.comp continuous_fst).mul ?_
    exact (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_snd)).matrix_elem i 0
  · exact (Units.continuous_val.comp (continuous_Dm L A hA)).matrix_elem 1 j

theorem continuous_coefL (a b : Fin 2) : Continuous fun p : Pm L => coefL L A p a b := by
  unfold coefL
  refine (continuous_e L).comp ((?_ : Continuous _).mul ?_)
  · refine (Units.continuous_val.comp continuous_fst).mul ?_
    exact (Units.continuous_val.comp (continuous_fst.comp continuous_snd)).matrix_elem 0 a
  · exact (Units.continuous_coe_inv.comp (continuous_Dm L A hA)).matrix_elem b 1

theorem continuous_Aop : Continuous (Aop L A) := by
  refine continuous_clm_apply.2 fun x => ?_
  simp only [Aop_apply]
  exact continuous_pi fun i => continuous_pi fun j => continuous_const.mul (continuous_coefA L A hA i j)

theorem continuous_Lop : Continuous (Lop L A) := by
  refine continuous_clm_apply.2 fun W => ?_
  simp only [Lop_apply]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_const.mul (continuous_coefL L A hA a b)

end Affine

end SlAR

end

open scoped Classical in
theorem solution
    (L : Type) [Field L] [NumberField L]
    (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (hA : Continuous A)
    (φ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφ : IsArchTestFactor L φ)
    (ξ : (InfiniteAdeleRing L)ˣ → ℂ) (hξ : Continuous ξ)
    [MeasurableSpace (InfiniteAdeleRing L)ˣ] [BorelSpace (InfiniteAdeleRing L)ˣ]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing L))]
    (μ : Measure ((InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ))
    [IsFiniteMeasure μ]
    (K : Set ((InfiniteAdeleRing L)ˣ × GL (Fin 2) (InfiniteAdeleRing L) × (InfiniteAdeleRing L)ˣ))
    (hK : IsCompact K) (hμK : μ Kᶜ = 0) :
    Continuous (fun y : InfiniteAdeleRing L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) ∧
    HasCompactSupport (fun y : InfiniteAdeleRing L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x : mixedEmbedding.mixedSpace L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ *
          unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace L).symm x * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) := by
  classical

  haveI := SlAR.secondCountableTopology_units L
  haveI := SlAR.secondCountableTopology_gl L

  set e := InfiniteAdeleRing.ringEquiv_mixedSpace L with he
  obtain ⟨⟨Φ, hΦ, hφΦ⟩, hφc⟩ := hφ

  have hS : IsCompact (archEntries L '' tsupport φ) := hφc.image (SlAR.continuous_archEntries L)
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L)
  let χ : ContDiffBump (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  let Ψ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L) → ℂ := fun w => ContDiffBump.toFun χ w • Φ w
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := χ.contDiff.smul hΦ
  have hΨc : HasCompactSupport Ψ := χ.hasCompactSupport.smul_right
  have hφΨ : ∀ g, φ g = Ψ (archEntries L g) := by
    intro g
    by_cases hg : g ∈ tsupport φ
    · have h1 : ContDiffBump.toFun χ (archEntries L g) = 1 := by
        apply χ.one_of_mem_closedBall
        have := hR ⟨g, hg, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
        show ‖archEntries L g‖ ≤ |R| + 1
        linarith [le_abs_self R]
      show φ g = ContDiffBump.toFun χ (archEntries L g) • Φ (archEntries L g)
      rw [h1, one_smul]
      exact hφΦ g
    · have h0 : φ g = 0 := image_eq_zero_of_notMem_tsupport hg
      show φ g = ContDiffBump.toFun χ (archEntries L g) • Φ (archEntries L g)
      rw [← hφΦ g, h0, smul_zero]

  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (SlAR.continuous_Lop L A hA).continuousOn
  have hproper : ∀ p ∈ K, ∀ x : mixedEmbedding.mixedSpace L, ‖x‖ ≤ max C 0 * (‖SlAR.Aop L A p x‖ + 1) := by
    intro p hp x
    have h1 : ‖x‖ ≤ ‖SlAR.Lop L A p‖ * ‖SlAR.Aop L A p x‖ := by
      conv_lhs => rw [← SlAR.Lop_Aop L A p x]
      exact (SlAR.Lop L A p).le_opNorm _
    have h2 : ‖SlAR.Lop L A p‖ ≤ max C 0 := (hC p hp).trans (le_max_left _ _)
    have h3 : 0 ≤ ‖SlAR.Aop L A p x‖ := norm_nonneg _
    have h4 : 0 ≤ max C 0 := le_max_right _ _
    nlinarith

  obtain ⟨hG, hGc⟩ := contDiff_top_and_hasCompactSupport_integral_comp_affine Ψ hΨ hΨc μ K hK hμK
    (fun p => ξ p.2.2) (hξ.comp (continuous_snd.comp continuous_snd))
    (SlAR.Aop L A) (SlAR.continuous_Aop L A hA) (SlAR.bvec L A) (SlAR.continuous_bvec L A hA) (max C 0) hproper
  have hint : ∀ (y : InfiniteAdeleRing L) (p : SlAR.Pm L),
      φ (SlAR.word L A y p) = Ψ (SlAR.Aop L A p (e y) + SlAR.bvec L A p) := fun y p => by
    rw [hφΨ, SlAR.archEntries_word]
  have hfun1 : (fun y : InfiniteAdeleRing L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ * unipotentGL2 (y * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) =
      (fun x : mixedEmbedding.mixedSpace L => ∫ p, (fun p : SlAR.Pm L => ξ p.2.2) p *
        Ψ (SlAR.Aop L A p x + SlAR.bvec L A p) ∂μ) ∘ e := by
    funext y
    show _ = ∫ p, (fun p : SlAR.Pm L => ξ p.2.2) p * Ψ (SlAR.Aop L A p (e y) + SlAR.bvec L A p) ∂μ
    congr 1
    funext p
    rw [← hint y p]
    rfl
  have hfun3 : (fun x : mixedEmbedding.mixedSpace L =>
        ∫ p, ξ p.2.2 * φ (p.2.1⁻¹ *
          unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace L).symm x * ((p.1⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L)) *
          diagOne (Units.map A.toRingHom.toMonoidHom p.1 * p.1⁻¹) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map A.toRingHom.toMonoidHom p.2.2) *
          Matrix.GeneralLinearGroup.map A.toRingHom p.2.1) ∂μ) =
      fun x : mixedEmbedding.mixedSpace L => ∫ p, (fun p : SlAR.Pm L => ξ p.2.2) p *
        Ψ (SlAR.Aop L A p x + SlAR.bvec L A p) ∂μ := by
    funext x
    congr 1
    funext p
    have := hint (e.symm x) p
    rw [RingEquiv.apply_symm_apply] at this
    rw [← this]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun1]
    exact hG.continuous.comp (SlAR.continuous_e L)
  · rw [hfun1]
    exact hGc.comp_homeomorph (SlAR.mixedHomeo L)
  · rw [hfun3]
    exact hG

end S_AutomorphicForm_TwistedBruhat_continuous_and_hasCompactSupport_and_contDiff_integral_archWord
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_continuous_and_hasCompactSupport_and_contDiff_integral_archWord (solution)
