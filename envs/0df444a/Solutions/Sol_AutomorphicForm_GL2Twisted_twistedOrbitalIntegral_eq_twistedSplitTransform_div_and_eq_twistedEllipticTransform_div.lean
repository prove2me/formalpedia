-- Prove2me | solution 1 for AutomorphicForm.GL2Twisted.twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/790849c4-0300-5fe9-8eb6-6c7ada3c047e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_upperTriangular_eq_smul_map_diag
import Theorems.Thm_AutomorphicForm_GL2Real_exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt
import Theorems.Thm_AutomorphicForm_GL2Twisted_exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv
import Theorems.Thm_AutomorphicForm_GL2Twisted_map_splitProductChart
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.Jacobian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedTorus
namespace Rid

private abbrev ridHom : ℂ ⊗[ℝ] ℝ →+* ℂ :=
  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom

private abbrev ridGL : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) →* GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.map ridHom

private theorem ridHom_tmul (z : ℂ) (a : ℝ) : ridHom (z ⊗ₜ[ℝ] a) = a • z := by
  first
    | rfl
    | (simp; done)

private theorem ridHom_injective : Function.Injective ridHom := by
  first
    | exact (Algebra.TensorProduct.rid ℝ ℝ ℂ).injective
    | exact (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)).injective
    | (intro x y hxy; exact (Algebra.TensorProduct.rid ℝ ℝ ℂ).injective (by simpa using hxy))

private theorem ridHom_sigmaTensor (x : ℂ ⊗[ℝ] ℝ) :
    ridHom (sigmaTensor ℝ ℂ ℝ Complex.conjAe x) = (starRingEnd ℂ) (ridHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul z a =>
      have h1 : sigmaTensor ℝ ℂ ℝ Complex.conjAe (z ⊗ₜ[ℝ] a) = ((starRingEnd ℂ) z) ⊗ₜ[ℝ] a := by
        first
          | rfl
          | (simp [sigmaTensor]; done)
      rw [h1, ridHom_tmul, ridHom_tmul, Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

private theorem ridHom_includeRight (a : ℝ) : ridHom ((1 : ℂ) ⊗ₜ[ℝ] a) = (a : ℂ) := by
  rw [ridHom_tmul, Complex.real_smul, mul_one]

private theorem coe_ridGL (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    ((ridGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).map ridHom := by
  rfl

private theorem coe_sigmaGL (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    ((sigmaGL ℝ ℂ ℝ Complex.conjAe t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
      ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).map (sigmaTensor ℝ ℂ ℝ Complex.conjAe) := by
  rfl

private theorem coe_toTensorGL (g : GL (Fin 2) ℝ) :
    ((toTensorGL ℝ ℂ ℝ g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map (fun a : ℝ => (1 : ℂ) ⊗ₜ[ℝ] a) := by
  first
    | rfl
    | (ext i j
       rfl)

private theorem ridGL_sigmaGL (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    ((ridGL (sigmaGL ℝ ℂ ℝ Complex.conjAe t) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((ridGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := by
  rw [coe_ridGL, coe_sigmaGL, coe_ridGL]
  ext i j
  simp only [Matrix.map_apply]
  exact ridHom_sigmaTensor _

private theorem ridGL_toTensorGL (g : GL (Fin 2) ℝ) :
    ((ridGL (toTensorGL ℝ ℂ ℝ g) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal := by
  rw [coe_ridGL, coe_toTensorGL]
  ext i j
  simp only [Matrix.map_apply]
  exact ridHom_includeRight _

private theorem injective_ridGL : Function.Injective ridGL := by
  intro u v huv
  apply Units.ext
  have h := congrArg (fun w : GL (Fin 2) ℂ => ((w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) huv
  simp only [coe_ridGL] at h
  exact Matrix.map_injective ridHom_injective h

private theorem mem_twistedCentralizer_iff_ridGL (δ t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ↔
      ((ridGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
          ((ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        ((ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
          ((ridGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) := by
  rw [twistedCentralizer, mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, ← injective_ridGL.eq_iff,
    ← Units.val_inj, map_mul, map_mul, Units.val_mul, Units.val_mul, ridGL_sigmaGL]

private theorem injective_toTensorGL : Function.Injective (toTensorGL ℝ ℂ ℝ) := by
  intro g₁ g₂ hg
  have h := congrArg (fun w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => ((ridGL w : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) hg
  simp only [ridGL_toTensorGL] at h
  exact Units.ext (Matrix.map_injective Complex.ofReal_injective h)

private def ridLM : (ℂ ⊗[ℝ] ℝ) →ₗ[ℝ] ℂ where
  toFun := ridHom
  map_add' x y := map_add ridHom x y
  map_smul' r x := by
    show ridHom (r • x) = r • ridHom x
    rw [TensorProduct.RightActions.smul_def]
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul z a =>
        rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul, ridHom_tmul, ridHom_tmul,
          smul_eq_mul, mul_smul]
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]

private theorem continuous_ridHom : Continuous ridHom := by
  have h : Continuous ridLM := IsModuleTopology.continuous_of_linearMap ridLM
  exact h

private def inclLM : ℝ →ₗ[ℝ] (ℂ ⊗[ℝ] ℝ) where
  toFun a := (1 : ℂ) ⊗ₜ[ℝ] a
  map_add' a b := TensorProduct.tmul_add (1 : ℂ) a b
  map_smul' r a := by
    show (1 : ℂ) ⊗ₜ[ℝ] (r • a) = r • ((1 : ℂ) ⊗ₜ[ℝ] a)
    rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
      TensorProduct.comm_symm_tmul]

private theorem continuous_includeRight : Continuous fun a : ℝ => (1 : ℂ) ⊗ₜ[ℝ] a := by
  haveI : IsModuleTopology ℝ ℝ := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd (ℂ ⊗[ℝ] ℝ) := IsModuleTopology.toContinuousAdd ℝ (ℂ ⊗[ℝ] ℝ)
  have h : Continuous inclLM := IsModuleTopology.continuous_of_linearMap inclLM
  first
    | exact h
    | exact h.congr fun a => rfl

private theorem continuous_glMap {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    {f : R →+* S} (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private theorem continuous_toTensorGL : Continuous (toTensorGL ℝ ℂ ℝ) := by
  refine continuous_glMap ?_
  first
    | exact continuous_includeRight
    | exact continuous_includeRight.congr fun a => rfl

private theorem re_entry_ridGL_toTensorGL (g : GL (Fin 2) ℝ) (i : Fin 2) :
    (((ridGL (toTensorGL ℝ ℂ ℝ g) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i i).re =
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i i := by
  rw [ridGL_toTensorGL]
  simp [Matrix.map_apply]

private theorem re_det_ridGL_toTensorGL (g : GL (Fin 2) ℝ) :
    (Matrix.det ((ridGL (toTensorGL ℝ ℂ ℝ g) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re =
      Matrix.det ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [ridGL_toTensorGL, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Matrix.map_apply]

private theorem exists_toTensorGL_eq {t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)} {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ((ridGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A.map Complex.ofReal) :
    ∃ x : GL (Fin 2) ℝ, toTensorGL ℝ ℂ ℝ x = t ∧ ((x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A := by
  have hdet : ((ridGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (ridGL t).isUnit).ne_zero
  have hdetA : A.det ≠ 0 := by
    intro h0
    apply hdet
    rw [hA, Matrix.det_fin_two]
    rw [Matrix.det_fin_two] at h0
    simp only [Matrix.map_apply]
    exact_mod_cast h0
  have hval : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A :=
    rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA, ?_, hval⟩
  apply injective_ridGL
  apply Units.ext
  rw [ridGL_toTensorGL, hval, hA]

private theorem coe_eq_of_toTensorGL_eq {x : GL (Fin 2) ℝ} {t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)} (h : toTensorGL ℝ ℂ ℝ x = t) :
    ((x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.of fun i j => (ridHom (((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j)).re := by
  have h1 : ((ridGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal := by
    rw [← h, ridGL_toTensorGL]
  rw [coe_ridGL] at h1
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at h2
  rw [Matrix.of_apply, h2, Complex.ofReal_re]

end TwistedTorus.Rid

namespace TwistedTorus
namespace Split

open TwistedTorus.Rid

private theorem mem_centralizer_upperTriangular_zero_iff (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (g : GL (Fin 2) ℝ) :
    g ∈ Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)) ↔
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  have hγ : ((upperTriangular a₁ a₂ 0 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, 0; 0, a₂] := rfl
  have hsub : a₁ - a₂ ≠ 0 := sub_ne_zero.2 hne
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Matrix.GeneralLinearGroup.ext_iff]
  constructor
  · intro hg
    have h01 := hg 0 1
    have h10 := hg 1 0
    simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
    constructor
    · have h1 : (a₁ - a₂) * (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by linarith
      exact (mul_eq_zero.1 h1).resolve_left hsub
    · have h2 : (a₁ - a₂) * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left hsub
  · rintro ⟨h01, h10⟩ i j
    fin_cases i <;> fin_cases j <;> simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two, h01, h10] <;> ring

private theorem exists_real_diagonal_of_mul_eq {M : Matrix (Fin 2) (Fin 2) ℂ} {s₁ s₂ : ℝ} (h₁ : 0 < s₁)
    (h₂ : 0 < s₂) (hne : s₁ ≠ s₂)
    (hM : M * !![((s₁ : ℝ) : ℂ), 0; 0, ((s₂ : ℝ) : ℂ)] =
      !![((s₁ : ℝ) : ℂ), 0; 0, ((s₂ : ℝ) : ℂ)] * M.map (starRingEnd ℂ)) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, M = A.map Complex.ofReal ∧ A 0 1 = 0 ∧ A 1 0 = 0 := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have r01 := congrArg Complex.re e01
  have i01 := congrArg Complex.im e01
  have r10 := congrArg Complex.re e10
  have i10 := congrArg Complex.im e10
  have i00 := congrArg Complex.im e00
  have i11 := congrArg Complex.im e11
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im] at r01 i01 r10 i10 i00 i11
  have hsub : s₂ - s₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hsub' : s₁ - s₂ ≠ 0 := sub_ne_zero.2 hne
  have hadd : s₁ + s₂ ≠ 0 := (add_pos h₁ h₂).ne'
  have hx01 : (M 0 1).re = 0 := by
    have h' : (s₂ - s₁) * (M 0 1).re = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_left hsub
  have hy01 : (M 0 1).im = 0 := by
    have h' : (s₁ + s₂) * (M 0 1).im = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_left hadd
  have hx10 : (M 1 0).re = 0 := by
    have h' : (s₁ - s₂) * (M 1 0).re = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_left hsub'
  have hy10 : (M 1 0).im = 0 := by
    have h' : (s₁ + s₂) * (M 1 0).im = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_left hadd
  have hy00 : (M 0 0).im = 0 := by
    have h' : s₁ * (M 0 0).im = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_left h₁.ne'
  have hy11 : (M 1 1).im = 0 := by
    have h' : s₂ * (M 1 1).im = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_left h₂.ne'
  refine ⟨!![(M 0 0).re, 0; 0, (M 1 1).re], ?_, by simp, by simp⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, hx01, hy01, hx10, hy10, hy00, hy11]

private theorem twistedCentralizer_eq_map_centralizer_diagonal (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((Matrix.GeneralLinearGroup.map
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
        δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)]) :
    twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =
      (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ))).map (toTensorGL ℝ ℂ ℝ) := by
  have hD : ((ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] := hδ
  have hs₁ : 0 < Real.sqrt a₁ := Real.sqrt_pos.2 h₁
  have hs₂ : 0 < Real.sqrt a₂ := Real.sqrt_pos.2 h₂
  have hsne : Real.sqrt a₁ ≠ Real.sqrt a₂ := by
    intro hs
    apply hne
    have h' := congrArg (fun x : ℝ => x ^ 2) hs
    simpa [Real.sq_sqrt h₁.le, Real.sq_sqrt h₂.le] using h'
  ext t
  rw [mem_twistedCentralizer_iff_ridGL, hD, Subgroup.mem_map]
  constructor
  · intro hM
    obtain ⟨A, hA, hA01, hA10⟩ := exists_real_diagonal_of_mul_eq hs₁ hs₂ hsne hM
    obtain ⟨x, hxt, hxA⟩ := exists_toTensorGL_eq hA
    refine ⟨x, ?_, hxt⟩
    rw [mem_centralizer_upperTriangular_zero_iff a₁ a₂ h hne, hxA]
    exact ⟨hA01, hA10⟩
  · rintro ⟨x, hx, rfl⟩
    rw [mem_centralizer_upperTriangular_zero_iff a₁ a₂ h hne] at hx
    rw [ridGL_toTensorGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hx.1, hx.2, Complex.conj_ofReal] <;> ring

private theorem toTensorGL_mem_diagonalBox_iff (g : GL (Fin 2) ℝ) :
    ((((ridGL (toTensorGL ℝ ℂ ℝ g) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈
        Set.Icc (1 : ℝ) (Real.exp 1) ∧
      (((ridGL (toTensorGL ℝ ℂ ℝ g) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈
        Set.Icc (1 : ℝ) (Real.exp 1)) ↔
      (((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
        ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)) := by
  rw [re_entry_ridGL_toTensorGL, re_entry_ridGL_toTensorGL]

end TwistedTorus.Split

namespace TwistedTorus
namespace Elliptic

open TwistedTorus.Rid

private theorem mem_centralizer_ellipticElt_iff (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0) (g : GL (Fin 2) ℝ) :
    g ∈ Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)) ↔
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ∧
        (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) := by
  have hγ : ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] := rfl
  have hrs : r * Real.sin θ ≠ 0 := mul_ne_zero hr.ne' hθ
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [Matrix.GeneralLinearGroup.ext_iff]
  constructor
  · intro hg
    have h00 := hg 0 0
    have h01 := hg 0 1
    simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    constructor
    · have h1 : (r * Real.sin θ) *
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = 0 := by linarith
      have h2 := (mul_eq_zero.1 h1).resolve_left hrs
      linarith
    · have h1 : (r * Real.sin θ) *
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 + (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) = 0 := by linarith
      have h2 := (mul_eq_zero.1 h1).resolve_left hrs
      linarith
  · rintro ⟨h11, h10⟩ i j
    fin_cases i <;> fin_cases j <;> simp [Units.val_mul, hγ, Matrix.mul_apply, Fin.sum_univ_two, h11, h10] <;> ring

private theorem exists_real_rotation_of_mul_eq {M : Matrix (Fin 2) (Fin 2) ℂ} {q c s : ℝ} (hq : q ≠ 0)
    (hc : c ≠ 0) (hs : s ≠ 0) (hcs : c ^ 2 + s ^ 2 = 1)
    (hM : M * !![((q * c : ℝ) : ℂ), ((q * s : ℝ) : ℂ); ((-(q * s) : ℝ) : ℂ), ((q * c : ℝ) : ℂ)] =
      !![((q * c : ℝ) : ℂ), ((q * s : ℝ) : ℂ); ((-(q * s) : ℝ) : ℂ), ((q * c : ℝ) : ℂ)] *
        M.map (starRingEnd ℂ)) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, M = A.map Complex.ofReal ∧ A 1 1 = A 0 0 ∧ A 1 0 = -(A 0 1) := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have r00 := congrArg Complex.re e00
  have i00 := congrArg Complex.im e00
  have r01 := congrArg Complex.re e01
  have i01 := congrArg Complex.im e01
  have i10 := congrArg Complex.im e10
  have i11 := congrArg Complex.im e11
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] at r00 i00 r01 i01 i10 i11
  have hqs : q * s ≠ 0 := mul_ne_zero hq hs
  have hqc : q * c ≠ 0 := mul_ne_zero hq hc
  have hx10 : (M 1 0).re = -(M 0 1).re := by
    have h' : (q * s) * ((M 1 0).re + (M 0 1).re) = 0 := by linarith
    have h'' := (mul_eq_zero.1 h').resolve_left hqs
    linarith
  have hx11 : (M 1 1).re = (M 0 0).re := by
    have h' : (q * s) * ((M 1 1).re - (M 0 0).re) = 0 := by linarith
    have h'' := (mul_eq_zero.1 h').resolve_left hqs
    linarith
  have hy11 : (M 1 1).im = (M 0 0).im := by
    have h' : (q * c) * ((M 1 1).im - (M 0 0).im) = 0 := by linarith
    have h'' := (mul_eq_zero.1 h').resolve_left hqc
    linarith
  have hy10 : (M 1 0).im = -(M 0 1).im := by
    have h' : (q * c) * ((M 1 0).im + (M 0 1).im) = 0 := by linarith
    have h'' := (mul_eq_zero.1 h').resolve_left hqc
    linarith
  rw [hy10] at i00
  rw [hy11] at i01
  have f1 : q * (c * (M 0 0).im - s * (M 0 1).im) = 0 := by linarith
  have f2 : q * (s * (M 0 0).im + c * (M 0 1).im) = 0 := by linarith
  have g1 := (mul_eq_zero.1 f1).resolve_left hq
  have g2 := (mul_eq_zero.1 f2).resolve_left hq
  have hy00 : (M 0 0).im = 0 := by linear_combination c * g1 + s * g2 - (M 0 0).im * hcs
  have hy01 : (M 0 1).im = 0 := by linear_combination (-s) * g1 + c * g2 - (M 0 1).im * hcs
  have hy10' : (M 1 0).im = 0 := by rw [hy10, hy01, neg_zero]
  have hy11' : (M 1 1).im = 0 := by rw [hy11, hy00]
  refine ⟨!![(M 0 0).re, (M 0 1).re; -((M 0 1).re), (M 0 0).re], ?_, by simp, by simp⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, hx10, hx11, hy00, hy01, hy10', hy11']

private theorem twistedCentralizer_eq_map_centralizer_rotation (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((Matrix.GeneralLinearGroup.map
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
        δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
          ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)]) :
    twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =
      (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))).map (toTensorGL ℝ ℂ ℝ) := by
  have hD : ((ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
        ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] := hδ
  have hq : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  have h2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h' := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h'
    exact h'
  have hs : Real.sin (θ / 2) ≠ 0 := by
    intro h0
    apply hθ
    rw [h2, h0]
    ring
  have hc : Real.cos (θ / 2) ≠ 0 := by
    intro h0
    apply hθ
    rw [h2, h0]
    ring
  have hcs : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq (θ / 2)
  ext t
  rw [mem_twistedCentralizer_iff_ridGL, hD, Subgroup.mem_map]
  constructor
  · intro hM
    obtain ⟨A, hA, hA11, hA10⟩ := exists_real_rotation_of_mul_eq hq hc hs hcs hM
    obtain ⟨x, hxt, hxA⟩ := exists_toTensorGL_eq hA
    refine ⟨x, ?_, hxt⟩
    rw [mem_centralizer_ellipticElt_iff r θ hr hθ, hxA]
    exact ⟨hA11, hA10⟩
  · rintro ⟨x, hx, rfl⟩
    rw [mem_centralizer_ellipticElt_iff r θ hr hθ] at hx
    rw [ridGL_toTensorGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hx.1, hx.2, Complex.conj_ofReal, Complex.ofReal_mul,
        Complex.ofReal_neg] <;> ring

private theorem toTensorGL_mem_detBox_iff (g : GL (Fin 2) ℝ) :
    (Matrix.det ((ridGL (toTensorGL ℝ ℂ ℝ g) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈
        Set.Icc (1 : ℝ) (Real.exp 2) ↔
      Matrix.det ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
  rw [re_det_ridGL_toTensorGL]

end TwistedTorus.Elliptic

namespace TwistedTorus
namespace Carry

open TwistedTorus.Rid

variable {H : Subgroup (GL (Fin 2) ℝ)} {δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)}

private def torusEquiv (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :
    H ≃* twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ :=
  (H.equivMapOfInjective (toTensorGL ℝ ℂ ℝ) injective_toTensorGL).trans (MulEquiv.subgroupCongr hH)

private theorem torusEquiv_val (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
    (x : H) :
    ((torusEquiv hH x : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
      toTensorGL ℝ ℂ ℝ (x : GL (Fin 2) ℝ) := by
  rfl

private theorem toTensorGL_val_symm (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
    (y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :
    toTensorGL ℝ ℂ ℝ (((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ) = (y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
  have h1 := torusEquiv_val hH ((torusEquiv hH).symm y)
  rw [(torusEquiv hH).apply_symm_apply y] at h1
  exact h1.symm

private theorem toTensorGL_inv_val_symm (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
    (y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :
    toTensorGL ℝ ℂ ℝ ((((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ)⁻¹) = (y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ := by
  rw [map_inv, toTensorGL_val_symm]

private theorem continuous_torusEquiv
    (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :
    Continuous (torusEquiv hH) := by
  have h : Continuous fun x : H => ((torusEquiv hH x : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :
      GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
    simp only [torusEquiv_val]
    exact continuous_toTensorGL.comp continuous_subtype_val
  exact continuous_induced_rng.2 h

private theorem continuous_torusEquiv_symm
    (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :
    Continuous (torusEquiv hH).symm := by
  have hval : Continuous fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
      ((((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hfun : (fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
        ((((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
          Matrix.of fun i j => (ridHom (((y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
          Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j)).re := by
      funext y
      exact coe_eq_of_toTensorGL_eq (toTensorGL_val_symm hH y)
    rw [hfun]
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    exact Complex.continuous_re.comp
      (continuous_ridHom.comp ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j))
  have hinv : Continuous fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
      (((((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hfun : (fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
        (((((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
          Matrix.of fun i j => (ridHom ((((y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
          Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j)).re := by
      funext y
      exact coe_eq_of_toTensorGL_eq (toTensorGL_inv_val_symm hH y)
    rw [hfun]
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    exact Complex.continuous_re.comp
      (continuous_ridHom.comp ((Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem i j))
  have h : Continuous fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
      (((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ) := by
    first
      | exact Units.continuous_iff.2 ⟨hval, hinv⟩
      | exact (Units.continuous_iff (f := fun y : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ =>
          (((torusEquiv hH).symm y : H) : GL (Fin 2) ℝ))).2 ⟨hval, hinv⟩
  exact continuous_induced_rng.2 h

private theorem isHaarMeasure_map_torusEquiv_symm
    (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ) :
    @Measure.IsHaarMeasure H _ _ (borel H)
      (@Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (borel H) (torusEquiv hH).symm τ) := by
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := hτ
  exact MulEquiv.isHaarMeasure_map τ (torusEquiv hH).symm (continuous_torusEquiv_symm hH)
    (continuous_torusEquiv hH)

private theorem map_val_eq_smul_map_comp_of_map_val_eq
    (hH : H.map (toTensorGL ℝ ℂ ℝ) = twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ)
    {ν : Measure (ℝ × ℝ)} {chart : ℝ × ℝ → GL (Fin 2) ℝ}
    (c : NNReal)
    (hc : @Measure.map _ _ (borel H) (glBorelOf ℝ) Subtype.val
        (@Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (borel H) (torusEquiv hH).symm τ) =
      c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf ℝ) chart ν) :
    @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ)) Subtype.val τ =
      c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (toTensorGL ℝ ℂ ℝ ∘ chart) ν := by
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  have hten : Measurable (toTensorGL ℝ ℂ ℝ) := continuous_toTensorGL.measurable
  have hvalH : Measurable (Subtype.val : H → GL (Fin 2) ℝ) := continuous_subtype_val.measurable
  have hsymm : Measurable (torusEquiv hH).symm := (continuous_torusEquiv_symm hH).measurable

  have hne : Measure.map (torusEquiv hH).symm τ ≠ 0 := by
    haveI := isHaarMeasure_map_torusEquiv_symm hH τ hτ
    first
      | exact NeZero.ne _
      | exact Measure.measure_univ_pos.mp (isOpen_univ.measure_pos _ Set.univ_nonempty)

  have hae : AEMeasurable chart ν := by
    by_contra hna
    have h0 : Measure.map chart ν = 0 := Measure.map_of_not_aemeasurable hna
    rw [h0, smul_zero] at hc
    have h1 : Measure.map (torusEquiv hH).symm τ Set.univ = 0 := by
      have h2 := congrArg (fun m : Measure (GL (Fin 2) ℝ) => m Set.univ) hc
      simp only [Measure.map_apply hvalH MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
        Pi.zero_apply] at h2
      exact h2
    exact hne (Measure.measure_univ_eq_zero.1 h1)
  have hid : (toTensorGL ℝ ℂ ℝ ∘ (Subtype.val : H → GL (Fin 2) ℝ)) ∘ (torusEquiv hH).symm =
      (Subtype.val : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
    funext y
    exact toTensorGL_val_symm hH y
  have h1 : Measure.map (Subtype.val : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) τ =
      Measure.map (toTensorGL ℝ ℂ ℝ) (Measure.map Subtype.val (Measure.map (torusEquiv hH).symm τ)) := by
    rw [Measure.map_map hten hvalH, Measure.map_map (hten.comp hvalH) hsymm, hid]
  rw [h1, hc, Measure.map_smul, AEMeasurable.map_map_of_aemeasurable hten.aemeasurable hae]

end TwistedTorus.Carry

namespace TwistedTorus
namespace Split

open TwistedTorus.Rid TwistedTorus.Carry

private theorem exists_map_val_eq_smul_map_diagonal (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂) (h₁ : 0 < a₁)
    (h₂ : 0 < a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((Matrix.GeneralLinearGroup.map
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
        δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ)) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
          (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) := by
  have hH : (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ))).map (toTensorGL ℝ ℂ ℝ) =
      twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ :=
    (twistedCentralizer_eq_map_centralizer_diagonal a₁ a₂ h hne h₁ h₂ δ hδ).symm
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  letI : MeasurableSpace (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ))) :=
    borel (Subgroup.centralizer ({upperTriangular a₁ a₂ 0 h} : Set (GL (Fin 2) ℝ)))
  obtain ⟨c, hc0, hc⟩ :=
    AutomorphicForm.GL2Real.exists_map_val_centralizer_upperTriangular_eq_smul_map_diag a₁ a₂ h hne
      (Measure.map (TwistedTorus.Carry.torusEquiv hH).symm τ)
      (TwistedTorus.Carry.isHaarMeasure_map_torusEquiv_symm hH τ hτ)
  exact ⟨c, hc0, TwistedTorus.Carry.map_val_eq_smul_map_comp_of_map_val_eq hH τ hτ c hc⟩

end TwistedTorus.Split

namespace TwistedTorus
namespace Elliptic

open TwistedTorus.Rid TwistedTorus.Carry

private theorem exists_map_val_eq_smul_map_rotation (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((Matrix.GeneralLinearGroup.map
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
        δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
          ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)])
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ) :
    ∃ c : NNReal, 0 < c ∧
      @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ)) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
          (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹)) := by
  have hH : (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))).map (toTensorGL ℝ ℂ ℝ) =
      twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ :=
    (twistedCentralizer_eq_map_centralizer_rotation r θ hr hθ δ hδ).symm
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  letI : MeasurableSpace (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ))) :=
    borel (Subgroup.centralizer ({ellipticElt r θ hr} : Set (GL (Fin 2) ℝ)))
  obtain ⟨c, hc0, hc⟩ :=
    AutomorphicForm.GL2Real.exists_map_val_centralizer_ellipticElt_eq_smul_map_ellipticElt r θ hr hθ
      (Measure.map (TwistedTorus.Carry.torusEquiv hH).symm τ)
      (TwistedTorus.Carry.isHaarMeasure_map_torusEquiv_symm hH τ hτ)
  exact ⟨c, hc0, TwistedTorus.Carry.map_val_eq_smul_map_comp_of_map_val_eq hH τ hτ c hc⟩

end TwistedTorus.Elliptic

namespace TwistedTorus
namespace Rid

private theorem continuous_ridGL : Continuous ridGL := by
  first
    | exact continuous_glMap continuous_ridHom
    | (unfold ridGL; exact continuous_glMap continuous_ridHom)

end TwistedTorus.Rid

namespace TwistedTorus
namespace Boxes

open TwistedTorus.Rid

private theorem aemeasurable_of_map_eq_smul_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (ρ : Measure γ) (hρ : ρ ≠ 0) {g : γ → β} (hg : Measurable g) (f : α → β) (ν : Measure α)
    (c : NNReal) (h : Measure.map g ρ = c • Measure.map f ν) : AEMeasurable f ν := by
  by_contra hna
  have h0 : Measure.map f ν = 0 := Measure.map_of_not_aemeasurable hna
  rw [h0, smul_zero] at h
  apply hρ
  refine Measure.measure_univ_eq_zero.1 ?_
  have h2 : Measure.map g ρ Set.univ = 0 := by
    rw [h]
    first
      | rfl
      | simp
  rwa [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ] at h2

private theorem exp_two_eq_sq : Real.exp 2 = Real.exp 1 ^ 2 := by
  rw [← Real.exp_nat_mul]
  norm_num

private theorem lintegral_rect (f g : ℝ → ENNReal) (hf : Measurable f) (hg : Measurable g) (s t : Set ℝ) :
    ∫⁻ z in s ×ˢ t, f z.1 * g z.2 = (∫⁻ x in s, f x) * ∫⁻ y in t, g y := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable hg.aemeasurable]

private theorem one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

private theorem lintegral_Icc_one_exp_ofReal_inv :
    ∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal x⁻¹ = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) := by
    refine continuousOn_inv₀.mono ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (lt_of_lt_of_le one_pos hx.1).ne'
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) (Real.exp 1))] fun x : ℝ => x⁻¹ :=
    ae_restrict_of_forall_mem measurableSet_Icc fun x hx => inv_nonneg.2 (zero_le_one.trans hx.1)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le one_le_exp_one, integral_inv_of_pos one_pos (Real.exp_pos 1), div_one,
    Real.log_exp, ENNReal.ofReal_one]

private def splitBox : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
  {x | (((ridGL x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
    (((ridGL x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈ Set.Icc (1 : ℝ) (Real.exp 1)}

private def detBox : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
  {x | (Matrix.det ((ridGL x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈ Set.Icc (1 : ℝ) (Real.exp 2)}

private theorem continuous_re_entry (i j : Fin 2) :
    Continuous fun x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => (((ridGL x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j).re := by
  exact Complex.continuous_re.comp ((Units.continuous_val.comp continuous_ridGL).matrix_elem i j)

private theorem continuous_re_det :
    Continuous fun x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
      (Matrix.det ((ridGL x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  exact Complex.continuous_re.comp (Units.continuous_val.comp continuous_ridGL).matrix_det

private theorem measurableSet_splitBox : @MeasurableSet (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)) splitBox := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  exact ((continuous_re_entry 0 0).measurable measurableSet_Icc).inter
    ((continuous_re_entry 1 1).measurable measurableSet_Icc)

private theorem measurableSet_detBox : @MeasurableSet (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)) detBox := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  exact continuous_re_det.measurable measurableSet_Icc

end TwistedTorus.Boxes

namespace TwistedTorus
namespace Split

open TwistedTorus.Rid TwistedTorus.Boxes

private theorem splitModel_preimage_splitBox :
    ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹))
      ((toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ⁻¹' TwistedTorus.Boxes.splitBox) = 1 := by
  have hpre :
      (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ⁻¹' TwistedTorus.Boxes.splitBox =
      Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1) ∪ {α : ℝ × ℝ | α.1 * α.2 = 0} := by
    ext α
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_union, Set.mem_setOf_eq, Set.mem_prod]
    by_cases hD : α.1 * α.2 ≠ 0
    · rw [dif_pos hD]
      have hiff : toTensorGL ℝ ℂ ℝ (upperTriangular α.1 α.2 0 hD) ∈ TwistedTorus.Boxes.splitBox ↔
          (α.1 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧ α.2 ∈ Set.Icc (1 : ℝ) (Real.exp 1)) :=
        toTensorGL_mem_diagonalBox_iff (upperTriangular α.1 α.2 0 hD)
      constructor
      · intro hx
        exact Or.inl (hiff.1 hx)
      · rintro (hx | hx)
        · exact hiff.2 hx
        · exact absurd hx hD
    · rw [dif_neg hD, map_one]
      have hD' : α.1 * α.2 = 0 := not_not.1 hD
      constructor
      · intro _
        exact Or.inr hD'
      · intro _
        change (((ridGL (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈
            Set.Icc (1 : ℝ) (Real.exp 1) ∧
          (((ridGL (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈
            Set.Icc (1 : ℝ) (Real.exp 1)
        rw [map_one]
        simp only [Units.val_one, Matrix.one_apply_eq, Complex.one_re, Set.mem_Icc, le_refl, true_and]
        exact ⟨TwistedTorus.Boxes.one_le_exp_one, TwistedTorus.Boxes.one_le_exp_one⟩
  have hmeas : MeasurableSet (Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1) ∪
      {α : ℝ × ℝ | α.1 * α.2 = 0}) :=
    (measurableSet_Icc.prod measurableSet_Icc).union ((measurable_fst.mul measurable_snd) (measurableSet_singleton 0))
  rw [hpre, withDensity_apply _ hmeas, Measure.restrict_restrict hmeas]
  have hset : (Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1) ∪ {α : ℝ × ℝ | α.1 * α.2 = 0}) ∩
      {α : ℝ × ℝ | α.1 * α.2 ≠ 0} = Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1) := by
    ext α
    constructor
    · rintro ⟨hα | hα, hD⟩
      · exact hα
      · exact absurd hα hD
    · intro hα
      obtain ⟨h1, h2⟩ := Set.mem_prod.1 hα
      exact ⟨Or.inl hα, (mul_pos (lt_of_lt_of_le one_pos h1.1) (lt_of_lt_of_le one_pos h2.1)).ne'⟩
  rw [hset]
  calc ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal |α.1 * α.2|⁻¹
      = ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1),
          ENNReal.ofReal α.1⁻¹ * ENNReal.ofReal α.2⁻¹ := by
        refine setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) ?_
        intro α hα
        obtain ⟨h1, h2⟩ := Set.mem_prod.1 hα
        have hp1 : 0 < α.1 := lt_of_lt_of_le one_pos h1.1
        have hp2 : 0 < α.2 := lt_of_lt_of_le one_pos h2.1
        show ENNReal.ofReal |α.1 * α.2|⁻¹ = ENNReal.ofReal α.1⁻¹ * ENNReal.ofReal α.2⁻¹
        rw [abs_of_pos (mul_pos hp1 hp2), mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 hp1.le)]
    _ = (∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal x⁻¹) *
          ∫⁻ y in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal y⁻¹ :=
        lintegral_rect (fun x => ENNReal.ofReal x⁻¹) (fun y => ENNReal.ofReal y⁻¹)
          measurable_id.inv.ennreal_ofReal measurable_id.inv.ennreal_ofReal _ _
    _ = 1 := by rw [lintegral_Icc_one_exp_ofReal_inv, one_mul]

private theorem toReal_splitBox_of_map_val_eq (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂) (h₁ : 0 < a₁)
    (h₂ : 0 < a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((Matrix.GeneralLinearGroup.map
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
        δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ)
    (c : NNReal)
    (hc :
      @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ)) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
          (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
          ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
            (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹))) :
    (τ {t |
        (((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈
          Set.Icc (1 : ℝ) (Real.exp 1) ∧
        (((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈
          Set.Icc (1 : ℝ) (Real.exp 1)}).toReal = c := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  have hval : Measurable (Subtype.val : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    continuous_subtype_val.measurable
  have hτne : τ ≠ 0 := by
    haveI := hτ
    first
      | exact NeZero.ne τ
      | exact Measure.measure_univ_pos.mp (isOpen_univ.measure_pos τ Set.univ_nonempty)
  have hae := TwistedTorus.Boxes.aemeasurable_of_map_eq_smul_map τ hτne hval _ _ c hc
  change (τ (Subtype.val ⁻¹' TwistedTorus.Boxes.splitBox)).toReal = c
  rw [← Measure.map_apply hval TwistedTorus.Boxes.measurableSet_splitBox, hc, Measure.smul_apply,
    Measure.map_apply_of_aemeasurable hae TwistedTorus.Boxes.measurableSet_splitBox, splitModel_preimage_splitBox]
  simp [ENNReal.smul_def]

end TwistedTorus.Split

namespace TwistedTorus
namespace Elliptic

open TwistedTorus.Rid TwistedTorus.Boxes

private theorem polarModel_preimage_detBox :
    ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹))
      ((toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ⁻¹' TwistedTorus.Boxes.detBox) = ENNReal.ofReal (2 * Real.pi) := by
  have hdet : ∀ (ρ φ : ℝ) (hρ : 0 < ρ),
      Matrix.det ((ellipticElt ρ φ hρ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ρ ^ 2 := by
    intro ρ φ hρ
    have hγ : ((ellipticElt ρ φ hρ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![ρ * Real.cos φ, ρ * Real.sin φ; -(ρ * Real.sin φ), ρ * Real.cos φ] := rfl
    rw [hγ, Matrix.det_fin_two_of]
    have h := Real.cos_sq_add_sin_sq φ
    linear_combination ρ ^ 2 * h
  have hpre :
      (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ⁻¹' TwistedTorus.Boxes.detBox =
      Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ (Set.univ : Set ℝ) ∪ Set.Iic (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext q
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_union, Set.mem_prod, Set.mem_univ, and_true,
      Set.mem_Iic]
    by_cases hq : 0 < q.1
    · rw [dif_pos hq]
      have hiff : toTensorGL ℝ ℂ ℝ (ellipticElt q.1 q.2 hq) ∈ TwistedTorus.Boxes.detBox ↔
          q.1 ^ 2 ∈ Set.Icc (1 : ℝ) (Real.exp 2) := by
        have h := toTensorGL_mem_detBox_iff (ellipticElt q.1 q.2 hq)
        rw [hdet q.1 q.2 hq] at h
        exact h
      constructor
      · intro hx
        have hx' := hiff.1 hx
        rw [TwistedTorus.Boxes.exp_two_eq_sq] at hx'
        refine Or.inl ⟨?_, ?_⟩
        · nlinarith [hx'.1, hq]
        · nlinarith [hx'.2, hq, Real.exp_pos 1]
      · rintro (hx | hx)
        · refine hiff.2 ?_
          rw [TwistedTorus.Boxes.exp_two_eq_sq]
          refine ⟨?_, ?_⟩
          · nlinarith [hx.1]
          · have hsq : q.1 * q.1 ≤ Real.exp 1 * Real.exp 1 :=
              mul_le_mul hx.2 hx.2 (by linarith [hx.1]) (by linarith [TwistedTorus.Boxes.one_le_exp_one])
            nlinarith [hsq]
        · exact absurd hq (not_lt.2 hx)
    · rw [dif_neg hq, map_one]
      constructor
      · intro _
        exact Or.inr (not_lt.1 hq)
      · intro _
        change (Matrix.det ((ridGL (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈
          Set.Icc (1 : ℝ) (Real.exp 2)
        rw [map_one]
        simp only [Units.val_one, Matrix.det_one, Complex.one_re, Set.mem_Icc, le_refl, true_and]
        have h := Real.add_one_le_exp (2 : ℝ)
        linarith
  have hmeas : MeasurableSet (Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ (Set.univ : Set ℝ) ∪
      Set.Iic (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    (measurableSet_Icc.prod MeasurableSet.univ).union (measurableSet_Iic.prod MeasurableSet.univ)
  rw [hpre, withDensity_apply _ hmeas, Measure.restrict_restrict hmeas]
  have hset : (Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ (Set.univ : Set ℝ) ∪ Set.Iic (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) ∩
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) =
      Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, Set.mem_Iic, Set.mem_Ioi]
    constructor
    · rintro ⟨hq | hq, hpos, hφ⟩
      · exact ⟨hq, hφ⟩
      · exact absurd hpos (not_lt.2 hq)
    · rintro ⟨hq, hφ⟩
      exact ⟨Or.inl hq, lt_of_lt_of_le one_pos hq.1, hφ⟩
  rw [hset]
  calc ∫⁻ q in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ENNReal.ofReal q.1⁻¹
      = ∫⁻ q in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal q.1⁻¹ * (fun _ : ℝ => (1 : ENNReal)) q.2 :=
        lintegral_congr fun q => (mul_one _).symm
    _ = (∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal x⁻¹) *
          ∫⁻ _ in Set.Ioo (0 : ℝ) (2 * Real.pi), (1 : ENNReal) :=
        lintegral_rect (fun x => ENNReal.ofReal x⁻¹) (fun _ => (1 : ENNReal)) measurable_id.inv.ennreal_ofReal
          measurable_const _ _
    _ = ENNReal.ofReal (2 * Real.pi) := by
        rw [lintegral_Icc_one_exp_ofReal_inv, one_mul, setLIntegral_one, Real.volume_Ioo, sub_zero]

private theorem toReal_detBox_of_map_val_eq (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((Matrix.GeneralLinearGroup.map
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
        δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
          ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)])
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ)
    (c : NNReal)
    (hc :
      @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ)) Subtype.val τ =
        c • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
          (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
          ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
            (fun q => ENNReal.ofReal q.1⁻¹))) :
    (τ {t | (Matrix.det
        ((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈
          Set.Icc (1 : ℝ) (Real.exp 2)}).toReal = 2 * Real.pi * c := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  have hval : Measurable (Subtype.val : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    continuous_subtype_val.measurable
  have hτne : τ ≠ 0 := by
    haveI := hτ
    first
      | exact NeZero.ne τ
      | exact Measure.measure_univ_pos.mp (isOpen_univ.measure_pos τ Set.univ_nonempty)
  have hae := TwistedTorus.Boxes.aemeasurable_of_map_eq_smul_map τ hτne hval _ _ c hc
  change (τ (Subtype.val ⁻¹' TwistedTorus.Boxes.detBox)).toReal = 2 * Real.pi * c
  rw [← Measure.map_apply hval TwistedTorus.Boxes.measurableSet_detBox, hc, Measure.smul_apply,
    Measure.map_apply_of_aemeasurable hae TwistedTorus.Boxes.measurableSet_detBox, polarModel_preimage_detBox]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (by positivity)]
  ring

end TwistedTorus.Elliptic

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit
namespace Transfer

private def torusD : Set (ℝ × ℝ) := {α | α.1 * α.2 ≠ 0}

private def diagElt (α : ℝ × ℝ) : GL (Fin 2) ℝ :=
  if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1

private theorem diagElt_apply_of_ne (α : ℝ × ℝ) (hα : α.1 * α.2 ≠ 0) :
    diagElt α = upperTriangular α.1 α.2 0 hα :=
  dif_pos hα

private theorem continuousOn_matrixInv_isUnit' :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_ (Continuous.matrix_adjugate continuous_id).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem isEmbedding_glVal' :
    Topology.IsEmbedding (Units.val : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv_isUnit' fun u => (Matrix.coe_units_inv u).symm

private theorem measurable_of_continuousOn_of_eq_one {P : ℝ × ℝ → GL (Fin 2) ℝ} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hPD : ContinuousOn P D) (hP1 : ∀ α, α ∉ D → P α = 1) :
    @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ) P := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  classical
  have h : P = D.piecewise P (fun _ => 1) := by
    funext α
    by_cases hα : α ∈ D
    · simp [Set.piecewise, hα]
    · simp [Set.piecewise, hα, hP1 α hα]
  rw [h]
  exact hPD.measurable_piecewise continuousOn_const hD.measurableSet

private theorem coe_upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] :=
  rfl

private theorem splitParam_apply_of_ne (α : ℝ × ℝ) (hα : α.1 * α.2 ≠ 0) :
    (if hα' : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα' else 1) = upperTriangular α.1 α.2 0 hα :=
  dif_pos hα

private theorem isOpen_splitDomain : IsOpen {α : ℝ × ℝ | α.1 * α.2 ≠ 0} :=
  isOpen_ne.preimage (continuous_fst.mul continuous_snd)

private theorem continuousOn_splitParam :
    ContinuousOn (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
      {α : ℝ × ℝ | α.1 * α.2 ≠ 0} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn
      (Units.val ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
      (fun α : ℝ × ℝ => !![α.1, 0; 0, α.2]) {α : ℝ × ℝ | α.1 * α.2 ≠ 0} := by
    intro α (hα : α.1 * α.2 ≠ 0)
    show ((if hα' : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα' else 1 : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![α.1, 0; 0, α.2]
    rw [splitParam_apply_of_ne α hα, coe_upperTriangular]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem measurable_splitParam :
    @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ)
      (fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1) := by
  refine measurable_of_continuousOn_of_eq_one isOpen_splitDomain continuousOn_splitParam ?_
  intro α hα
  have hα' : ¬ α.1 * α.2 ≠ 0 := hα
  simp only [dif_neg hα']

private theorem measurableSet_torusD : MeasurableSet torusD := by
  exact isOpen_splitDomain.measurableSet

private theorem measurable_toTensorGL_diagElt :
    @Measurable (ℝ × ℝ) (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (toTensorGL ℝ ℂ ℝ ∘ diagElt) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  exact TwistedTorus.Rid.continuous_toTensorGL.measurable.comp measurable_splitParam

private theorem coset_transfer_split (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
          (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hφ : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ φ)
    (hint : Integrable (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => φ t) τ) :
    Integrable (fun α : ℝ × ℝ => |α.1 * α.2|⁻¹ * φ (toTensorGL ℝ ℂ ℝ (diagElt α))) (volume.restrict torusD) ∧
      ∫ α in torusD, |α.1 * α.2|⁻¹ * φ (toTensorGL ℝ ℂ ℝ (diagElt α)) =
        (cT : ℝ)⁻¹ * ∫ t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, φ t ∂τ := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  have hval : Measurable (Subtype.val : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    continuous_subtype_val.measurable
  have hdm : Measurable fun α : ℝ × ℝ => ENNReal.ofReal |α.1 * α.2|⁻¹ :=
    (by fun_prop : Measurable fun α : ℝ × ℝ => |α.1 * α.2|⁻¹).ennreal_ofReal
  have hdlt : ∀ᵐ α ∂(volume.restrict torusD), ENNReal.ofReal |α.1 * α.2|⁻¹ < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hτ' : Measure.map Subtype.val τ =
      cT • Measure.map (toTensorGL ℝ ℂ ℝ ∘ diagElt)
        ((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) :=
    hτ
  have hν : Measure.map (toTensorGL ℝ ℂ ℝ ∘ diagElt)
        ((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) =
      cT⁻¹ • Measure.map Subtype.val τ := by
    rw [hτ', smul_smul, inv_mul_cancel₀ hcT.ne', one_smul]
  have h1 : Integrable φ (Measure.map Subtype.val τ) :=
    (integrable_map_measure hφ.aestronglyMeasurable hval.aemeasurable).2 hint
  have h2 : Integrable φ (Measure.map (toTensorGL ℝ ℂ ℝ ∘ diagElt)
      ((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) := by
    rw [hν]
    exact h1.smul_measure_nnreal
  have h3 : Integrable (φ ∘ (toTensorGL ℝ ℂ ℝ ∘ diagElt)) ((volume.restrict torusD).withDensity
      fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) :=
    (integrable_map_measure hφ.aestronglyMeasurable measurable_toTensorGL_diagElt.aemeasurable).1 h2
  have h4 := (integrable_withDensity_iff_integrable_smul' hdm hdlt).1 h3
  have hpt : ∀ α : ℝ × ℝ,
      (ENNReal.ofReal |α.1 * α.2|⁻¹).toReal • (φ ∘ (toTensorGL ℝ ℂ ℝ ∘ diagElt)) α =
        |α.1 * α.2|⁻¹ * φ (toTensorGL ℝ ℂ ℝ (diagElt α)) :=
    fun α => by
      rw [ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg _)), smul_eq_mul, Function.comp_apply,
        Function.comp_apply]
  refine ⟨h4.congr (Filter.Eventually.of_forall hpt), ?_⟩
  calc ∫ α in torusD, |α.1 * α.2|⁻¹ * φ (toTensorGL ℝ ℂ ℝ (diagElt α))
      = ∫ α, φ (toTensorGL ℝ ℂ ℝ (diagElt α))
          ∂((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹) := by
        rw [integral_withDensity_eq_integral_toReal_smul hdm hdlt]
        exact (integral_congr_ae (Filter.Eventually.of_forall hpt)).symm
    _ = ∫ g, φ g ∂(Measure.map (toTensorGL ℝ ℂ ℝ ∘ diagElt)
          ((volume.restrict torusD).withDensity fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)) :=
        (integral_map measurable_toTensorGL_diagElt.aemeasurable hφ.aestronglyMeasurable).symm
    _ = (cT⁻¹ : NNReal) • ∫ g, φ g ∂(Measure.map Subtype.val τ) := by
        rw [hν, integral_smul_nnreal_measure]
    _ = (cT : ℝ)⁻¹ * ∫ t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, φ t ∂τ := by
        rw [integral_map hval.aemeasurable hφ.aestronglyMeasurable, NNReal.smul_def, smul_eq_mul,
          NNReal.coe_inv]

private theorem torus_integral_section (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
          (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ φ w)
    (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (hx : φ (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) ≠ 0) :
    Integrable (fun α : ℝ × ℝ => |α.1 * α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (diagElt α) * x))
        (volume.restrict torusD) ∧
      ∫ α in torusD, |α.1 * α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (diagElt α) * x) = (cT : ℝ)⁻¹ := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  obtain ⟨-, hwm, -, hsec⟩ := hw
  have hφx : Measurable fun g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => w (g * x) :=
    hwm.comp (continuous_mul_right x).measurable
  have hsec1 : ∫ t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, w (t * x) ∂τ = 1 := hsec x hx
  have hint : Integrable (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => w (t * x)) τ := by
    by_contra hni
    rw [integral_undef hni] at hsec1
    exact zero_ne_one hsec1
  obtain ⟨hiα, hval⟩ := coset_transfer_split δ τ cT hcT hτ (fun g => w (g * x)) hφx hint
  rw [hsec1, mul_one] at hval
  exact ⟨hiα, hval⟩

private theorem orbit_mul_left (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
    (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x) =
      x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x := by
  have h0 : (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * δ * (sigmaGL ℝ ℂ ℝ Complex.conjAe (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)))⁻¹ = δ :=
    t.2
  rw [mul_inv_eq_iff_eq_mul] at h0
  have ht : (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) = δ := by
    rw [mul_assoc, ← h0, inv_mul_cancel_left]
  calc ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x)
      = x⁻¹ * ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) *
          sigmaGL ℝ ℂ ℝ Complex.conjAe x := by
        simp only [map_mul, mul_inv_rev, mul_assoc]
    _ = x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x := by
        rw [ht]

private def ellD : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)

private def ellElt (q : ℝ × ℝ) : GL (Fin 2) ℝ :=
  if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1

private theorem ellElt_apply_of_pos (q : ℝ × ℝ) (hq : 0 < q.1) : ellElt q = ellipticElt q.1 q.2 hq :=
  dif_pos hq

private theorem coe_ellipticElt (r θ : ℝ) (hr : 0 < r) :
    ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] :=
  rfl

private theorem isOpen_posFst : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst

private theorem continuousOn_ellElt : ContinuousOn ellElt {q : ℝ × ℝ | 0 < q.1} := by
  rw [isEmbedding_glVal'.continuousOn_iff]
  have h : Set.EqOn (Units.val ∘ ellElt)
      (fun q : ℝ × ℝ => !![q.1 * Real.cos q.2, q.1 * Real.sin q.2; -(q.1 * Real.sin q.2), q.1 * Real.cos q.2])
      {q : ℝ × ℝ | 0 < q.1} := by
    intro q (hq : 0 < q.1)
    show ((ellElt q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [ellElt_apply_of_pos q hq, coe_ellipticElt]
  refine ContinuousOn.congr ?_ h
  refine (continuous_matrix fun i j => ?_).continuousOn
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem measurable_ellElt : @Measurable (ℝ × ℝ) (GL (Fin 2) ℝ) _ (glBorelOf ℝ) ellElt :=
  measurable_of_continuousOn_of_eq_one isOpen_posFst continuousOn_ellElt fun q hq => by
    have hq' : ¬ 0 < q.1 := hq
    show (if h : 0 < q.1 then ellipticElt q.1 q.2 h else 1) = 1
    rw [dif_neg hq']

private theorem measurableSet_ellD : MeasurableSet ellD := by
  exact measurableSet_Ioi.prod measurableSet_Ioo

private theorem measurable_toTensorGL_ellElt :
    @Measurable (ℝ × ℝ) (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (toTensorGL ℝ ℂ ℝ ∘ ellElt) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  exact TwistedTorus.Rid.continuous_toTensorGL.measurable.comp measurable_ellElt

private theorem coset_transfer_elliptic (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hφ : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ φ)
    (hint : Integrable (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => φ t) τ) :
    Integrable (fun q : ℝ × ℝ => q.1⁻¹ * φ (toTensorGL ℝ ℂ ℝ (ellElt q))) (volume.restrict ellD) ∧
      ∫ q in ellD, q.1⁻¹ * φ (toTensorGL ℝ ℂ ℝ (ellElt q)) =
        (cT : ℝ)⁻¹ * ∫ t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, φ t ∂τ := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  have hval : Measurable (Subtype.val : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    continuous_subtype_val.measurable
  have hdm : Measurable fun q : ℝ × ℝ => ENNReal.ofReal q.1⁻¹ :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => q.1⁻¹).ennreal_ofReal
  have hdlt : ∀ᵐ q ∂(volume.restrict ellD), ENNReal.ofReal q.1⁻¹ < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hτ' : Measure.map Subtype.val τ =
      cT • Measure.map (toTensorGL ℝ ℂ ℝ ∘ ellElt)
        ((volume.restrict ellD).withDensity fun q => ENNReal.ofReal q.1⁻¹) :=
    hτ
  have hν : Measure.map (toTensorGL ℝ ℂ ℝ ∘ ellElt)
        ((volume.restrict ellD).withDensity fun q => ENNReal.ofReal q.1⁻¹) =
      cT⁻¹ • Measure.map Subtype.val τ := by
    rw [hτ', smul_smul, inv_mul_cancel₀ hcT.ne', one_smul]
  have h1 : Integrable φ (Measure.map Subtype.val τ) :=
    (integrable_map_measure hφ.aestronglyMeasurable hval.aemeasurable).2 hint
  have h2 : Integrable φ (Measure.map (toTensorGL ℝ ℂ ℝ ∘ ellElt)
      ((volume.restrict ellD).withDensity fun q => ENNReal.ofReal q.1⁻¹)) := by
    rw [hν]
    exact h1.smul_measure_nnreal
  have h3 : Integrable (φ ∘ (toTensorGL ℝ ℂ ℝ ∘ ellElt))
      ((volume.restrict ellD).withDensity fun q => ENNReal.ofReal q.1⁻¹) :=
    (integrable_map_measure hφ.aestronglyMeasurable measurable_toTensorGL_ellElt.aemeasurable).1 h2
  have h4 := (integrable_withDensity_iff_integrable_smul' hdm hdlt).1 h3
  have hpt : ∀ᵐ q ∂(volume.restrict ellD),
      (ENNReal.ofReal q.1⁻¹).toReal • (φ ∘ (toTensorGL ℝ ℂ ℝ ∘ ellElt)) q =
        q.1⁻¹ * φ (toTensorGL ℝ ℂ ℝ (ellElt q)) := by
    refine (ae_restrict_iff' measurableSet_ellD).2 (Filter.Eventually.of_forall fun q hq => ?_)
    have hq1 : 0 < q.1 := (Set.mem_prod.1 hq).1
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 hq1.le), smul_eq_mul, Function.comp_apply, Function.comp_apply]
  refine ⟨h4.congr hpt, ?_⟩
  calc ∫ q in ellD, q.1⁻¹ * φ (toTensorGL ℝ ℂ ℝ (ellElt q))
      = ∫ q, φ (toTensorGL ℝ ℂ ℝ (ellElt q)) ∂((volume.restrict ellD).withDensity fun q => ENNReal.ofReal q.1⁻¹) := by
        rw [integral_withDensity_eq_integral_toReal_smul hdm hdlt]
        exact (integral_congr_ae hpt).symm
    _ = ∫ g, φ g ∂(Measure.map (toTensorGL ℝ ℂ ℝ ∘ ellElt)
          ((volume.restrict ellD).withDensity fun q => ENNReal.ofReal q.1⁻¹)) :=
        (integral_map measurable_toTensorGL_ellElt.aemeasurable hφ.aestronglyMeasurable).symm
    _ = (cT⁻¹ : NNReal) • ∫ g, φ g ∂(Measure.map Subtype.val τ) := by
        rw [hν, integral_smul_nnreal_measure]
    _ = (cT : ℝ)⁻¹ * ∫ t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, φ t ∂τ := by
        rw [integral_map hval.aemeasurable hφ.aestronglyMeasurable, NNReal.smul_def, smul_eq_mul,
          NNReal.coe_inv]

private theorem torus_integral_section_elliptic (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ φ w)
    (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (hx : φ (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) ≠ 0) :
    Integrable (fun q : ℝ × ℝ => q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (ellElt q) * x)) (volume.restrict ellD) ∧
      ∫ q in ellD, q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (ellElt q) * x) = (cT : ℝ)⁻¹ := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  obtain ⟨-, hwm, -, hsec⟩ := hw
  have hφx : Measurable fun g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => w (g * x) :=
    hwm.comp (continuous_mul_right x).measurable
  have hsec1 : ∫ t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ, w (t * x) ∂τ = 1 := hsec x hx
  have hint : Integrable (fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => w (t * x)) τ := by
    by_contra hni
    rw [integral_undef hni] at hsec1
    exact zero_ne_one hsec1
  obtain ⟨hiq, hval⟩ := coset_transfer_elliptic δ τ cT hcT hτ (fun g => w (g * x)) hφx hint
  rw [hsec1, mul_one] at hval
  exact ⟨hiq, hval⟩

end TwistedOrbit.Transfer

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit
namespace HaarRef

private theorem det_of_apply (m : Fin 2 → Fin 2 → ℂ) : (Matrix.of m).det = m 0 0 * m 1 1 - m 0 1 * m 1 0 :=
  Matrix.det_fin_two _

private def ridE : ℂ ⊗[ℝ] ℝ ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ)

private theorem ridE_tmul (z : ℂ) (a : ℝ) : ridE (z ⊗ₜ[ℝ] a) = a • z := rfl

private def ridL : (ℂ ⊗[ℝ] ℝ) ≃ₗ[ℝ] ℂ :=
  { ridE with
    map_smul' := fun r x => by
      show ridE (r • x) = r • ridE x
      rw [TensorProduct.RightActions.smul_def]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul z a =>
          rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul, ridE_tmul, ridE_tmul,
            smul_eq_mul, mul_smul]
      | add x y hx hy => simp only [map_add, smul_add, hx, hy] }

private theorem continuous_ridE_symm : Continuous ridE.symm := by
  haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd (ℂ ⊗[ℝ] ℝ) := IsModuleTopology.toContinuousAdd ℝ (ℂ ⊗[ℝ] ℝ)
  have h : Continuous ridL.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap ridL.symm.toLinearMap
  exact h

private theorem continuousOn_matrixInv_isUnit_complex :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.fun_smul ?_ (Continuous.matrix_adjugate continuous_id).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

private theorem isEmbedding_glVal_complex :
    Topology.IsEmbedding (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv_isUnit_complex fun u => (Matrix.coe_units_inv u).symm

private def glOfℂ (A : Fin 2 → Fin 2 → ℂ) : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) :=
  if h : (Matrix.of A).det ≠ 0 then
    Matrix.GeneralLinearGroup.map
      (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h)
  else 1

private def densℂ (A : Fin 2 → Fin 2 → ℂ) : ENNReal := ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹)

private def regSetℂ : Set (Fin 2 → Fin 2 → ℂ) := {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}

private def refMeasureℂ : Measure (Fin 2 → Fin 2 → ℂ) := (volume.restrict regSetℂ).withDensity densℂ

private theorem eq_smul_map_glOfℂ (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ))) (c : NNReal)
    (h : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (fun A : Fin 2 → Fin 2 → ℂ =>
          if h : (Matrix.of A).det ≠ 0 then
            Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).symm.toRingHom
              (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h)
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℂ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal ((Complex.normSq (Matrix.of A).det ^ 2)⁻¹))) :
    μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) glOfℂ refMeasureℂ :=
  h

private def glOfGL (A : Fin 2 → Fin 2 → ℂ) : GL (Fin 2) ℂ :=
  if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h else 1

private theorem glOfℂ_eq (A : Fin 2 → Fin 2 → ℂ) :
    glOfℂ A = Matrix.GeneralLinearGroup.map ridE.symm.toRingHom (glOfGL A) := by
  unfold glOfℂ glOfGL
  split_ifs
  · rfl
  · rw [map_one]

private theorem ridGL_glOfℂ (A : Fin 2 → Fin 2 → ℂ) (hA : (Matrix.of A).det ≠ 0) :
    TwistedTorus.Rid.ridGL (glOfℂ A) = Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) hA := by
  rw [glOfℂ_eq]
  unfold glOfGL
  rw [dif_pos hA]
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply, ridE]

private theorem measurable_densℂ : Measurable densℂ := by
  have h : densℂ = fun A : Fin 2 → Fin 2 → ℂ =>
      ENNReal.ofReal ((Complex.normSq (A 0 0 * A 1 1 - A 0 1 * A 1 0) ^ 2)⁻¹) := by
    funext A
    simp only [densℂ, det_of_apply]
  rw [h]
  have hm : Measurable fun A : Fin 2 → Fin 2 → ℂ => Complex.normSq (A 0 0 * A 1 1 - A 0 1 * A 1 0) :=
    Complex.continuous_normSq.measurable.comp (by fun_prop)
  exact ((hm.pow_const 2).inv).ennreal_ofReal

private theorem densℂ_lt_top (A : Fin 2 → Fin 2 → ℂ) : densℂ A < ⊤ := ENNReal.ofReal_lt_top

private theorem isOpen_regSetℂ : IsOpen regSetℂ := by
  have h : regSetℂ = {A : Fin 2 → Fin 2 → ℂ | A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0} := by
    ext A
    simp only [regSetℂ, Set.mem_setOf_eq, det_of_apply]
  rw [h]
  exact isOpen_ne_fun (by fun_prop) continuous_const

private theorem continuousOn_glOfGL : ContinuousOn glOfGL regSetℂ := by
  rw [isEmbedding_glVal_complex.continuousOn_iff]
  have hof : Continuous fun A : Fin 2 → Fin 2 → ℂ => Matrix.of A :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      fun_prop
  have h : Set.EqOn (Units.val ∘ glOfGL) (fun A => Matrix.of A) regSetℂ := by
    intro A hA
    have hA' : (Matrix.of A).det ≠ 0 := hA
    show ((glOfGL A : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.of A
    unfold glOfGL
    rw [dif_pos hA']
    rfl
  exact hof.continuousOn.congr h

private theorem continuousOn_glOfℂ : ContinuousOn glOfℂ regSetℂ := by
  have h : glOfℂ = Matrix.GeneralLinearGroup.map ridE.symm.toRingHom ∘ glOfGL := funext glOfℂ_eq
  rw [h]
  exact (TwistedTorus.Rid.continuous_glMap continuous_ridE_symm).comp_continuousOn continuousOn_glOfGL

private theorem measurable_of_continuousOn_of_eq_one {P : (Fin 2 → Fin 2 → ℂ) → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)}
    {D : Set (Fin 2 → Fin 2 → ℂ)} (hD : IsOpen D) (hPD : ContinuousOn P D) (hP1 : ∀ A, A ∉ D → P A = 1) :
    @Measurable (Fin 2 → Fin 2 → ℂ) (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) P := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  classical
  have h : P = D.piecewise P (fun _ => 1) := by
    funext A
    by_cases hA : A ∈ D
    · simp [Set.piecewise, hA]
    · simp [Set.piecewise, hA, hP1 A hA]
  rw [h]
  exact hPD.measurable_piecewise continuousOn_const hD.measurableSet

private theorem measurable_glOfℂ :
    @Measurable (Fin 2 → Fin 2 → ℂ) (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) glOfℂ :=
  measurable_of_continuousOn_of_eq_one isOpen_regSetℂ continuousOn_glOfℂ fun A hA => by
    have hA' : ¬ (Matrix.of A).det ≠ 0 := hA
    unfold glOfℂ
    rw [dif_neg hA']

private theorem integral_haar_eqℂ (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ))) (c : NNReal)
    (hμc : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) glOfℂ refMeasureℂ)
    (F : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hF : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ F) :
    ∫ g, F g ∂μ = (c : ℝ) • ∫ A in regSetℂ, (densℂ A).toReal • F (glOfℂ A) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  rw [hμc, integral_smul_nnreal_measure, NNReal.smul_def,
    integral_map measurable_glOfℂ.aemeasurable hF.aestronglyMeasurable]
  unfold refMeasureℂ
  rw [integral_withDensity_eq_integral_toReal_smul measurable_densℂ (Filter.Eventually.of_forall densℂ_lt_top)]

private def eqvℂ : (Fin 2 → Fin 2 → ℂ) ≃ᵐ (ℂ × ℂ) × (ℂ × ℂ) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → ℂ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.finTwoArrow (α := ℂ)) (MeasurableEquiv.finTwoArrow (α := ℂ)))

private theorem eqvℂ_apply (p : Fin 2 → Fin 2 → ℂ) : eqvℂ p = ((p 0 0, p 0 1), (p 1 0, p 1 1)) := rfl

private theorem measurePreserving_eqvℂ : MeasurePreserving eqvℂ volume volume := by
  have h1 := volume_preserving_finTwoArrow (Fin 2 → ℂ)
  have h2 := (volume_preserving_finTwoArrow ℂ).prod (volume_preserving_finTwoArrow ℂ)
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h2
  exact h2.comp h1

private theorem
    setIntegral_eq_of_map_eq {Φ : (Fin 2 → Fin 2 → ℂ) → (Fin 2 → Fin 2 → ℂ)} {D L : Set (Fin 2 → Fin 2 → ℂ)}
    {J : (Fin 2 → Fin 2 → ℂ) → ENNReal} (hJ : Measurable J) (hJlt : ∀ p, J p < ⊤)
    (hmap : Measure.map Φ ((volume.restrict D).withDensity J) = volume.restrict L) (hL : volume L ≠ 0)
    (F : (Fin 2 → Fin 2 → ℂ) → ℂ) (hF : IntegrableOn F L volume) :
    (∫ m in L, F m = ∫ p in D, (J p).toReal • F (Φ p)) ∧
      IntegrableOn (fun p => (J p).toReal • F (Φ p)) D volume := by
  have hae : AEMeasurable Φ ((volume.restrict D).withDensity J) := by
    by_contra h
    rw [Measure.map_of_not_aemeasurable h] at hmap
    exact hL (Measure.restrict_eq_zero.1 hmap.symm)
  have hF' : AEStronglyMeasurable F (Measure.map Φ ((volume.restrict D).withDensity J)) := by
    rw [hmap]
    exact hF.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · rw [← hmap, integral_map hae hF']
    exact integral_withDensity_eq_integral_toReal_smul hJ (Filter.Eventually.of_forall hJlt) _
  · have hi : Integrable F (Measure.map Φ ((volume.restrict D).withDensity J)) := by
      rw [hmap]
      exact hF
    exact (integrable_withDensity_iff_integrable_smul' hJ (Filter.Eventually.of_forall hJlt)).1
      ((integrable_map_measure hF' hae).1 hi)

private theorem integrableOn_iff_of_map_eq {Φ : (Fin 2 → Fin 2 → ℂ) → (Fin 2 → Fin 2 → ℂ)}
    {D L : Set (Fin 2 → Fin 2 → ℂ)} {J : (Fin 2 → Fin 2 → ℂ) → ENNReal} (hJ : Measurable J)
    (hJlt : ∀ p, J p < ⊤) (hmap : Measure.map Φ ((volume.restrict D).withDensity J) = volume.restrict L)
    (hL : volume L ≠ 0) (F : (Fin 2 → Fin 2 → ℂ) → ℂ) (hF : AEStronglyMeasurable F (volume.restrict L)) :
    IntegrableOn F L volume ↔ IntegrableOn (fun p => (J p).toReal • F (Φ p)) D volume := by
  have hae : AEMeasurable Φ ((volume.restrict D).withDensity J) := by
    by_contra h
    rw [Measure.map_of_not_aemeasurable h] at hmap
    exact hL (Measure.restrict_eq_zero.1 hmap.symm)
  have hF' : AEStronglyMeasurable F (Measure.map Φ ((volume.restrict D).withDensity J)) := by
    rw [hmap]
    exact hF
  unfold IntegrableOn
  rw [← hmap, integrable_map_measure hF' hae]
  exact integrable_withDensity_iff_integrable_smul' hJ (Filter.Eventually.of_forall hJlt)

end TwistedOrbit.HaarRef

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit

namespace Window

private theorem coe_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
        Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
          Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] :=
  rfl

private theorem exp_add_pi_mul_I (x : ℝ) :
    Complex.exp (((x + Real.pi : ℝ) : ℂ) * Complex.I) = -Complex.exp ((x : ℂ) * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

private theorem exp_neg_add_pi_mul_I (x : ℝ) :
    Complex.exp (-(((x + Real.pi : ℝ) : ℂ) * Complex.I)) = -Complex.exp (-((x : ℂ) * Complex.I)) := by
  rw [Complex.ofReal_add, add_mul, neg_add, Complex.exp_add, Complex.exp_neg ((Real.pi : ℂ) * Complex.I),
    Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg_one]

private theorem exp_add_two_pi_mul_I (x : ℝ) :
    Complex.exp (((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) := by
  have h2 : (((2 * Real.pi : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) := by simp
  rw [Complex.ofReal_add, h2, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private theorem exp_neg_add_two_pi_mul_I (x : ℝ) :
    Complex.exp (-(((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I)) = Complex.exp (-((x : ℂ) * Complex.I)) := by
  have h2 : (((2 * Real.pi : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) := by simp
  rw [Complex.ofReal_add, h2, add_mul, neg_add, Complex.exp_add, Complex.exp_neg (2 * (Real.pi : ℂ) * Complex.I),
    Complex.exp_two_pi_mul_I, inv_one, mul_one]

private theorem unitaryElt_add_pi (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt (ψ + Real.pi) η ξ₁ ξ₂ = unitaryElt ψ η (ξ₁ + Real.pi) (ξ₂ + Real.pi) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_unitaryElt, coe_unitaryElt, exp_add_pi_mul_I, exp_add_pi_mul_I, exp_add_pi_mul_I,
    exp_neg_add_pi_mul_I, exp_neg_add_pi_mul_I]
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', Fin.zero_eta, Fin.mk_one, Fin.isValue]; ring)

private theorem unitaryElt_add_two_pi_left (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt ψ η (ξ₁ + 2 * Real.pi) ξ₂ = unitaryElt ψ η ξ₁ ξ₂ :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    rw [coe_unitaryElt, coe_unitaryElt, exp_add_two_pi_mul_I, exp_neg_add_two_pi_mul_I]

private theorem unitaryElt_add_two_pi_right (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt ψ η ξ₁ (ξ₂ + 2 * Real.pi) = unitaryElt ψ η ξ₁ ξ₂ :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    rw [coe_unitaryElt, coe_unitaryElt, exp_add_two_pi_mul_I, exp_neg_add_two_pi_mul_I]

private theorem det_coe_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = Complex.exp (ψ * Complex.I) ^ 2 := by
  rw [coe_unitaryElt, Matrix.det_fin_two_of]
  have h1 : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h2 : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h3 : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq η
  linear_combination
    Complex.exp (ψ * Complex.I) ^ 2 * (Real.cos η : ℂ) ^ 2 * h1 +
      Complex.exp (ψ * Complex.I) ^ 2 * (Real.sin η : ℂ) ^ 2 * h2 +
      Complex.exp (ψ * Complex.I) ^ 2 * h3

private theorem unitaryElt_mem_rowIsometrySubgroup (ψ η ξ₁ ξ₂ : ℝ) :
    unitaryElt ψ η ξ₁ ξ₂ ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ := by
  rw [AutomorphicForm.WindowedSiegel.mem_rowIsometrySubgroup_iff]
  refine ⟨?_, fun x y => ?_⟩
  · rw [det_coe_unitaryElt, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]
  · have hP : Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h1 : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h2 : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h3 : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq η
    have hc : ∀ t : ℝ, (starRingEnd ℂ) (Complex.exp (t * Complex.I)) = Complex.exp (-(t * Complex.I)) := fun t => by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    have hc' : ∀ t : ℝ, (starRingEnd ℂ) (Complex.exp (-(t * Complex.I))) = Complex.exp (t * Complex.I) := fun t => by
      rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
    rw [coe_unitaryElt]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    apply Complex.ofReal_injective
    rw [Complex.ofReal_add, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [map_add, map_mul, map_neg, Complex.conj_ofReal, hc, hc']
    linear_combination
      ((starRingEnd ℂ) x * x + (starRingEnd ℂ) y * y) * hP +
        ((starRingEnd ℂ) x * x + (starRingEnd ℂ) y * y) * Complex.exp (ψ * Complex.I) *
            Complex.exp (-(ψ * Complex.I)) * (Real.cos η : ℂ) ^ 2 * h1 +
        ((starRingEnd ℂ) x * x + (starRingEnd ℂ) y * y) * Complex.exp (ψ * Complex.I) *
            Complex.exp (-(ψ * Complex.I)) * (Real.sin η : ℂ) ^ 2 * h2 +
        ((starRingEnd ℂ) x * x + (starRingEnd ℂ) y * y) * Complex.exp (ψ * Complex.I) *
            Complex.exp (-(ψ * Complex.I)) * h3

private theorem continuous_unitaryElt :
    Continuous fun p : ℝ × ℝ × ℝ × ℝ => unitaryElt p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  rw [HaarRef.isEmbedding_glVal_complex.continuous_iff]
  have h : (Units.val ∘ fun p : ℝ × ℝ × ℝ × ℝ => unitaryElt p.1 p.2.1 p.2.2.1 p.2.2.2) = fun p : ℝ × ℝ × ℝ × ℝ =>
      !![Complex.exp (p.1 * Complex.I) * (Real.cos p.2.1 * Complex.exp (p.2.2.1 * Complex.I)),
          Complex.exp (p.1 * Complex.I) * (Real.sin p.2.1 * Complex.exp (p.2.2.2 * Complex.I));
        Complex.exp (p.1 * Complex.I) * (-(Real.sin p.2.1 * Complex.exp (-(p.2.2.2 * Complex.I)))),
          Complex.exp (p.1 * Complex.I) * (Real.cos p.2.1 * Complex.exp (-(p.2.2.1 * Complex.I)))] :=
    funext fun p => coe_unitaryElt _ _ _ _
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_unitaryElt_comp {X : Type*} [TopologicalSpace X] {f g k l : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hk : Continuous k) (hl : Continuous l) :
    Continuous fun x => unitaryElt (f x) (g x) (k x) (l x) := by
  have hc := continuous_unitaryElt.comp (hf.prodMk (hg.prodMk (hk.prodMk hl)))
  exact hc

private theorem integral_zero_two_pi_eq_two_mul_integral_zero_pi (G : ℝ → ℂ) (hG : ∀ θ, G (θ + Real.pi) = G θ)
    (hint : IntegrableOn G (Set.Ioc (0 : ℝ) (2 * Real.pi))) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), G θ = 2 * ∫ θ in (0 : ℝ)..Real.pi, G θ := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hπ2 : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have h1 : IntervalIntegrable G volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).2 hint
  have hA : IntervalIntegrable G volume 0 Real.pi :=
    h1.mono_set (by rw [Set.uIcc_of_le hπ, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc le_rfl hπ2)
  have hB : IntervalIntegrable G volume Real.pi (2 * Real.pi) :=
    h1.mono_set (by rw [Set.uIcc_of_le hπ2, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc hπ le_rfl)
  have hshift : ∫ θ in Real.pi..(2 * Real.pi), G θ = ∫ θ in (0 : ℝ)..Real.pi, G θ := by
    have h := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi) G Real.pi
    simp only [hG, zero_add] at h
    rw [h, two_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB, hshift, two_mul]

private theorem integral_comp_add_pi_of_periodic (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), f (t + Real.pi) = ∫ t in (0 : ℝ)..(2 * Real.pi), f t := by
  have h := hf.intervalIntegral_add_eq Real.pi 0
  rw [zero_add] at h
  rw [intervalIntegral.integral_comp_add_right, zero_add,
    show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring, h]

private theorem box_integral_eq_two_mul (h : GL (Fin 2) ℂ → ℂ) (hh : Continuous h) :
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * h (unitaryElt ψ η ξ₁ ξ₂) =
      2 * ∫ ψ in (0 : ℝ)..Real.pi, ∫ η in (0 : ℝ)..(Real.pi / 2),
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * h (unitaryElt ψ η ξ₁ ξ₂) := by

  have hK : Continuous fun q : ℝ × ℝ × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin q.2.1 * Real.cos q.2.1 : ℂ) * h (unitaryElt q.1 q.2.1 q.2.2 ξ₂) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : ℝ × ℝ × ℝ) (ξ₂ : ℝ) =>
        (Real.sin q.2.1 * Real.cos q.2.1 : ℂ) * h (unitaryElt q.1 q.2.1 q.2.2 ξ₂)) ?_ _ _
    show Continuous fun r : (ℝ × ℝ × ℝ) × ℝ =>
      (Real.sin r.1.2.1 * Real.cos r.1.2.1 : ℂ) * h (unitaryElt r.1.1 r.1.2.1 r.1.2.2 r.2)
    have hU : Continuous fun r : (ℝ × ℝ × ℝ) × ℝ => unitaryElt r.1.1 r.1.2.1 r.1.2.2 r.2 :=
      continuous_unitaryElt_comp (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    have hhU : Continuous fun r : (ℝ × ℝ × ℝ) × ℝ => h (unitaryElt r.1.1 r.1.2.1 r.1.2.2 r.2) := by
      have hc := hh.comp hU
      exact hc
    exact (by fun_prop : Continuous fun r : (ℝ × ℝ × ℝ) × ℝ => (Real.sin r.1.2.1 * Real.cos r.1.2.1 : ℂ)).mul hhU
  have hH : Continuous fun q : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin q.2 * Real.cos q.2 : ℂ) * h (unitaryElt q.1 q.2 ξ₁ ξ₂) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : ℝ × ℝ) (ξ₁ : ℝ) => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin q.2 * Real.cos q.2 : ℂ) * h (unitaryElt q.1 q.2 ξ₁ ξ₂)) ?_ _ _
    show Continuous fun r : (ℝ × ℝ) × ℝ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin r.1.2 * Real.cos r.1.2 : ℂ) * h (unitaryElt r.1.1 r.1.2 r.2 ξ₂)
    have hc := hK.comp (by fun_prop : Continuous fun r : (ℝ × ℝ) × ℝ => (r.1.1, r.1.2, r.2))
    exact hc
  have hG : Continuous fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * h (unitaryElt ψ η ξ₁ ξ₂) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (ψ : ℝ) (η : ℝ) => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * h (unitaryElt ψ η ξ₁ ξ₂)) ?_ _ _
    show Continuous fun r : ℝ × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin r.2 * Real.cos r.2 : ℂ) * h (unitaryElt r.1 r.2 ξ₁ ξ₂)
    exact hH
  refine integral_zero_two_pi_eq_two_mul_integral_zero_pi
    (fun ψ : ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * h (unitaryElt ψ η ξ₁ ξ₂))
    (fun ψ => ?_) (hG.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)

  simp only [unitaryElt_add_pi]
  refine intervalIntegral.integral_congr fun η _ => ?_
  have hper₁ : Function.Periodic (fun ξ₁ => ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * h (unitaryElt ψ η ξ₁ (ξ₂ + Real.pi))) (2 * Real.pi) := fun ξ₁ => by
    simp only [unitaryElt_add_two_pi_left]
  have hstep₁ := integral_comp_add_pi_of_periodic _ hper₁
  rw [hstep₁]
  refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
  have hper₂ : Function.Periodic (fun ξ₂ => (Real.sin η * Real.cos η : ℂ) * h (unitaryElt ψ η ξ₁ ξ₂))
      (2 * Real.pi) := fun ξ₂ => by
    simp only [unitaryElt_add_two_pi_right]
  exact integral_comp_add_pi_of_periodic _ hper₂

end Window

namespace Coords

private def negFst : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl ℝ)

private def negSnd : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

private theorem negFst_apply (b : ℝ × ℝ) : negFst b = (-b.1, b.2) := rfl

private theorem negSnd_apply (b : ℝ × ℝ) : negSnd b = (b.1, -b.2) := rfl

private theorem measurePreserving_negFst : MeasurePreserving negFst volume volume := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id (volume : Measure ℝ))
  rw [← Measure.volume_eq_prod] at h
  exact h

private theorem measurePreserving_negSnd : MeasurePreserving negSnd volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  rw [← Measure.volume_eq_prod] at h
  exact h

private theorem setIntegral_off_axes_eq (h : ℝ × ℝ → ℝ) (hi : IntegrableOn h {α : ℝ × ℝ | α.1 * α.2 ≠ 0}) :
    ∫ α in {α : ℝ × ℝ | α.1 * α.2 ≠ 0}, h α =
      ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), (h b + h (-b.1, b.2) + h (b.1, -b.2) + h (-b.1, -b.2)) := by

  have hm₁ : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hm₂ : MeasurableSet (Set.Iio (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := measurableSet_Iio.prod measurableSet_Ioi
  have hm₃ : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Iio
  have hm₄ : MeasurableSet (Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) := measurableSet_Iio.prod measurableSet_Iio
  have hsplit : {α : ℝ × ℝ | α.1 * α.2 ≠ 0} =
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ∪ Set.Iio (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ∪
        (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ) ∪ Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod, Set.mem_Ioi, Set.mem_Iio, mul_ne_zero_iff]
    simp only [ne_iff_lt_or_gt]
    tauto
  have hIoiIio : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio 0) :=
    Set.disjoint_left.2 fun x (hx : 0 < x) (hx' : x < 0) => lt_asymm hx hx'
  have hIioIoi : Disjoint (Set.Iio (0 : ℝ)) (Set.Ioi 0) :=
    Set.disjoint_left.2 fun x (hx : x < 0) (hx' : 0 < x) => lt_asymm hx hx'
  have hd₁₂ : Disjoint (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) (Set.Iio (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
    Set.disjoint_prod.2 (Or.inl hIoiIio)
  have hd₃₄ : Disjoint (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) (Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) :=
    Set.disjoint_prod.2 (Or.inl hIoiIio)
  have hdAB : Disjoint (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ∪ Set.Iio (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ) ∪ Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) :=
    Set.disjoint_union_left.2
      ⟨Set.disjoint_union_right.2 ⟨Set.disjoint_prod.2 (Or.inr hIoiIio), Set.disjoint_prod.2 (Or.inr hIoiIio)⟩,
        Set.disjoint_union_right.2 ⟨Set.disjoint_prod.2 (Or.inr hIoiIio), Set.disjoint_prod.2 (Or.inr hIoiIio)⟩⟩

  have hi₁ : IntegrableOn h (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
    hi.mono_set (by rw [hsplit]; exact Set.subset_union_left.trans Set.subset_union_left)
  have hi₂ : IntegrableOn h (Set.Iio (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
    hi.mono_set (by rw [hsplit]; exact Set.subset_union_right.trans Set.subset_union_left)
  have hi₃ : IntegrableOn h (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) :=
    hi.mono_set (by rw [hsplit]; exact Set.subset_union_left.trans Set.subset_union_right)
  have hi₄ : IntegrableOn h (Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) :=
    hi.mono_set (by rw [hsplit]; exact Set.subset_union_right.trans Set.subset_union_right)

  have hpre₂ : negFst ⁻¹' (Set.Iio (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) = Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    ext b
    simp [negFst_apply]
  have hpre₃ : negSnd ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) = Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    ext b
    simp [negSnd_apply]
  have hpre₄ : negFst ⁻¹' (Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) = Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ) := by
    ext b
    simp [negFst_apply]
  have hr₂ : ∫ α in Set.Iio (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), h α =
      ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), h (-b.1, b.2) := by
    rw [← hpre₂]
    exact (measurePreserving_negFst.setIntegral_preimage_emb negFst.measurableEmbedding h _).symm
  have hr₃ : ∫ α in Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ), h α =
      ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), h (b.1, -b.2) := by
    rw [← hpre₃]
    exact (measurePreserving_negSnd.setIntegral_preimage_emb negSnd.measurableEmbedding h _).symm
  have hr₄ : ∫ α in Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ), h α =
      ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), h (-b.1, -b.2) := by
    have h₁ : ∫ α in Set.Iio (0 : ℝ) ×ˢ Set.Iio (0 : ℝ), h α =
        ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ), h (-b.1, b.2) := by
      rw [← hpre₄]
      exact (measurePreserving_negFst.setIntegral_preimage_emb negFst.measurableEmbedding h _).symm
    rw [h₁, ← hpre₃]
    exact (measurePreserving_negSnd.setIntegral_preimage_emb negSnd.measurableEmbedding
      (fun b => h (-b.1, b.2)) _).symm

  have hI₂ : IntegrableOn (fun b : ℝ × ℝ => h (-b.1, b.2)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    have h' := (measurePreserving_negFst.integrableOn_comp_preimage negFst.measurableEmbedding).2 hi₂
    have hc : h ∘ negFst = fun b : ℝ × ℝ => h (-b.1, b.2) := funext fun b => rfl
    rw [hc, hpre₂] at h'
    exact h'
  have hI₃ : IntegrableOn (fun b : ℝ × ℝ => h (b.1, -b.2)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    have h' := (measurePreserving_negSnd.integrableOn_comp_preimage negSnd.measurableEmbedding).2 hi₃
    have hc : h ∘ negSnd = fun b : ℝ × ℝ => h (b.1, -b.2) := funext fun b => rfl
    rw [hc, hpre₃] at h'
    exact h'
  have hI₄' : IntegrableOn (fun b : ℝ × ℝ => h (-b.1, b.2)) (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) := by
    have h' := (measurePreserving_negFst.integrableOn_comp_preimage negFst.measurableEmbedding).2 hi₄
    have hc : h ∘ negFst = fun b : ℝ × ℝ => h (-b.1, b.2) := funext fun b => rfl
    rw [hc, hpre₄] at h'
    exact h'
  have hI₄ : IntegrableOn (fun b : ℝ × ℝ => h (-b.1, -b.2)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    have h' := (measurePreserving_negSnd.integrableOn_comp_preimage negSnd.measurableEmbedding).2 hI₄'
    have hc : (fun b : ℝ × ℝ => h (-b.1, b.2)) ∘ negSnd = fun b : ℝ × ℝ => h (-b.1, -b.2) := funext fun b => rfl
    rw [hc, hpre₃] at h'
    exact h'
  have hI₁₂ : Integrable (fun b : ℝ × ℝ => h b + h (-b.1, b.2))
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) := hi₁.add hI₂
  have hI₁₂₃ : Integrable (fun b : ℝ × ℝ => h b + h (-b.1, b.2) + h (b.1, -b.2))
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) := hI₁₂.add hI₃
  rw [hsplit, setIntegral_union hdAB (hm₃.union hm₄) (hi₁.union hi₂) (hi₃.union hi₄),
    setIntegral_union hd₁₂ hm₂ hi₁ hi₂, setIntegral_union hd₃₄ hm₄ hi₃ hi₄, hr₂, hr₃, hr₄, ← add_assoc,
    ← integral_add hi₁ hI₂, ← integral_add hI₁₂ hI₃, ← integral_add hI₁₂₃ hI₄]

end Coords

namespace Average

private theorem integral_mul_comp_mul_left {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (Φ : G → ℂ) (W : G → ℂ) (t : G) (hΦ : ∀ x, Φ (t * x) = Φ x) :
    ∫ x, Φ x * W (t * x) ∂μ = ∫ x, Φ x * W x ∂μ := by
  have h := integral_mul_left_eq_self (μ := μ) (fun x => Φ x * W x) t
  simp only [hΦ] at h
  exact h

end Average

end TwistedOrbit

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit

namespace Window

private theorem exp_add_mul_I (x y : ℝ) :
    Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
  push_cast
  rw [add_mul, Complex.exp_add]

private theorem exp_neg_add_mul_I (x y : ℝ) :
    Complex.exp (-(((x + y : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-((x : ℂ) * Complex.I)) * Complex.exp (-((y : ℂ) * Complex.I)) := by
  push_cast
  rw [add_mul, neg_add, Complex.exp_add]

private theorem exp_mul_I_mul_exp_neg_mul_I (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) * Complex.exp (-((x : ℂ) * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem exp_two_mul_mul_I (ψ : ℝ) :
    Complex.exp (2 * (ψ : ℂ) * Complex.I) =
      Complex.exp ((ψ : ℂ) * Complex.I) * Complex.exp ((ψ : ℂ) * Complex.I) := by
  have h : (2 * (ψ : ℂ) * Complex.I) = (ψ : ℂ) * Complex.I + (ψ : ℂ) * Complex.I := by ring
  rw [h, Complex.exp_add]

private theorem coe_unitaryElt_zero_zero (ψ : ℝ) :
    ((unitaryElt 0 0 ψ 0 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I), 0; 0, Complex.exp (-(ψ * Complex.I))] := by
  rw [coe_unitaryElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem unitaryElt_zero_zero_mul (ψ ψ₀ η ξ₁ ξ₂ : ℝ) :
    unitaryElt 0 0 ψ 0 * unitaryElt ψ₀ η ξ₁ ξ₂ = unitaryElt ψ₀ η (ξ₁ + ψ) (ξ₂ + ψ) := by
  apply Units.ext
  rw [Units.val_mul, coe_unitaryElt_zero_zero, coe_unitaryElt, coe_unitaryElt, exp_add_mul_I, exp_add_mul_I,
    exp_neg_add_mul_I, exp_neg_add_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    ring

private theorem diagPhase_mul_upper (ψ : ℝ) (b₁ b₂ z : ℂ) :
    !![Complex.exp (ψ * Complex.I), 0; 0, Complex.exp (-(ψ * Complex.I))] * !![b₁, b₁ * z; 0, b₂] =
      !![b₁, b₁ * (Complex.exp (2 * ψ * Complex.I) * z); 0, b₂] *
        !![Complex.exp (ψ * Complex.I), 0; 0, Complex.exp (-(ψ * Complex.I))] := by
  have hN := exp_mul_I_mul_exp_neg_mul_I ψ
  rw [exp_two_mul_mul_I]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination (-(b₁ * z * Complex.exp ((ψ : ℂ) * Complex.I))) * hN
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring

end Window

end TwistedOrbit

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit
namespace Proper

private theorem conj_exp_mul_I (t : ℝ) : (starRingEnd ℂ) (Complex.exp (t * Complex.I)) = Complex.exp (-(t *
    Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

private theorem conj_exp_neg_mul_I (t : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(t * Complex.I))) = Complex.exp (t * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]

private def frobSq (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (X 0 0) + Complex.normSq (X 0 1) + Complex.normSq (X 1 0) + Complex.normSq (X 1 1)

private theorem continuous_frobSq_val : Continuous fun g : GL (Fin 2) ℂ => frobSq (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  have he : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j =>
    TwistedOrbit.HaarRef.isEmbedding_glVal_complex.continuous.matrix_elem i j
  unfold frobSq
  exact (((Complex.continuous_normSq.comp (he 0 0)).add (Complex.continuous_normSq.comp (he 0 1))).add
    (Complex.continuous_normSq.comp (he 1 0))).add (Complex.continuous_normSq.comp (he 1 1))

private theorem frobSq_mul_left (U Y : Matrix (Fin 2) (Fin 2) ℂ) (hU : U.conjTranspose * U = 1) : frobSq (U * Y) =
    frobSq Y := by
  have h00 := congrFun (congrFun hU 0) 0
  have h01 := congrFun (congrFun hU 0) 1
  have h10 := congrFun (congrFun hU 1) 0
  have h11 := congrFun (congrFun hU 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h00 h01 h10 h11
  apply Complex.ofReal_injective
  simp only [frobSq, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, Matrix.mul_apply, Fin.sum_univ_two, map_add,
    map_mul]
  linear_combination ((starRingEnd ℂ) (Y 0 0) * Y 0 0 + (starRingEnd ℂ) (Y 0 1) * Y 0 1) * h00 + ((starRingEnd ℂ) (Y
    0 0) * Y 1 0 + (starRingEnd ℂ) (Y 0 1) * Y 1 1) * h01 + ((starRingEnd ℂ) (Y 1 0) * Y 0 0 + (starRingEnd ℂ) (Y 1
    1) * Y 0 1) * h10 + ((starRingEnd ℂ) (Y 1 0) * Y 1 0 + (starRingEnd ℂ) (Y 1 1) * Y 1 1) * h11

private theorem frobSq_mul_right (Y V : Matrix (Fin 2) (Fin 2) ℂ) (hV : V * V.conjTranspose = 1) : frobSq (Y * V) =
    frobSq Y := by
  have h00 := congrFun (congrFun hV 0) 0
  have h01 := congrFun (congrFun hV 0) 1
  have h10 := congrFun (congrFun hV 1) 0
  have h11 := congrFun (congrFun hV 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h00 h01 h10 h11
  apply Complex.ofReal_injective
  simp only [frobSq, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, Matrix.mul_apply, Fin.sum_univ_two, map_add,
    map_mul]
  linear_combination ((starRingEnd ℂ) (Y 0 0) * Y 0 0 + (starRingEnd ℂ) (Y 1 0) * Y 1 0) * h00 + ((starRingEnd ℂ) (Y
    0 1) * Y 0 0 + (starRingEnd ℂ) (Y 1 1) * Y 1 0) * h01 + ((starRingEnd ℂ) (Y 0 0) * Y 0 1 + (starRingEnd ℂ) (Y 1
    0) * Y 1 1) * h10 + ((starRingEnd ℂ) (Y 0 1) * Y 0 1 + (starRingEnd ℂ) (Y 1 1) * Y 1 1) * h11

private theorem val_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
        Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
          Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] := by
  first
    | rfl
    | (simp only [unitaryElt, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; done)
    | (simp [unitaryElt]; done)

private theorem val_conjEntries (g : GL (Fin 2) ℂ) :
    ((conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ)
        := by
  first
    | rfl
    | (simp [conjEntries]; done)

private theorem val_unitaryElt_mul_conjTranspose (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 := by
  have hψ : Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hξ₁ : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hξ₂ : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcs : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq η
  rw [val_unitaryElt, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) * (Real.cos η : ℂ) ^ 2 +
      Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) * (Real.sin η : ℂ) ^ 2) * hψ + ((Real.cos η :
      ℂ) ^ 2) * hξ₁ + ((Real.sin η : ℂ) ^ 2) * hξ₂ + (1) * hcs
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (0 : ℂ) * hψ
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (0 : ℂ) * hψ
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) * (Real.cos η : ℂ) ^ 2 +
      Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) * (Real.sin η : ℂ) ^ 2) * hψ + ((Real.cos η :
      ℂ) ^ 2) * hξ₁ + ((Real.sin η : ℂ) ^ 2) * hξ₂ + (1) * hcs

private theorem val_conjEntries_unitaryElt_mul_conjTranspose (ψ η ξ₁ ξ₂ : ℝ) :
    ((conjEntries (unitaryElt ψ η ξ₁ ξ₂) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      ((conjEntries (unitaryElt ψ η ξ₁ ξ₂) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 := by
  have hψ : Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hξ₁ : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hξ₂ : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcs : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq η
  rw [val_conjEntries, val_unitaryElt, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) * (Real.cos η : ℂ) ^ 2 +
      Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) * (Real.sin η : ℂ) ^ 2) * hψ + ((Real.cos η :
      ℂ) ^ 2) * hξ₁ + ((Real.sin η : ℂ) ^ 2) * hξ₂ + (1) * hcs
  · simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (0 : ℂ) * hψ
  · simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (0 : ℂ) * hψ
  · simp only [Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
      Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_mul, map_neg, Complex.conj_ofReal, conj_exp_mul_I,
      conj_exp_neg_mul_I]
    linear_combination (Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) * (Real.cos η : ℂ) ^ 2 +
      Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) * (Real.sin η : ℂ) ^ 2) * hψ + ((Real.cos η :
      ℂ) ^ 2) * hξ₁ + ((Real.sin η : ℂ) ^ 2) * hξ₂ + (1) * hcs

private theorem val_unitaryElt_inv (ψ η ξ₁ ξ₂ : ℝ) :
    (((unitaryElt ψ η ξ₁ ξ₂)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose := by
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_right_inv (val_unitaryElt_mul_conjTranspose ψ η ξ₁ ξ₂)

private theorem frobSq_twistedConj (ψ η ξ₁ ξ₂ : ℝ) (M : GL (Fin 2) ℂ) :
    frobSq (((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * M * conjEntries (unitaryElt ψ η ξ₁ ξ₂) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin
        2) ℂ) =
      frobSq (M : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hU : ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose.conjTranspose *
      ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact val_unitaryElt_mul_conjTranspose ψ η ξ₁ ξ₂
  rw [Units.val_mul, Units.val_mul, val_unitaryElt_inv,
    frobSq_mul_right _ _ (val_conjEntries_unitaryElt_mul_conjTranspose ψ η ξ₁ ξ₂), frobSq_mul_left _ _ hU]

private theorem val_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![(Real.sqrt a₁ : ℂ), v; 0,
        (Real.sqrt a₂ : ℂ)] := by
  first
    | rfl
    | (simp only [twistedSplitElt, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; done)
    | (simp [twistedSplitElt]; done)

private theorem frobSq_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    frobSq ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = a₁ + Complex.normSq v + a₂ := by
  rw [val_twistedSplitElt]
  simp only [frobSq, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Complex.normSq_ofReal,
    map_zero, Real.mul_self_sqrt h.1.le, Real.mul_self_sqrt h.2.le]
  ring

private theorem val_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))),
          (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
            (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)));
        (Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I))),
          (Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))] := by
  first
    | rfl
    | (simp only [twistedEllipticElt, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; done)
    | (simp [twistedEllipticElt]; done)

private theorem normSq_exp_half (θ : ℝ) : Complex.normSq (Complex.exp (θ / 2 * Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp

private theorem normSq_exp_neg_half (θ : ℝ) : Complex.normSq (Complex.exp (-(θ / 2 * Complex.I))) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp

private theorem re_exp_half_mul_exp_half (θ : ℝ) :
    (Complex.exp (θ / 2 * Complex.I) * Complex.exp (θ / 2 * Complex.I)).re = Real.cos θ := by
  rw [← Complex.exp_add, show (θ / 2 * Complex.I + θ / 2 * Complex.I : ℂ) = (θ : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I_re]

private theorem conj_exp_neg_half (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(θ / 2 * Complex.I))) = Complex.exp (θ / 2 * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg, map_ofNat]

private theorem frobSq_twistedEllipticElt_ge (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    r * ρ ^ 2 ≤ frobSq ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ∧
      r * (Complex.normSq u * ρ ^ 2) ≤ frobSq ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2)
          (Fin 2) ℂ) ∧
      r * Real.sin θ ^ 2 ≤ ρ ^ 2 * (frobSq ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin
          2) ℂ) + 2 * r) := by
  rw [val_twistedEllipticElt]
  simp only [frobSq, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.normSq_mul,
    Complex.normSq_neg, Complex.normSq_ofReal, Complex.normSq_conj, normSq_exp_half, normSq_exp_neg_half,
    Real.mul_self_sqrt hr.le, Complex.normSq_sub, Complex.normSq_inv]
  have hre : ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) *
      (starRingEnd ℂ) ((Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)))).re =
        (ρ⁻¹ * (Complex.normSq u * ρ)) * Real.cos θ := by
    rw [map_mul, map_mul, conj_exp_neg_half, Complex.conj_ofReal, Complex.conj_ofReal,
      show ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) * ((Complex.normSq u : ℂ) * ρ * Complex.exp (θ / 2 *
          Complex.I)))
          = (((ρ⁻¹ * (Complex.normSq u * ρ) : ℝ)) : ℂ) * (Complex.exp (θ / 2 * Complex.I) * Complex.exp (θ / 2 *
              Complex.I))
        by push_cast; ring,
      Complex.re_ofReal_mul, re_exp_half_mul_exp_half]
  rw [hre]
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hρ' : ρ⁻¹ * (Complex.normSq u * ρ) = Complex.normSq u := by field_simp
  rw [hρ']
  have hu := Complex.normSq_nonneg u
  have hinv : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0
  have hinv2 : (ρ * ρ)⁻¹ = ρ⁻¹ * ρ⁻¹ := by rw [mul_inv]
  have hsu : Complex.normSq u * (ρ⁻¹ * ρ) = Complex.normSq u := by rw [hinv, mul_one]
  have hm01 : 2 * (Complex.normSq u * Real.cos θ) ≤ (ρ * ρ)⁻¹ + Complex.normSq u * Complex.normSq u * (ρ * ρ) := by
    nlinarith [sq_nonneg (ρ⁻¹ - Complex.normSq u * ρ), hsu, hinv2, mul_nonneg hu (sub_nonneg.2 (Real.cos_le_one θ))]
  have hA : 0 ≤ r * (Complex.normSq u * (ρ * ρ)) := mul_nonneg hr.le (mul_nonneg hu (mul_self_nonneg ρ))
  have hB : 0 ≤ r * ((ρ * ρ)⁻¹ + Complex.normSq u * Complex.normSq u * (ρ * ρ) - 2 * (Complex.normSq u * Real.cos
      θ)) :=
    mul_nonneg hr.le (by linarith [hm01])
  have hC : 0 ≤ r * (ρ * ρ) := mul_nonneg hr.le (mul_self_nonneg ρ)
  have hsq : 0 ≤ r * (Complex.normSq u * (ρ * ρ) + (ρ * ρ - Real.cos θ)) ^ 2 := mul_nonneg hr.le (sq_nonneg _)
  have hcosr : 0 ≤ r * (ρ * ρ) * (1 + Real.cos θ) := mul_nonneg hC (by linarith [Real.neg_one_le_cos θ])
  have hrcs : r * (Real.cos θ ^ 2 + Real.sin θ ^ 2) = r := by rw [Real.cos_sq_add_sin_sq, mul_one]
  have hrinv : r * ((ρ * ρ)⁻¹ * (ρ * ρ)) = r := by rw [inv_mul_cancel₀ (mul_ne_zero hρ0 hρ0), mul_one]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hA, hB, hC]
  · nlinarith [hA, hB, hC]
  · nlinarith [hsq, hcosr, hrcs, hrinv, hA, hC]

private def ellipticArray (r θ : ℝ) (w : ℂ) (ρ : ℝ) (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))),
      (Real.sqrt r : ℂ) * (w * Complex.exp (θ / 2 * Complex.I) -
        (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)));
    (Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I))),
      (Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))]

private theorem exists_bound_split (φ : GL (Fin 2) ℂ → ℂ) (hφc : HasCompactSupport φ) (a₁ a₂ : ℝ)
    (h : 0 < a₁ ∧ 0 < a₂) :
    ∃ R : ℝ, ∀ (ψ η ξ₁ ξ₂ : ℝ) (v : ℂ),
      φ ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (unitaryElt ψ η ξ₁ ξ₂)) ≠ 0 →
        ‖v‖ ≤ R := by
  have hK : IsCompact (tsupport φ) := hφc
  obtain ⟨R₀, hR₀⟩ := hK.bddAbove_image continuous_frobSq_val.continuousOn
  refine ⟨Real.sqrt (max R₀ 0), fun ψ η ξ₁ ξ₂ v hv => ?_⟩
  have hmem : (unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (unitaryElt ψ η ξ₁ ξ₂) ∈ tsupport φ :=
    subset_tsupport φ hv
  have hle : frobSq ((((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (unitaryElt ψ η ξ₁ ξ₂) :
      GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)) ≤ R₀ :=
    hR₀ (Set.mem_image_of_mem _ hmem)
  rw [frobSq_twistedConj, frobSq_twistedSplitElt, Complex.normSq_eq_norm_sq] at hle
  exact (Real.le_sqrt (norm_nonneg v) (le_max_right R₀ 0)).2 (by nlinarith [h.1, h.2, le_max_left R₀ 0])

private theorem exists_bound_elliptic (φ : GL (Fin 2) ℂ → ℂ) (hφc : HasCompactSupport φ) (r θ : ℝ) (hr : 0 < r)
    (hθ : Real.sin θ ≠ 0) :
    ∃ R ε : ℝ, 0 < ε ∧ ∀ (ψ η ξ₁ ξ₂ ρ : ℝ) (u : ℂ) (hρ : 0 < ρ),
      φ ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries (unitaryElt ψ η ξ₁ ξ₂)) ≠ 0 →
        ε ≤ ρ ∧ ρ ≤ R ∧ ‖u‖ ≤ R := by
  have hK : IsCompact (tsupport φ) := hφc
  obtain ⟨R₀, hR₀⟩ := hK.bddAbove_image continuous_frobSq_val.continuousOn
  have hR₁ : 0 ≤ max R₀ 0 := le_max_right R₀ 0
  have hs : 0 < Real.sin θ ^ 2 := by positivity
  have hεsq : 0 < r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r) := by positivity
  refine ⟨Real.sqrt (max R₀ 0 / r) + Real.sqrt (max R₀ 0 / (r * (r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r)))),
    Real.sqrt (r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r)), Real.sqrt_pos.2 hεsq, ?_⟩
  intro ψ η ξ₁ ξ₂ ρ u hρ hne
  have hmem : (unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries (unitaryElt ψ η ξ₁ ξ₂) ∈
      tsupport φ :=
    subset_tsupport φ hne
  have hle : frobSq ((((unitaryElt ψ η ξ₁ ξ₂)⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries (unitaryElt ψ η ξ₁
      ξ₂) :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) ≤ R₀ :=
    hR₀ (Set.mem_image_of_mem _ hmem)
  rw [frobSq_twistedConj] at hle
  obtain ⟨h1, h2, h3⟩ := frobSq_twistedEllipticElt_ge r θ ρ u hr hρ
  have hF : frobSq ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ≤ max R₀ 0 :=
    hle.trans (le_max_left R₀ 0)
  have hεle : r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r) ≤ ρ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h3, hF, sq_nonneg ρ]
  have hερ : Real.sqrt (r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r)) ≤ ρ :=
    calc Real.sqrt (r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r)) ≤ Real.sqrt (ρ ^ 2) := Real.sqrt_le_sqrt hεle
      _ = ρ := Real.sqrt_sq hρ.le
  refine ⟨hερ, ?_, ?_⟩
  · calc ρ = Real.sqrt (ρ ^ 2) := (Real.sqrt_sq hρ.le).symm
      _ ≤ Real.sqrt (max R₀ 0 / r) := Real.sqrt_le_sqrt (by rw [le_div_iff₀ hr]; nlinarith [h1, hF])
      _ ≤ _ := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  · have hu2 : ‖u‖ ^ 2 ≤ max R₀ 0 / (r * (r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r))) := by
      rw [le_div_iff₀ (by positivity), ← Complex.normSq_eq_norm_sq]
      nlinarith [h2, hF, hεle, Complex.normSq_nonneg u, mul_nonneg hr.le (Complex.normSq_nonneg u)]
    calc ‖u‖ ≤ Real.sqrt (max R₀ 0 / (r * (r * Real.sin θ ^ 2 / (max R₀ 0 + 2 * r)))) :=
          (Real.le_sqrt (norm_nonneg u) (by positivity)).2 hu2
      _ ≤ _ := le_add_of_nonneg_left (Real.sqrt_nonneg _)

private theorem continuous_orbitFactor_split (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (a₁ a₂ : ℝ)
    (h : 0 < a₁ ∧ 0 < a₂) :
    Continuous fun q : (ℝ × ℝ × ℝ × ℝ) × ℂ =>
      φ ((unitaryElt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2)⁻¹ * twistedSplitElt a₁ a₂ q.2 h *
        conjEntries (unitaryElt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2)) := by
  refine hφ.comp ?_
  rw [HaarRef.isEmbedding_glVal_complex.continuous_iff]
  have hk : Continuous fun q : (ℝ × ℝ × ℝ × ℝ) × ℂ => ((unitaryElt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 : GL (Fin 2) ℂ)
      : Matrix (Fin 2) (Fin 2) ℂ) :=
    HaarRef.isEmbedding_glVal_complex.continuous.comp (Window.continuous_unitaryElt.comp continuous_fst)
  have hS : Continuous fun q : (ℝ × ℝ × ℝ × ℝ) × ℂ => ((twistedSplitElt a₁ a₂ q.2 h : GL (Fin 2) ℂ) : Matrix (Fin 2)
      (Fin 2) ℂ) := by
    simp only [val_twistedSplitElt]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> fun_prop
  simp only [Function.comp_def, Units.val_mul, val_unitaryElt_inv, val_conjEntries]
  exact (hk.matrix_conjTranspose.matrix_mul hS).matrix_mul (hk.matrix_map Complex.continuous_conj)

private theorem continuousOn_orbitFactor_elliptic (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r θ : ℝ)
    (hr : 0 < r) :
    ContinuousOn (fun q : (ℝ × ℝ × ℝ × ℝ) × ℝ × ℂ =>
      φ ((unitaryElt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2)⁻¹ *
          (if hρ : 0 < q.2.1 then twistedEllipticElt r θ q.2.1 q.2.2 hr hρ else 1) *
        conjEntries (unitaryElt q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2))) {q | 0 < q.2.1} := by
  refine hφ.comp_continuousOn ?_
  rw [HaarRef.isEmbedding_glVal_complex.continuousOn_iff]
  have hk : Continuous fun x : (ℝ × ℝ × ℝ × ℝ) × ℂ × ℝ × ℂ =>
      ((unitaryElt x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    HaarRef.isEmbedding_glVal_complex.continuous.comp (Window.continuous_unitaryElt.comp continuous_fst)
  have hL : Continuous fun x : (ℝ × ℝ × ℝ × ℝ) × ℂ × ℝ × ℂ => ellipticArray r θ x.2.1 x.2.2.1 x.2.2.2 := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [ellipticArray, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> fun_prop
  have hΨ : Continuous fun x : (ℝ × ℝ × ℝ × ℝ) × ℂ × ℝ × ℂ =>
      ((unitaryElt x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose *
        ellipticArray r θ x.2.1 x.2.2.1 x.2.2.2 *
        ((unitaryElt x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd
            ℂ) :=
    (hk.matrix_conjTranspose.matrix_mul hL).matrix_mul (hk.matrix_map Complex.continuous_conj)
  have hinner : ContinuousOn (fun q : (ℝ × ℝ × ℝ × ℝ) × ℝ × ℂ => (q.1, (((q.2.1 : ℝ) : ℂ)⁻¹, q.2.1, q.2.2)))
      {q : (ℝ × ℝ × ℝ × ℝ) × ℝ × ℂ | 0 < q.2.1} := by
    refine continuous_fst.continuousOn.prodMk (ContinuousOn.prodMk ?_ (continuous_snd.continuousOn))
    refine (Complex.continuous_ofReal.comp (continuous_fst.comp continuous_snd)).continuousOn.inv₀ ?_
    intro q hq
    show ((q.2.1 : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < q.2.1 from hq))
  refine (hΨ.comp_continuousOn hinner).congr ?_
  intro q hq
  have hq' : 0 < q.2.1 := hq
  simp only [Function.comp_def, Units.val_mul, val_unitaryElt_inv, val_conjEntries, dif_pos hq',
      val_twistedEllipticElt,
    ellipticArray]

end TwistedOrbit.Proper

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit
namespace TorusSlot

private def bSet : Set ℂ := {b : ℂ | 0 < b.re ∧ 0 < b.im}

private theorem bSet_eq_preimage :
    bSet = Complex.measurableEquivRealProd ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  ext b
  simp only [bSet, Set.mem_setOf_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_prod,
    Set.mem_Ioi]

private theorem integrableOn_bSet_iff_real (F : ℝ × ℝ → ℝ) :
    IntegrableOn (fun b : ℂ => F (b.re, b.im)) bSet ↔ IntegrableOn F (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  rw [bSet_eq_preimage]
  exact Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.measurableEmbedding (f := F)

private theorem setIntegral_bSet_eq_real (F : ℝ × ℝ → ℝ) :
    ∫ b in bSet, F (b.re, b.im) = ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), F q := by
  rw [bSet_eq_preimage]
  exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding F _

private theorem setIntegral_bSet_eq (G : ℝ × ℝ → ℂ) :
    (IntegrableOn (fun b : ℂ => G (b.re, b.im)) bSet ↔ IntegrableOn G (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) ∧
      ∫ b in bSet, G (b.re, b.im) = ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G q := by
  rw [bSet_eq_preimage]
  exact ⟨Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding (f := G),
    Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding G _⟩

private noncomputable def planeMap (a b c d : ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun z := (a * z.1 + b * z.2, c * z.1 + d * z.2)
  map_add' z w := by ext <;> simp <;> ring
  map_smul' t z := by ext <;> simp <;> ring

private theorem
    planeMap_apply (a b c d : ℝ) (z : ℝ × ℝ) : planeMap a b c d z = (a * z.1 + b * z.2, c * z.1 + d * z.2) :=
  rfl

private theorem det_planeMap (a b c d : ℝ) : LinearMap.det (planeMap a b c d) = a * d - b * c := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, planeMap_apply]
  try ring

private def _root_.TwistedOrbit.TorusSlot.shear (q : ℝ × ℝ) : ℝ × ℝ := (q.1 * q.2, q.1)

p2m_export "TwistedOrbit.TorusSlot" "shear"
private theorem shear_apply (q : ℝ × ℝ) : shear q = (q.1 * q.2, q.1) := rfl

private def shearDeriv (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap (planeMap q.2 q.1 1 0)

private theorem det_shearDeriv (q : ℝ × ℝ) : (shearDeriv q).det = -q.1 := by
  rw [shearDeriv, LinearMap.det_toContinuousLinearMap, det_planeMap]
  ring

private theorem hasFDerivAt_shear (q : ℝ × ℝ) : HasFDerivAt shear (shearDeriv q) q := by
  have h : HasFDerivAt (fun p : ℝ × ℝ => (p.1 * p.2, p.1))
      ((q.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + q.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) q :=
    (hasFDerivAt_fst.mul hasFDerivAt_snd).prodMk hasFDerivAt_fst
  refine h.congr_fderiv ?_
  ext z <;> simp [shearDeriv, planeMap_apply] <;> ring

private theorem shear_image :
    shear '' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) = Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
  ext b
  constructor
  · rintro ⟨q, ⟨(hq₁ : 0 < q.1), (hq₂ : 0 < q.2)⟩, rfl⟩
    exact ⟨mul_pos hq₁ hq₂, hq₁⟩
  · rintro ⟨(hb₁ : 0 < b.1), (hb₂ : 0 < b.2)⟩
    have hb₂' : b.2 ≠ 0 := hb₂.ne'
    refine ⟨(b.2, b.1 / b.2), ⟨hb₂, div_pos hb₁ hb₂⟩, ?_⟩
    refine Prod.ext ?_ rfl
    show b.2 * (b.1 / b.2) = b.1
    first
      | (field_simp; done)
      | (field_simp; ring)

private theorem shear_injOn : Set.InjOn shear (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  rintro p ⟨(hp₁ : 0 < p.1), -⟩ q ⟨(hq₁ : 0 < q.1), -⟩ h
  have h₂ : p.1 = q.1 := congrArg Prod.snd h
  have h₁ : p.1 * p.2 = q.1 * q.2 := congrArg Prod.fst h
  rw [h₂] at h₁
  exact Prod.ext h₂ (mul_left_cancel₀ hq₁.ne' h₁)

private theorem setIntegral_scaleShear_eq (G : ℝ × ℝ → ℂ) :
    (IntegrableOn G (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ↔
        IntegrableOn (fun q : ℝ × ℝ => (q.1 : ℂ) * G (q.1 * q.2, q.1)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) ∧
      ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G b =
        ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), (q.1 : ℂ) * G (q.1 * q.2, q.1) := by
  have hs : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hf' : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ),
      HasFDerivWithinAt shear (shearDeriv q) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) q :=
    fun q _ => (hasFDerivAt_shear q).hasFDerivWithinAt
  have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hf' shear_injOn G
  have heq := integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' shear_injOn G
  rw [shear_image] at hiff heq
  have hcongr : Set.EqOn (fun q : ℝ × ℝ => |(shearDeriv q).det| • G (shear q))
      (fun q : ℝ × ℝ => (q.1 : ℂ) * G (q.1 * q.2, q.1)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    rintro q ⟨(hq₁ : 0 < q.1), -⟩
    simp only [det_shearDeriv, abs_neg, abs_of_pos hq₁, shear_apply, Complex.real_smul]
  refine ⟨?_, ?_⟩
  · rw [hiff]
    exact ⟨fun h => h.congr_fun hcongr hs, fun h => h.congr_fun hcongr.symm hs⟩
  · rw [heq]
    exact setIntegral_congr_fun hs hcongr

private theorem abs_mul_inv_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a * b|⁻¹ = (a * b)⁻¹ ∧ |-a * b|⁻¹ = (a * b)⁻¹ ∧ |a * -b|⁻¹ = (a * b)⁻¹ ∧ |-a * -b|⁻¹ = (a * b)⁻¹ := by
  simp [abs_mul, abs_neg, abs_of_pos ha, abs_of_pos hb]

private theorem split_slot (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
          (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ φ w)
    (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (hx : φ (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) ≠ 0) :
    IntegrableOn (fun b : ℂ => (b.re * b.im)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, b.im)) * x)) bSet ∧
    IntegrableOn (fun b : ℂ => (b.re * b.im)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, b.im)) * x)) bSet ∧
    IntegrableOn (fun b : ℂ => (b.re * b.im)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, -b.im)) * x)) bSet ∧
    IntegrableOn (fun b : ℂ => (b.re * b.im)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, -b.im)) * x)) bSet ∧
      ∫ b in bSet, (b.re * b.im)⁻¹ *
          (w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, b.im)) * x) +
            w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, b.im)) * x) +
            w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, -b.im)) * x) +
            w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, -b.im)) * x)) = (cT : ℝ)⁻¹ := by
  obtain ⟨hint, hval⟩ := Transfer.torus_integral_section δ τ cT hcT hτ φ w hw x hx
  have hi : IntegrableOn
      (fun α : ℝ × ℝ => |α.1 * α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt α) * x))
      {α : ℝ × ℝ | α.1 * α.2 ≠ 0} := hint
  have hval' : ∫ α in {α : ℝ × ℝ | α.1 * α.2 ≠ 0},
      |α.1 * α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt α) * x) = (cT : ℝ)⁻¹ := hval
  have hQ : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi

  have r₁ : IntegrableOn
      (fun α : ℝ × ℝ => |α.1 * α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt α) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    refine hi.mono_set ?_
    rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
    exact mul_ne_zero hα₁.ne' hα₂.ne'
  have r₂ : IntegrableOn
      (fun α : ℝ × ℝ => |-α.1 * α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-α.1, α.2)) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    have h := (Coords.measurePreserving_negFst.integrableOn_comp_preimage
      Coords.negFst.measurableEmbedding).2 hi
    refine (h.mono_set ?_).congr_fun ?_ hQ
    · rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Coords.negFst_apply]
      exact mul_ne_zero (neg_ne_zero.2 hα₁.ne') hα₂.ne'
    · intro α _
      simp only [Function.comp_apply, Coords.negFst_apply]
  have r₃ : IntegrableOn
      (fun α : ℝ × ℝ => |α.1 * -α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (α.1, -α.2)) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    have h := (Coords.measurePreserving_negSnd.integrableOn_comp_preimage
      Coords.negSnd.measurableEmbedding).2 hi
    refine (h.mono_set ?_).congr_fun ?_ hQ
    · rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Coords.negSnd_apply]
      exact mul_ne_zero hα₁.ne' (neg_ne_zero.2 hα₂.ne')
    · intro α _
      simp only [Function.comp_apply, Coords.negSnd_apply]
  have r₄ : IntegrableOn
      (fun α : ℝ × ℝ => |-α.1 * -α.2|⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-α.1, -α.2)) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    have h := ((Coords.measurePreserving_negFst.comp Coords.measurePreserving_negSnd).integrableOn_comp_preimage
      (Coords.negFst.measurableEmbedding.comp Coords.negSnd.measurableEmbedding)).2 hi
    refine (h.mono_set ?_).congr_fun ?_ hQ
    · rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply, Coords.negSnd_apply,
        Coords.negFst_apply]
      exact mul_ne_zero (neg_ne_zero.2 hα₁.ne') (neg_ne_zero.2 hα₂.ne')
    · intro α _
      simp only [Function.comp_apply, Coords.negSnd_apply, Coords.negFst_apply]

  have p₁ : IntegrableOn
      (fun α : ℝ × ℝ => (α.1 * α.2)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt α) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    refine r₁.congr_fun ?_ hQ
    rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
    simp only [(abs_mul_inv_of_pos hα₁ hα₂).1]
  have p₂ : IntegrableOn
      (fun α : ℝ × ℝ => (α.1 * α.2)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-α.1, α.2)) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    refine r₂.congr_fun ?_ hQ
    rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
    simp only [(abs_mul_inv_of_pos hα₁ hα₂).2.1]
  have p₃ : IntegrableOn
      (fun α : ℝ × ℝ => (α.1 * α.2)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (α.1, -α.2)) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    refine r₃.congr_fun ?_ hQ
    rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
    simp only [(abs_mul_inv_of_pos hα₁ hα₂).2.2.1]
  have p₄ : IntegrableOn
      (fun α : ℝ × ℝ => (α.1 * α.2)⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-α.1, -α.2)) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    refine r₄.congr_fun ?_ hQ
    rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
    simp only [(abs_mul_inv_of_pos hα₁ hα₂).2.2.2]

  have hsum := Coords.setIntegral_off_axes_eq _ hi
  rw [hval'] at hsum
  refine ⟨(integrableOn_bSet_iff_real _).2 p₁, (integrableOn_bSet_iff_real _).2 p₂,
    (integrableOn_bSet_iff_real _).2 p₃, (integrableOn_bSet_iff_real _).2 p₄, ?_⟩
  refine (setIntegral_bSet_eq_real fun α : ℝ × ℝ => (α.1 * α.2)⁻¹ *
    (w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt α) * x) +
      w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-α.1, α.2)) * x) +
      w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (α.1, -α.2)) * x) +
      w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-α.1, -α.2)) * x))).trans ?_
  rw [hsum]
  refine setIntegral_congr_fun hQ ?_
  rintro α ⟨(hα₁ : 0 < α.1), (hα₂ : 0 < α.2)⟩
  obtain ⟨e₁, e₂, e₃, e₄⟩ := abs_mul_inv_of_pos hα₁ hα₂
  simp only [e₁, e₂, e₃, e₄]
  ring

private theorem elliptic_slot (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ φ w)
    (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (hx : φ (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) ≠ 0) :
    IntegrableOn (fun q : ℝ × ℝ => q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.ellElt q) * x))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ∧
      ∫ ψ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ l in Set.Ioi (0 : ℝ),
          l⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.ellElt (l, ψ)) * x) = (cT : ℝ)⁻¹ := by
  obtain ⟨hint, hval⟩ := Transfer.torus_integral_section_elliptic δ τ cT hcT hτ φ w hw x hx
  have hi : IntegrableOn (fun q : ℝ × ℝ => q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.ellElt q) * x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) := hint
  have hval' : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
      q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.ellElt q) * x) = (cT : ℝ)⁻¹ := hval
  refine ⟨hi, ?_⟩
  have hf : Integrable (fun q : ℝ × ℝ => q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.ellElt q) * x))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioo (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hi
  rw [← hval', Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hf]

end TwistedOrbit.TorusSlot

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit

namespace FibreShift

private theorem exists_rotation_measurableEquiv (u : ℂ) (hu : Complex.normSq u = 1) :
    ∃ e : ℂ ≃ᵐ ℂ, MeasurePreserving e volume volume ∧ ∀ z : ℂ, e z = u * z := by
  let L : ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun v => u * v
      map_add' := fun v w => mul_add u v w
      map_smul' := fun r v => by
        simp only [RingHom.id_apply, Complex.real_smul]
        ring }
  have hL : ∀ v : ℂ, L v = u * v := fun v => rfl
  have hdet : LinearMap.det L = 1 := by
    have hM : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI L = !![u.re, -u.im; u.im, u.re] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, hL] <;> ring
    rw [← LinearMap.det_toMatrix Complex.basisOneI, hM, Matrix.det_fin_two_of]
    rw [Complex.normSq_apply] at hu
    linear_combination hu
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  let e : ℂ ≃ᵐ ℂ := (L.equivOfDetNeZero hdet0).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ v : ℂ, e v = L v := fun v => rfl
  refine ⟨e, ⟨e.measurable, ?_⟩, fun z => by rw [he, hL]⟩
  calc Measure.map e volume = Measure.map L volume := rfl
    _ = volume := by
      rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, hdet]
      simp

private theorem normSq_exp_two_mul (ψ : ℝ) : Complex.normSq (Complex.exp (2 * ψ * Complex.I)) = 1 := by
  have hcast : (2 * (ψ : ℂ) * Complex.I) = ((2 * ψ : ℝ) : ℂ) * Complex.I := by
    first
      | (push_cast; done)
      | (push_cast; ring)
  rw [Complex.normSq_eq_norm_sq, hcast, Complex.norm_exp_ofReal_mul_I]
  norm_num

private theorem integrableOn_univ_prod_singleton (G : ℂ × ℝ → ℂ) (a : ℝ) :
    IntegrableOn G ((Set.univ : Set ℂ) ×ˢ ({a} : Set ℝ)) := by
  have h0 : (volume : Measure (ℂ × ℝ)) ((Set.univ : Set ℂ) ×ˢ ({a} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  rw [IntegrableOn, Measure.restrict_eq_zero.2 h0]
  exact integrable_zero_measure

private theorem integrableOn_window_int (G : ℂ × ℝ → ℂ)
    (hG : IntegrableOn G ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))
    (hper : ∀ z : ℂ, Function.Periodic (fun ξ : ℝ => G (z, ξ)) (2 * Real.pi)) (k : ℤ) :
    IntegrableOn G
      ((Set.univ : Set ℂ) ×ˢ Set.Ioo ((k : ℝ) * (2 * Real.pi)) ((k : ℝ) * (2 * Real.pi) + 2 * Real.pi)) := by
  let S : ℂ × ℝ ≃ᵐ ℂ × ℝ :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℂ) (MeasurableEquiv.addRight ((k : ℝ) * (2 * Real.pi)))
  have hS_apply : ∀ q : ℂ × ℝ, S q = (q.1, q.2 + (k : ℝ) * (2 * Real.pi)) := fun q => rfl
  have hS : MeasurePreserving S volume volume := by
    have h := (MeasurePreserving.id (volume : Measure ℂ)).prod
      (measurePreserving_add_right (volume : Measure ℝ) ((k : ℝ) * (2 * Real.pi)))
    rw [← Measure.volume_eq_prod] at h
    exact h
  have hpre : S ⁻¹' ((Set.univ : Set ℂ) ×ˢ
      Set.Ioo ((k : ℝ) * (2 * Real.pi)) ((k : ℝ) * (2 * Real.pi) + 2 * Real.pi)) =
        (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    ext q
    simp only [Set.mem_preimage, hS_apply, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
  refine (hS.integrableOn_comp_preimage S.measurableEmbedding).1 ?_
  rw [hpre]
  refine hG.congr_fun ?_ (MeasurableSet.univ.prod measurableSet_Ioo)
  intro q _
  show G q = G (S q)
  rw [hS_apply]
  exact ((hper q.1).int_mul k q.2).symm

private theorem integrableOn_window (G : ℂ × ℝ → ℂ)
    (hG : IntegrableOn G ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))
    (hper : ∀ z : ℂ, Function.Periodic (fun ξ : ℝ => G (z, ξ)) (2 * Real.pi)) (ψ : ℝ) :
    IntegrableOn G ((Set.univ : Set ℂ) ×ˢ Set.Ioo ψ (ψ + 2 * Real.pi)) := by
  have h2π : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ⌊ψ / (2 * Real.pi)⌋ = k := ⟨_, rfl⟩
  have hcancel : ψ / (2 * Real.pi) * (2 * Real.pi) = ψ := by
    first
      | rw [div_mul_eq_mul_div, mul_div_assoc, div_self h2π.ne', mul_one]
      | field_simp
  have hk₁ : (k : ℝ) * (2 * Real.pi) ≤ ψ := by
    have h := Int.floor_le (ψ / (2 * Real.pi))
    rw [hk] at h
    have h' : (k : ℝ) * (2 * Real.pi) ≤ ψ / (2 * Real.pi) * (2 * Real.pi) := by gcongr
    rwa [hcancel] at h'
  have hk₂ : ψ < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
    have h := Int.lt_floor_add_one (ψ / (2 * Real.pi))
    rw [hk] at h
    have h' : ψ / (2 * Real.pi) * (2 * Real.pi) < ((k : ℝ) + 1) * (2 * Real.pi) := by gcongr
    rw [hcancel] at h'
    linarith
  have h₁ := integrableOn_window_int G hG hper k
  have h₂ := integrableOn_window_int G hG hper (k + 1)
  have h₃ := integrableOn_univ_prod_singleton G ((k : ℝ) * (2 * Real.pi) + 2 * Real.pi)
  push_cast at h₂
  refine ((h₁.union h₂).union h₃).mono_set ?_
  rw [← Set.prod_union, ← Set.prod_union]
  refine Set.prod_mono subset_rfl ?_
  intro ξ hξ
  rcases hξ with ⟨hξ₁, hξ₂⟩
  simp only [Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
  by_cases hlt : ξ < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi
  · exact Or.inl (Or.inl ⟨by linarith, hlt⟩)
  · by_cases heq : ξ = (k : ℝ) * (2 * Real.pi) + 2 * Real.pi
    · exact Or.inr heq
    · have hξ' := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm heq)
      exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)

private theorem setIntegral_Ioo_comp_add_of_periodic (g : ℝ → ℂ) (hg : Function.Periodic g (2 * Real.pi)) (ψ : ℝ) :
    ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), g (ξ + ψ) = ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), g ξ := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h2π,
    ← intervalIntegral.integral_of_le h2π, intervalIntegral.integral_comp_add_right, zero_add,
    add_comm (2 * Real.pi) ψ]
  simpa using hg.intervalIntegral_add_eq ψ 0

private theorem setIntegral_univ_prod_Ioo (F : ℂ × ℝ → ℂ)
    (hF : IntegrableOn F ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) :
    ∫ q in (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), F q =
      ∫ z : ℂ, ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), F (z, ξ) := by
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [setIntegral_prod _ hF, Measure.restrict_univ]

private theorem integral_turn_advance (ψ : ℝ) (G : ℂ × ℝ → ℂ)
    (hG : IntegrableOn G ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))
    (hper : ∀ z : ℂ, Function.Periodic (fun ξ : ℝ => G (z, ξ)) (2 * Real.pi)) :
    IntegrableOn (fun q : ℂ × ℝ => G (Complex.exp (2 * ψ * Complex.I) * q.1, q.2 + ψ))
        ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ∧
      ∫ q in (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
          G (Complex.exp (2 * ψ * Complex.I) * q.1, q.2 + ψ) =
        ∫ q in (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), G q := by
  obtain ⟨rot, hrotP, hrot⟩ := exists_rotation_measurableEquiv _ (normSq_exp_two_mul ψ)
  have hW := integrableOn_window G hG hper ψ
  let T : ℂ × ℝ ≃ᵐ ℂ × ℝ := MeasurableEquiv.prodCongr rot (MeasurableEquiv.addRight ψ)
  have hT_apply : ∀ q : ℂ × ℝ, T q = (rot q.1, q.2 + ψ) := fun q => rfl
  have hT : MeasurePreserving T volume volume := by
    have h := hrotP.prod (measurePreserving_add_right (volume : Measure ℝ) ψ)
    rw [← Measure.volume_eq_prod] at h
    exact h
  have hpre : T ⁻¹' ((Set.univ : Set ℂ) ×ˢ Set.Ioo ψ (ψ + 2 * Real.pi)) =
      (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    ext q
    simp only [Set.mem_preimage, hT_apply, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
  have hA : MeasurableSet ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have h₁ : IntegrableOn (fun q : ℂ × ℝ => G (Complex.exp (2 * ψ * Complex.I) * q.1, q.2 + ψ))
      ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
    have h := (hT.integrableOn_comp_preimage T.measurableEmbedding).2 hW
    rw [hpre] at h
    refine h.congr_fun ?_ hA
    intro q _
    simp only [Function.comp_apply, hT_apply, hrot]
  refine ⟨h₁, ?_⟩
  rw [setIntegral_univ_prod_Ioo _ h₁, setIntegral_univ_prod_Ioo _ hG]
  show ∫ z : ℂ, ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), G (Complex.exp (2 * ψ * Complex.I) * z, ξ + ψ) =
    ∫ z : ℂ, ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), G (z, ξ)
  have hinner : ∀ z : ℂ, ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), G (Complex.exp (2 * ψ * Complex.I) * z, ξ + ψ) =
      ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), G (Complex.exp (2 * ψ * Complex.I) * z, ξ) :=
    fun z => setIntegral_Ioo_comp_add_of_periodic _ (hper (Complex.exp (2 * ψ * Complex.I) * z)) ψ
  simp_rw [hinner]
  have h := hrotP.integral_comp rot.measurableEmbedding
    (fun z : ℂ => ∫ ξ in Set.Ioo (0 : ℝ) (2 * Real.pi), G (z, ξ))
  simp only [hrot] at h
  exact h

end FibreShift

end TwistedOrbit

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit

namespace Orbit

private theorem conjEntries_mul (g h : GL (Fin 2) ℂ) : conjEntries (g * h) = conjEntries g * conjEntries h :=
  map_mul (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) g h

private theorem conjEntries_inv (g : GL (Fin 2) ℂ) : conjEntries g⁻¹ = (conjEntries g)⁻¹ :=
  map_inv (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) g

private theorem conjEntries_one : conjEntries (1 : GL (Fin 2) ℂ) = 1 :=
  map_one (Matrix.GeneralLinearGroup.map (starRingEnd ℂ))

private theorem conjEntries_apply (g : GL (Fin 2) ℂ) (i j : Fin 2) :
    (conjEntries g : Matrix (Fin 2) (Fin 2) ℂ) i j = (starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  rfl

private theorem conjEntries_conjEntries (g : GL (Fin 2) ℂ) : conjEntries (conjEntries g) = g :=
  Matrix.GeneralLinearGroup.ext fun i j => by rw [conjEntries_apply, conjEntries_apply, Complex.conj_conj]

private theorem diag_mul_conj_unipotent_eq (s₁ s₂ v vc : ℂ) :
    !![s₁, 0; 0, s₂] * !![1, vc; 0, 1] = !![1, v; 0, 1] * !![s₁, s₁ * vc - s₂ * v; 0, s₂] := by
  have h00 : s₁ * 1 + 0 * 0 = 1 * s₁ + v * 0 := by ring
  have h01 : s₁ * vc + 0 * 1 = 1 * (s₁ * vc - s₂ * v) + v * s₂ := by ring
  have h10 : 0 * 1 + s₂ * 0 = 0 * s₁ + 1 * 0 := by ring
  have h11 : 0 * vc + s₂ * 1 = 0 * (s₁ * vc - s₂ * v) + 1 * s₂ := by ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem antidiag_mul_conj_shear_eq (sr Ep Em ρ ρi u uc N : ℂ) (h : ρ * ρi = 1) (hN : N = uc * u) :
    !![0, sr * Ep; sr * Em, 0] * !![ρ, ρ * uc; 0, 1] =
      !![ρ, ρ * u; 0, 1] *
        !![sr * -(u * ρ * Em), sr * (ρi * Ep - N * ρ * Em); sr * (ρ * Em), sr * (uc * ρ * Em)] := by
  have h00 : 0 * ρ + sr * Ep * 0 = ρ * (sr * -(u * ρ * Em)) + ρ * u * (sr * (ρ * Em)) := by ring
  have h01 : 0 * (ρ * uc) + sr * Ep * 1 =
      ρ * (sr * (ρi * Ep - N * ρ * Em)) + ρ * u * (sr * (uc * ρ * Em)) := by
    linear_combination (-(sr * Ep)) * h + (sr * ρ ^ 2 * Em) * hN
  have h10 : sr * Em * ρ + 0 * 0 = 0 * (sr * -(u * ρ * Em)) + 1 * (sr * (ρ * Em)) := by ring
  have h11 : sr * Em * (ρ * uc) + 0 * 1 = 0 * (sr * (ρi * Ep - N * ρ * Em)) + 1 * (sr * (uc * ρ * Em)) := by
    ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem rot_mul_conj_cayley_eq (X Y Z P M J : ℂ) (hZ : Z = -Y) (hP : P = X + Y * J) (hM : M = X - Y * J)
    (hJ : J * J = -1) :
    !![X, Y; Z, X] * !![1, 1; -J, J] = !![1, 1; J, -J] * !![0, P; M, 0] := by
  have h00 : X * 1 + Y * -J = 1 * 0 + 1 * M := by linear_combination (-1 : ℂ) * hM
  have h01 : X * 1 + Y * J = 1 * P + 1 * 0 := by linear_combination (-1 : ℂ) * hP
  have h10 : Z * 1 + X * -J = J * 0 + -J * M := by linear_combination hZ + J * hM + (-Y) * hJ
  have h11 : Z * 1 + X * J = J * P + -J * 0 := by linear_combination hZ + (-J) * hP + (-Y) * hJ
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem rot_mul_conj_cayley_neg_eq (X Y Z P M J : ℂ) (hZ : Z = -Y) (hP : P = X + Y * J) (hM : M = X - Y * J)
    (hJ : J * J = -1) :
    !![X, Y; Z, X] * !![1, 1; J, -J] = !![1, 1; -J, J] * !![0, M; P, 0] := by
  have h00 : X * 1 + Y * J = 1 * 0 + 1 * P := by linear_combination (-1 : ℂ) * hP
  have h01 : X * 1 + Y * -J = 1 * M + 1 * 0 := by linear_combination (-1 : ℂ) * hM
  have h10 : Z * 1 + X * J = -J * 0 + J * P := by linear_combination hZ + (-J) * hP + (-Y) * hJ
  have h11 : Z * 1 + X * -J = -J * M + J * 0 := by linear_combination hZ + J * hM + (-Y) * hJ
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem torus_mul_cayley_eq (p q e J : ℂ) (he : e * e = 1) (hJ : J * J = -1) :
    !![p, q; -q, p] * !![1, 1; e * J, -(e * J)] =
      !![1, 1; e * J, -(e * J)] * !![p + e * q * J, 0; 0, p - e * q * J] := by
  have h00 : p * 1 + q * (e * J) = 1 * (p + e * q * J) + 1 * 0 := by ring
  have h01 : p * 1 + q * -(e * J) = 1 * 0 + 1 * (p - e * q * J) := by ring
  have h10 : -q * 1 + p * (e * J) = e * J * (p + e * q * J) + -(e * J) * 0 := by
    linear_combination q * he + (-(e * e * q)) * hJ
  have h11 : -q * 1 + p * -(e * J) = e * J * 0 + -(e * J) * (p - e * q * J) := by
    linear_combination q * he + (-(e * e * q)) * hJ
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem diag_mul_shear_eq (w₁ w₂ ρ u : ℂ) :
    !![w₁, 0; 0, w₂] * !![ρ, ρ * (w₂ * u); 0, 1] = !![ρ, ρ * (w₁ * u); 0, 1] * !![w₁, 0; 0, w₂] := by
  have h00 : w₁ * ρ + 0 * 0 = ρ * w₁ + ρ * (w₁ * u) * 0 := by ring
  have h01 : w₁ * (ρ * (w₂ * u)) + 0 * 1 = ρ * 0 + ρ * (w₁ * u) * w₂ := by ring
  have h10 : 0 * ρ + w₂ * 0 = 0 * w₁ + 1 * 0 := by ring
  have h11 : 0 * (ρ * (w₂ * u)) + w₂ * 1 = 0 * 0 + 1 * w₂ := by ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private def unipotent (v : ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, v; 0, 1] (by simp [Matrix.det_fin_two_of])

private def shear (ρ : ℝ) (u : ℂ) (hρ : 0 < ρ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ρ : ℂ), (ρ : ℂ) * u; 0, 1]
    (by
      rw [Matrix.det_fin_two_of]
      have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
      simpa using hρ')

private def antidiag (r α : ℝ) (hr : 0 < r) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![0, (Real.sqrt r : ℂ) * Complex.exp (α / 2 * Complex.I);
      (Real.sqrt r : ℂ) * Complex.exp (-(α / 2 * Complex.I)), 0]
    (by
      rw [Matrix.det_fin_two_of]
      have hE : Complex.exp (α / 2 * Complex.I) * Complex.exp (-(α / 2 * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast Real.sq_sqrt hr.le
      have key : (0 : ℂ) * 0 - (Real.sqrt r : ℂ) * Complex.exp (α / 2 * Complex.I) *
          ((Real.sqrt r : ℂ) * Complex.exp (-(α / 2 * Complex.I))) = -(r : ℂ) := by
        linear_combination (-(Real.sqrt r : ℂ) ^ 2) * hE - hs
      rw [key]
      exact neg_ne_zero.mpr (by exact_mod_cast hr.ne'))

private def cayley (ε : ℝ) (hε : ε ≠ 0) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; (ε : ℂ) * Complex.I, -((ε : ℂ) * Complex.I)]
    (by
      rw [Matrix.det_fin_two_of]
      have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
      have key : (1 : ℂ) * -((ε : ℂ) * Complex.I) - 1 * ((ε : ℂ) * Complex.I) = -(2 * (ε : ℂ) * Complex.I) := by
        ring
      rw [key]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hε') Complex.I_ne_zero))

private theorem coe_unipotent (v : ℂ) : ((unipotent v : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, v; 0, 1] :=
  rfl

private theorem coe_shear (ρ : ℝ) (u : ℂ) (hρ : 0 < ρ) :
    ((shear ρ u hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![(ρ : ℂ), (ρ : ℂ) * u; 0, 1] :=
  rfl

private theorem coe_antidiag (r α : ℝ) (hr : 0 < r) :
    ((antidiag r α hr : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![0, (Real.sqrt r : ℂ) * Complex.exp (α / 2 * Complex.I);
        (Real.sqrt r : ℂ) * Complex.exp (-(α / 2 * Complex.I)), 0] :=
  rfl

private theorem coe_cayley (ε : ℝ) (hε : ε ≠ 0) :
    ((cayley ε hε : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, 1; (ε : ℂ) * Complex.I, -((ε : ℂ) * Complex.I)] :=
  rfl

private theorem coe_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] :=
  rfl

private theorem coe_twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    ((twistedEllipticElt r θ ρ u hr hρ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))),
          (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
            (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)));
        (Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I))),
          (Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))] :=
  rfl

private theorem coe_antidiag_neg (r θ : ℝ) (hr : 0 < r) :
    ((antidiag r (-θ) hr : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![0, (Real.sqrt r : ℂ) * Complex.exp (-(θ / 2 * Complex.I));
        (Real.sqrt r : ℂ) * Complex.exp (θ / 2 * Complex.I), 0] := by
  have h1 : -(((-θ : ℝ) : ℂ) / 2 * Complex.I) = θ / 2 * Complex.I := by push_cast; ring
  have h2 : ((-θ : ℝ) : ℂ) / 2 * Complex.I = -(θ / 2 * Complex.I) := by push_cast; ring
  rw [coe_antidiag, h1, h2]

private theorem coe_conj_unipotent (v : ℂ) :
    ((conjEntries (unipotent v) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, (starRingEnd ℂ) v; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjEntries_apply, coe_unipotent]

private theorem coe_conj_shear (ρ : ℝ) (u : ℂ) (hρ : 0 < ρ) :
    ((conjEntries (shear ρ u hρ) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(ρ : ℂ), (ρ : ℂ) * (starRingEnd ℂ) u; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjEntries_apply, coe_shear]

private theorem inv_unipotent_mul_mul_conj (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (v : ℂ) (δ : GL (Fin 2) ℂ)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) ℂ) = !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)]) :
    (unipotent v)⁻¹ * δ * conjEntries (unipotent v) =
      twistedSplitElt a₁ a₂ ((Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) v - (Real.sqrt a₂ : ℂ) * v) h := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hδ, coe_conj_unipotent, coe_unipotent, coe_twistedSplitElt]
  exact diag_mul_conj_unipotent_eq _ _ _ _

private theorem inv_shear_mul_antidiag_mul_conj (r α ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) :
    (shear ρ u hρ)⁻¹ * antidiag r α hr * conjEntries (shear ρ u hρ) = twistedEllipticElt r α ρ u hr hρ := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_antidiag, coe_conj_shear, coe_shear, coe_twistedEllipticElt]
  exact antidiag_mul_conj_shear_eq (Real.sqrt r) (Complex.exp (α / 2 * Complex.I))
    (Complex.exp (-(α / 2 * Complex.I))) ρ (ρ : ℂ)⁻¹ u ((starRingEnd ℂ) u) (Complex.normSq u)
    (mul_inv_cancel₀ hρ') Complex.normSq_eq_conj_mul_self

private theorem inv_mul_rot_mul_conj_of_cayley (r θ : ℝ) (hr : 0 < r) (c δ : GL (Fin 2) ℂ)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; Complex.I, -Complex.I])
    (hδ : (δ : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
        ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)]) :
    c⁻¹ * δ * conjEntries c = antidiag r θ hr := by
  have hcc : ((conjEntries c : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; -Complex.I, Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjEntries_apply, hc]
  have hP : (Real.sqrt r : ℂ) * Complex.exp (θ / 2 * Complex.I) =
      ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ) + ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    ring
  have hM : (Real.sqrt r : ℂ) * Complex.exp (-(θ / 2 * Complex.I)) =
      ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ) - ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hδ, hcc, hc, coe_antidiag]
  exact rot_mul_conj_cayley_eq _ _ _ _ _ Complex.I (Complex.ofReal_neg _) hP hM Complex.I_mul_I

private theorem inv_mul_rot_mul_conj_of_cayley_neg (r θ : ℝ) (hr : 0 < r) (c δ : GL (Fin 2) ℂ)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; -Complex.I, Complex.I])
    (hδ : (δ : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
        ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)]) :
    c⁻¹ * δ * conjEntries c = antidiag r (-θ) hr := by
  have hcc : ((conjEntries c : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; Complex.I, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjEntries_apply, hc]
  have hP : (Real.sqrt r : ℂ) * Complex.exp (θ / 2 * Complex.I) =
      ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ) + ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    ring
  have hM : (Real.sqrt r : ℂ) * Complex.exp (-(θ / 2 * Complex.I)) =
      ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ) - ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hδ, hcc, hc, coe_antidiag_neg]
  exact rot_mul_conj_cayley_neg_eq _ _ _ _ _ Complex.I (Complex.ofReal_neg _) hP hM Complex.I_mul_I

private theorem torus_mul_cayley (p q ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c t : GL (Fin 2) ℂ)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; (ε : ℂ) * Complex.I, -((ε : ℂ) * Complex.I)])
    (ht : (t : Matrix (Fin 2) (Fin 2) ℂ) = !![(p : ℂ), (q : ℂ); -(q : ℂ), (p : ℂ)]) :
    (t : Matrix (Fin 2) (Fin 2) ℂ) * c =
      c * !![(p : ℂ) + (ε : ℂ) * (q : ℂ) * Complex.I, 0; 0, (p : ℂ) - (ε : ℂ) * (q : ℂ) * Complex.I] := by
  have he : (ε : ℂ) * (ε : ℂ) = 1 := by
    rcases hε with h | h <;> simp [h]
  rw [ht, hc]
  exact torus_mul_cayley_eq (p : ℂ) (q : ℂ) (ε : ℂ) Complex.I he Complex.I_mul_I

private theorem coe_inv_cayley_mul_torus_mul_cayley (p q ε : ℝ) (hε : ε = 1 ∨ ε = -1) (c t : GL (Fin 2) ℂ)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; (ε : ℂ) * Complex.I, -((ε : ℂ) * Complex.I)])
    (ht : (t : Matrix (Fin 2) (Fin 2) ℂ) = !![(p : ℂ), (q : ℂ); -(q : ℂ), (p : ℂ)]) :
    ((c⁻¹ * t * c : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(p : ℂ) + (ε : ℂ) * (q : ℂ) * Complex.I, 0; 0, (p : ℂ) - (ε : ℂ) * (q : ℂ) * Complex.I] := by
  rw [Units.val_mul, Units.val_mul, mul_assoc, torus_mul_cayley p q ε hε c t hc ht, ← mul_assoc, Units.inv_mul,
    one_mul]

private theorem diag_mul_shear (w₁ w₂ : ℂ) (d : GL (Fin 2) ℂ) (hd : (d : Matrix (Fin 2) (Fin 2) ℂ) = !![w₁, 0; 0, w₂])
    (ρ : ℝ) (u : ℂ) (hρ : 0 < ρ) :
    d * shear ρ (w₂ * u) hρ = shear ρ (w₁ * u) hρ * d := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hd, coe_shear, coe_shear]
  exact diag_mul_shear_eq w₁ w₂ ρ u

end Orbit

namespace Substitution

private theorem exists_twistShear_linearMap (a₁ a₂ : ℝ) :
    ∃ L : ℂ →ₗ[ℝ] ℂ, ∀ v, L v = (Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) v - (Real.sqrt a₂ : ℂ) * v :=
  ⟨Real.sqrt a₁ • Complex.conjAe.toLinearMap - Real.sqrt a₂ • LinearMap.id, fun v => by simp⟩

private theorem det_twistShear (a₁ a₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) (L : ℂ →ₗ[ℝ] ℂ)
    (hL : ∀ v, L v = (Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) v - (Real.sqrt a₂ : ℂ) * v) :
    LinearMap.det L = a₂ - a₁ := by
  have hM : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI L =
      !![Real.sqrt a₁ - Real.sqrt a₂, 0; 0, -Real.sqrt a₁ - Real.sqrt a₂] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, hL] <;> ring
  rw [← LinearMap.det_toMatrix Complex.basisOneI, hM, Matrix.det_fin_two_of]
  linear_combination Real.sq_sqrt h₂.le - Real.sq_sqrt h₁.le

private theorem integral_comp_twistShear (a₁ a₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) (hne : a₁ ≠ a₂) (F : ℂ → ℂ) :
    ∫ v : ℂ, F ((Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) v - (Real.sqrt a₂ : ℂ) * v) =
      (|a₁ - a₂|⁻¹ : ℝ) • ∫ w : ℂ, F w := by
  obtain ⟨L, hL⟩ := exists_twistShear_linearMap a₁ a₂
  have hdet : LinearMap.det L = a₂ - a₁ := det_twistShear a₁ a₂ h₁ h₂ L hL
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]
    exact sub_ne_zero.2 (Ne.symm hne)
  let e : ℂ ≃ᵐ ℂ := (L.equivOfDetNeZero hdet0).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ v, e v = L v := fun v => rfl
  calc ∫ v : ℂ, F ((Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) v - (Real.sqrt a₂ : ℂ) * v)
      = ∫ v : ℂ, F (e v) := by simp_rw [he, hL]
    _ = ∫ w : ℂ, F w ∂(Measure.map e volume) := (integral_map_equiv e F).symm
    _ = ∫ w : ℂ, F w ∂(Measure.map L volume) := rfl
    _ = (|a₁ - a₂|⁻¹ : ℝ) • ∫ w : ℂ, F w := by
      rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, integral_smul_measure,
        ENNReal.toReal_ofReal (abs_nonneg _), hdet, abs_inv, abs_sub_comm]

private theorem integrable_comp_twistShear_iff (a₁ a₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) (hne : a₁ ≠ a₂) (F : ℂ → ℂ) :
    Integrable (fun v : ℂ => F ((Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) v - (Real.sqrt a₂ : ℂ) * v)) ↔
      Integrable F := by
  obtain ⟨L, hL⟩ := exists_twistShear_linearMap a₁ a₂
  have hdet : LinearMap.det L = a₂ - a₁ := det_twistShear a₁ a₂ h₁ h₂ L hL
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]
    exact sub_ne_zero.2 (Ne.symm hne)
  let e : ℂ ≃ᵐ ℂ := (L.equivOfDetNeZero hdet0).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have key : Integrable F (Measure.map L volume) ↔ Integrable F volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0]
    exact integrable_smul_measure (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet0))).ne'
      ENNReal.ofReal_ne_top
  have key' : Integrable (F ∘ e) volume ↔ Integrable F volume := (integrable_map_equiv e F).symm.trans key
  simp_rw [← hL]
  exact key'

end Substitution

end TwistedOrbit

end

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit
namespace SplitCore

private def ksDom : Set (Fin 2 → Fin 2 → ℂ) :=
  {p : Fin 2 → Fin 2 → ℂ |
    0 < (p 1 0).re ∧ 0 < (p 1 0).im ∧
    0 < (p 0 0).re ∧ (p 0 0).re < Real.pi ∧ 0 < (p 0 0).im ∧ (p 0 0).im < Real.pi / 2 ∧
    0 < (p 0 1).re ∧ (p 0 1).re < 2 * Real.pi ∧ 0 < (p 0 1).im ∧ (p 0 1).im < 2 * Real.pi}

private def ksJ (p : Fin 2 → Fin 2 → ℂ) : ENNReal :=
  ENNReal.ofReal (2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im)

private def ksChart (p : Fin 2 → Fin 2 → ℂ) : Fin 2 → Fin 2 → ℂ :=
  Matrix.of.symm
    (((if h : 0 < (p 1 0).re ∧ 0 < (p 1 0).im then
          twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
            unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im
        else 1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))

private def ksLocus : Set (Fin 2 → Fin 2 → ℂ) := {m : Fin 2 → Fin 2 → ℂ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0}

private def aSet : Set (ℂ × ℂ) :=
  {α : ℂ × ℂ | 0 < α.1.re ∧ α.1.re < Real.pi ∧ 0 < α.1.im ∧ α.1.im < Real.pi / 2 ∧
    0 < α.2.re ∧ α.2.re < 2 * Real.pi ∧ 0 < α.2.im ∧ α.2.im < 2 * Real.pi}

private def kU (α : ℂ × ℂ) : GL (Fin 2) ℂ := unitaryElt α.1.re α.1.im α.2.re α.2.im

private def secY (α : ℂ × ℂ) (z : ℂ) : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) :=
  HaarRef.glOfℂ (Matrix.of.symm ((Orbit.unipotent z * kU α : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))

private def torA (b : ℝ × ℝ) : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) := toTensorGL ℝ ℂ ℝ (Transfer.diagElt b)

private def secF (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (α : ℂ × ℂ) (z : ℂ) : ℂ :=
  φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ ((Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) z - (Real.sqrt a₂ : ℂ) * z) h *
    conjEntries (kU α))

private theorem ridGL_glOfℂ_symm_coe (g : GL (Fin 2) ℂ) :
    TwistedTorus.Rid.ridGL (HaarRef.glOfℂ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ))) = g := by
  have hA : (Matrix.of (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [HaarRef.ridGL_glOfℂ _ hA]
  apply Units.ext
  exact Equiv.apply_symm_apply Matrix.of _

private theorem ridGL_secY (α : ℂ × ℂ) (z : ℂ) : TwistedTorus.Rid.ridGL (secY α z) = Orbit.unipotent z * kU α :=
  ridGL_glOfℂ_symm_coe _

private theorem coe_ridGL_torA (b : ℝ × ℝ) (hb : b.1 * b.2 ≠ 0) :
    ((TwistedTorus.Rid.ridGL (torA b) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(b.1 : ℂ), 0; 0, (b.2 : ℂ)] := by
  unfold torA
  rw [Transfer.diagElt_apply_of_ne b hb, TwistedTorus.Rid.ridGL_toTensorGL]
  have hγ : ((upperTriangular b.1 b.2 0 hb : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![b.1, 0; 0, b.2] := rfl
  rw [hγ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem glOfℂ_ksChart {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ ksDom) :
    HaarRef.glOfℂ (ksChart p) = torA ((p 1 0).re, (p 1 0).im) * secY (p 0 0, p 0 1) (p 1 1) := by
  simp only [ksDom, Set.mem_setOf_eq] at hp
  obtain ⟨hb₁, hb₂, -⟩ := hp
  have hb : ((p 1 0).re, (p 1 0).im).1 * ((p 1 0).re, (p 1 0).im).2 ≠ 0 := mul_ne_zero hb₁.ne' hb₂.ne'
  apply TwistedTorus.Rid.injective_ridGL
  rw [map_mul, ridGL_secY]
  have hc : ksChart p = Matrix.of.symm ((twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1)
      ⟨pow_pos hb₁ 2, pow_pos hb₂ 2⟩ * unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold ksChart
    rw [dif_pos ⟨hb₁, hb₂⟩]
  rw [hc, ridGL_glOfℂ_symm_coe, ← mul_assoc]
  have hk : unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im = kU (p 0 0, p 0 1) := rfl
  rw [hk]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Orbit.coe_twistedSplitElt, coe_ridGL_torA _ hb, Orbit.coe_unipotent, Real.sqrt_sq hb₁.le,
    Real.sqrt_sq hb₂.le]
  have h00 : ((p 1 0).re : ℂ) = ((p 1 0).re : ℂ) * 1 + 0 * 0 := by ring
  have h01 : ((p 1 0).re : ℂ) * p 1 1 = ((p 1 0).re : ℂ) * p 1 1 + 0 * 1 := by ring
  have h10 : (0 : ℂ) = 0 * 1 + ((p 1 0).im : ℂ) * 0 := by ring
  have h11 : ((p 1 0).im : ℂ) = 0 * p 1 1 + ((p 1 0).im : ℂ) * 1 := by ring
  rw [Matrix.mul_fin_two, ← h00, ← h01, ← h10, ← h11]

private theorem torA_mem (a₁ a₂ : ℝ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (b : ℝ × ℝ) : torA b ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ := by
  by_cases hb : b.1 * b.2 = 0
  · have h1 : Transfer.diagElt b = 1 := by
      unfold Transfer.diagElt
      rw [dif_neg (not_not.2 hb)]
    rw [torA, h1, map_one]
    exact Subgroup.one_mem _
  · rw [TwistedTorus.Rid.mem_twistedCentralizer_iff_ridGL, coe_ridGL_torA b hb, hδ]
    have hm : (!![(b.1 : ℂ), 0; 0, (b.2 : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) =
        !![(b.1 : ℂ), 0; 0, (b.2 : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Complex.conj_ofReal]
    rw [hm]
    have h00 : (b.1 : ℂ) * ((Real.sqrt a₁ : ℝ) : ℂ) + 0 * 0 = ((Real.sqrt a₁ : ℝ) : ℂ) * (b.1 : ℂ) + 0 * 0 := by ring
    have h01 : (b.1 : ℂ) * 0 + 0 * ((Real.sqrt a₂ : ℝ) : ℂ) = ((Real.sqrt a₁ : ℝ) : ℂ) * 0 + 0 * (b.2 : ℂ) := by ring
    have h10 : 0 * ((Real.sqrt a₁ : ℝ) : ℂ) + (b.2 : ℂ) * 0 = 0 * (b.1 : ℂ) + ((Real.sqrt a₂ : ℝ) : ℂ) * 0 := by ring
    have h11 : (0 : ℂ) * 0 + (b.2 : ℂ) * ((Real.sqrt a₂ : ℝ) : ℂ) = 0 * 0 + ((Real.sqrt a₂ : ℝ) : ℂ) * (b.2 : ℂ) := by
      ring
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem orbitFactor_torA_mul (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (b : ℝ × ℝ) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    φ (TwistedTorus.Rid.ridGL ((torA b * x)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (torA b * x))) =
      φ (TwistedTorus.Rid.ridGL (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x)) := by
  have ht : torA b = ((⟨torA b, torA_mem a₁ a₂ δ hδ b⟩ : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :
      GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := rfl
  rw [ht, Transfer.orbit_mul_left]

private theorem orbitFactor_secY (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (α : ℂ × ℂ) (z : ℂ) :
    φ (TwistedTorus.Rid.ridGL ((secY α z)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (secY α z))) = secF φ a₁ a₂ h α z := by
  have hσ : TwistedTorus.Rid.ridGL (sigmaGL ℝ ℂ ℝ Complex.conjAe (secY α z)) =
      conjEntries (TwistedTorus.Rid.ridGL (secY α z)) :=
    Units.ext (TwistedTorus.Rid.ridGL_sigmaGL _)
  unfold secF
  rw [← Orbit.inv_unipotent_mul_mul_conj a₁ a₂ h z (TwistedTorus.Rid.ridGL δ) hδ, map_mul, map_mul, map_inv, hσ,
    ridGL_secY, Orbit.conjEntries_mul, mul_inv_rev]
  simp only [mul_assoc]

private theorem torA_sign_mul (ε₁ ε₂ : ℝ) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (b : ℝ × ℝ)
    (hb : b.1 * b.2 ≠ 0) : torA (ε₁, ε₂) * torA b = torA (ε₁ * b.1, ε₂ * b.2) := by
  have hε0 : ε₁ * ε₂ ≠ 0 := by
    rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> norm_num
  have heb : ε₁ * b.1 * (ε₂ * b.2) ≠ 0 := by
    have hr : ε₁ * b.1 * (ε₂ * b.2) = (ε₁ * ε₂) * (b.1 * b.2) := by ring
    rw [hr]
    exact mul_ne_zero hε0 hb
  have hu : ∀ (x y : ℝ) (hxy : x * y ≠ 0),
      ((upperTriangular x y 0 hxy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![x, 0; 0, y] := fun x y hxy => rfl
  unfold torA
  rw [← map_mul, Transfer.diagElt_apply_of_ne (ε₁, ε₂) hε0, Transfer.diagElt_apply_of_ne b hb,
    Transfer.diagElt_apply_of_ne (ε₁ * b.1, ε₂ * b.2) heb]
  congr 1
  apply Units.ext
  rw [Units.val_mul, hu, hu, hu]
  have h00 : ε₁ * b.1 + 0 * 0 = ε₁ * b.1 := by ring
  have h01 : ε₁ * 0 + 0 * b.2 = 0 := by ring
  have h10 : 0 * b.1 + ε₂ * 0 = 0 := by ring
  have h11 : 0 * 0 + ε₂ * b.2 = ε₂ * b.2 := by ring
  rw [Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem densℂ_ksChart {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ ksDom) :
    (HaarRef.densℂ (ksChart p)).toReal = ((((p 1 0).re * (p 1 0).im) ^ 2) ^ 2)⁻¹ := by
  simp only [ksDom, Set.mem_setOf_eq] at hp
  obtain ⟨hb₁, hb₂, -⟩ := hp
  have hc : ksChart p = Matrix.of.symm ((twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1)
      ⟨pow_pos hb₁ 2, pow_pos hb₂ 2⟩ * unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold ksChart
    rw [dif_pos ⟨hb₁, hb₂⟩]
  have hE : Complex.normSq (Complex.exp (((p 0 0).re : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hD : Complex.normSq (((Real.sqrt ((p 1 0).re ^ 2) : ℝ) : ℂ) * ((Real.sqrt ((p 1 0).im ^ 2) : ℝ) : ℂ) -
      ((p 1 0).re : ℂ) * p 1 1 * 0) = ((p 1 0).re * (p 1 0).im) ^ 2 := by
    rw [Real.sqrt_sq hb₁.le, Real.sqrt_sq hb₂.le, mul_zero, sub_zero, ← Complex.ofReal_mul, Complex.normSq_ofReal,
      ← sq]
  unfold HaarRef.densℂ
  rw [hc, Equiv.apply_symm_apply, Units.val_mul, Matrix.det_mul, Orbit.coe_twistedSplitElt, Matrix.det_fin_two_of,
    Window.det_coe_unitaryElt, map_mul, map_pow, hE, one_pow, mul_one, hD,
    ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg _))]

private theorem ksJ_toReal {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ ksDom) :
    (ksJ p).toReal = 2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im := by
  simp only [ksDom, Set.mem_setOf_eq] at hp
  obtain ⟨hb₁, hb₂, -, -, hη0, hηlt, -⟩ := hp
  have hsin : 0 < Real.sin (p 0 0).im := Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (p 0 0).im := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hηlt⟩
  exact ENNReal.toReal_ofReal
    (mul_pos (mul_pos (mul_pos (mul_pos two_pos (pow_pos hb₁ 3)) (pow_pos hb₂ 3)) hsin) hcos).le

private theorem measurable_ksJ : Measurable ksJ := by
  have hc : ∀ i j : Fin 2, Continuous fun p : Fin 2 → Fin 2 → ℂ => p i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have h10r : Continuous fun p : Fin 2 → Fin 2 → ℂ => (p 1 0).re := Complex.continuous_re.comp (hc 1 0)
  have h10i : Continuous fun p : Fin 2 → Fin 2 → ℂ => (p 1 0).im := Complex.continuous_im.comp (hc 1 0)
  have h00i : Continuous fun p : Fin 2 → Fin 2 → ℂ => (p 0 0).im := Complex.continuous_im.comp (hc 0 0)
  unfold ksJ
  exact ENNReal.measurable_ofReal.comp
    (((((continuous_const.mul (h10r.pow 3)).mul (h10i.pow 3)).mul (Real.continuous_sin.comp h00i)).mul
      (Real.continuous_cos.comp h00i)).measurable)

private theorem ksJ_lt_top (p : Fin 2 → Fin 2 → ℂ) : ksJ p < ⊤ := ENNReal.ofReal_lt_top

private theorem measurableSet_ksDom : MeasurableSet ksDom := by
  have hc : ∀ i j : Fin 2, Continuous fun p : Fin 2 → Fin 2 → ℂ => p i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have hre : ∀ i j : Fin 2, Continuous fun p : Fin 2 → Fin 2 → ℂ => (p i j).re :=
    fun i j => Complex.continuous_re.comp (hc i j)
  have him : ∀ i j : Fin 2, Continuous fun p : Fin 2 → Fin 2 → ℂ => (p i j).im :=
    fun i j => Complex.continuous_im.comp (hc i j)
  refine IsOpen.measurableSet ?_
  simp only [ksDom, Set.setOf_and]
  exact (isOpen_lt continuous_const (hre 1 0)).inter ((isOpen_lt continuous_const (him 1 0)).inter
    ((isOpen_lt continuous_const (hre 0 0)).inter ((isOpen_lt (hre 0 0) continuous_const).inter
    ((isOpen_lt continuous_const (him 0 0)).inter ((isOpen_lt (him 0 0) continuous_const).inter
    ((isOpen_lt continuous_const (hre 0 1)).inter ((isOpen_lt (hre 0 1) continuous_const).inter
    ((isOpen_lt continuous_const (him 0 1)).inter (isOpen_lt (him 0 1) continuous_const)))))))))

private theorem ksLocus_eq_regSetℂ : ksLocus = HaarRef.regSetℂ := by
  ext m
  simp only [ksLocus, HaarRef.regSetℂ, Set.mem_setOf_eq, HaarRef.det_of_apply]

private def shuf : (Fin 2 → Fin 2 → ℂ) ≃ᵐ ℂ × ((ℂ × ℂ) × ℂ) :=
  HaarRef.eqvℂ.trans
    ((MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℂ)).trans MeasurableEquiv.prodAssoc)) :
      (ℂ × ℂ) × (ℂ × ℂ) ≃ᵐ ℂ × ((ℂ × ℂ) × ℂ))

private theorem shuf_apply (p : Fin 2 → Fin 2 → ℂ) : shuf p = (p 1 0, ((p 0 0, p 0 1), p 1 1)) := rfl

private theorem measurePreserving_shuf : MeasurePreserving shuf volume volume := by
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm : (ℂ × ℂ) × (ℂ × ℂ) ≃ᵐ ((ℂ × ℂ) × ℂ) × ℂ)
      volume volume :=
    (measurePreserving_prodAssoc (volume : Measure (ℂ × ℂ)) (volume : Measure ℂ) (volume : Measure ℂ)).symm _
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℂ) : ((ℂ × ℂ) × ℂ) × ℂ ≃ᵐ (ℂ × (ℂ × ℂ)) × ℂ)
      volume volume :=
    (Measure.measurePreserving_swap (μ := (volume : Measure (ℂ × ℂ))) (ν := (volume : Measure ℂ))).prod
      (MeasurePreserving.id (volume : Measure ℂ))
  have h4 : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℂ × (ℂ × ℂ)) × ℂ ≃ᵐ ℂ × ((ℂ × ℂ) × ℂ)) volume volume :=
    measurePreserving_prodAssoc (volume : Measure ℂ) (volume : Measure (ℂ × ℂ)) (volume : Measure ℂ)
  have hs := (h4.comp (h3.comp h2)).comp HaarRef.measurePreserving_eqvℂ
  exact hs

private theorem ksDom_eq_preimage : ksDom = shuf ⁻¹' (TorusSlot.bSet ×ˢ (aSet ×ˢ (Set.univ : Set ℂ))) := by
  ext p
  simp only [ksDom, aSet, TorusSlot.bSet, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Set.mem_setOf_eq,
    shuf_apply, and_assoc]

private def orbF (φ : GL (Fin 2) ℂ → ℂ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : ℂ :=
  φ (TwistedTorus.Rid.ridGL (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x))

private theorem ridGL_orbit (δ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    TwistedTorus.Rid.ridGL (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) =
      (TwistedTorus.Rid.ridGL x)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (TwistedTorus.Rid.ridGL x) := by
  have hσ : TwistedTorus.Rid.ridGL (sigmaGL ℝ ℂ ℝ Complex.conjAe x) = conjEntries (TwistedTorus.Rid.ridGL x) :=
    Units.ext (TwistedTorus.Rid.ridGL_sigmaGL _)
  rw [map_mul, map_mul, map_inv, hσ]

private theorem continuous_orbF (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    Continuous (orbF φ δ) := by
  have hconj : Continuous (conjEntries : GL (Fin 2) ℂ → GL (Fin 2) ℂ) :=
    TwistedTorus.Rid.continuous_glMap Complex.continuous_conj
  have h1 : Continuous fun g : GL (Fin 2) ℂ => g⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries g :=
    (continuous_inv.mul continuous_const).mul hconj
  have he : orbF φ δ = fun x => φ ((TwistedTorus.Rid.ridGL x)⁻¹ * TwistedTorus.Rid.ridGL δ *
      conjEntries (TwistedTorus.Rid.ridGL x)) := funext fun x => by simp only [orbF, ridGL_orbit]
  rw [he]
  have hc := hφ.comp (h1.comp TwistedTorus.Rid.continuous_ridGL)
  exact hc

private theorem measurable_orbF (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ (orbF φ δ) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  exact (continuous_orbF φ hφ δ).measurable

private def wE (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : ℝ :=
  4⁻¹ * (w x + w (torA (-1, 1) * x) + w (torA (1, -1) * x) + w (torA (-1, -1) * x))

private theorem wE_nonneg (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    0 ≤ wE w x := by
  have h0 := hw0 x
  have h1 := hw0 (torA (-1, 1) * x)
  have h2 := hw0 (torA (1, -1) * x)
  have h3 := hw0 (torA (-1, -1) * x)
  unfold wE
  exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3)

private theorem le_four_mul_wE (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    w x ≤ 4 * wE w x ∧ w (torA (-1, 1) * x) ≤ 4 * wE w x ∧ w (torA (1, -1) * x) ≤ 4 * wE w x ∧
      w (torA (-1, -1) * x) ≤ 4 * wE w x := by
  have h0 := hw0 x
  have h1 := hw0 (torA (-1, 1) * x)
  have h2 := hw0 (torA (1, -1) * x)
  have h3 := hw0 (torA (-1, -1) * x)
  have h4 : 4 * wE w x = w x + w (torA (-1, 1) * x) + w (torA (1, -1) * x) + w (torA (-1, -1) * x) := by
    unfold wE
    ring
  rw [h4]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem measurable_wE (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hwm : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ w) :
    @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ (wE w) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  have hm : ∀ b : ℝ × ℝ, Measurable fun x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => w (torA b * x) :=
    fun b => hwm.comp (continuous_const.mul continuous_id).measurable
  unfold wE
  exact measurable_const.mul (((hwm.add (hm _)).add (hm _)).add (hm _))

private theorem integral_orbF_mul_wE (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (a₁ a₂ : ℝ)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ w)
    (hint : Integrable (fun x => orbF φ δ x * (wE w x : ℂ)) μ) :
    ∫ x, orbF φ δ x * (w x : ℂ) ∂μ = ∫ x, orbF φ δ x * (wE w x : ℂ) ∂μ := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI := hμ
  have hΦ : ∀ (b : ℝ × ℝ) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), orbF φ δ (torA b * x) = orbF φ δ x :=
    fun b x => orbitFactor_torA_mul φ a₁ a₂ δ hδ b x

  have hav : ∀ b : ℝ × ℝ, ∫ x, orbF φ δ x * (w (torA b * x) : ℂ) ∂μ = ∫ x, orbF φ δ x * (w x : ℂ) ∂μ :=
    fun b => Average.integral_mul_comp_mul_left μ (orbF φ δ) (fun x => (w x : ℂ)) (torA b) (hΦ b)

  have hmeas : ∀ b : ℝ × ℝ, AEStronglyMeasurable (fun x => orbF φ δ x * (w (torA b * x) : ℂ)) μ := fun b =>
    ((measurable_orbF φ hφ δ).mul
      (Complex.measurable_ofReal.comp (hwm.comp (continuous_const.mul continuous_id).measurable))).aestronglyMeasurable
  have hdom : ∀ (v : ℝ) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), 0 ≤ v → v ≤ 4 * wE w x →
      ‖orbF φ δ x * (v : ℂ)‖ ≤ ‖(4 : ℂ) * (orbF φ δ x * (wE w x : ℂ))‖ := by
    intro v x hv hle
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hv,
      Real.norm_of_nonneg (wE_nonneg w hw0 x), Complex.norm_ofNat]
    calc ‖orbF φ δ x‖ * v ≤ ‖orbF φ δ x‖ * (4 * wE w x) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = 4 * (‖orbF φ δ x‖ * wE w x) := by ring
  have hint4 : Integrable (fun x => (4 : ℂ) * (orbF φ δ x * (wE w x : ℂ))) μ := hint.const_mul _
  have hi₀ : Integrable (fun x => orbF φ δ x * (w x : ℂ)) μ :=
    hint4.norm.mono' (((measurable_orbF φ hφ δ).mul (Complex.measurable_ofReal.comp hwm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hdom _ x (hw0 x) (le_four_mul_wE w hw0 x).1)
  have hi₁ : Integrable (fun x => orbF φ δ x * (w (torA (-1, 1) * x) : ℂ)) μ :=
    hint4.norm.mono' (hmeas _) (Filter.Eventually.of_forall fun x => hdom _ x (hw0 _) (le_four_mul_wE w hw0 x).2.1)
  have hi₂ : Integrable (fun x => orbF φ δ x * (w (torA (1, -1) * x) : ℂ)) μ :=
    hint4.norm.mono' (hmeas _) (Filter.Eventually.of_forall fun x => hdom _ x (hw0 _) (le_four_mul_wE w hw0 x).2.2.1)
  have hi₃ : Integrable (fun x => orbF φ δ x * (w (torA (-1, -1) * x) : ℂ)) μ :=
    hint4.norm.mono' (hmeas _) (Filter.Eventually.of_forall fun x => hdom _ x (hw0 _) (le_four_mul_wE w hw0 x).2.2.2)

  have hsum : ∫ x, orbF φ δ x * (wE w x : ℂ) ∂μ = 4⁻¹ * (∫ x, orbF φ δ x * (w x : ℂ) ∂μ +
      ∫ x, orbF φ δ x * (w (torA (-1, 1) * x) : ℂ) ∂μ + ∫ x, orbF φ δ x * (w (torA (1, -1) * x) : ℂ) ∂μ +
      ∫ x, orbF φ δ x * (w (torA (-1, -1) * x) : ℂ) ∂μ) := by
    have h01 : Integrable (fun x => orbF φ δ x * (w x : ℂ) + orbF φ δ x * (w (torA (-1, 1) * x) : ℂ)) μ :=
      hi₀.add hi₁
    have h012 : Integrable (fun x => orbF φ δ x * (w x : ℂ) + orbF φ δ x * (w (torA (-1, 1) * x) : ℂ) +
        orbF φ δ x * (w (torA (1, -1) * x) : ℂ)) μ := h01.add hi₂
    rw [← integral_add hi₀ hi₁, ← integral_add h01 hi₂, ← integral_add h012 hi₃, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [wE, Pi.add_apply]
    push_cast
    ring
  rw [hsum, hav, hav, hav]
  ring

private def ksF (φ : GL (Fin 2) ℂ → ℂ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (A : Fin 2 → Fin 2 → ℂ) : ℂ :=
  (HaarRef.densℂ A).toReal • (orbF φ δ (HaarRef.glOfℂ A) * (wE w (HaarRef.glOfℂ A) : ℂ))

private def ksKp (φ : GL (Fin 2) ℂ → ℂ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (p : Fin 2 → Fin 2 → ℂ) : ℂ :=
  (ksJ p).toReal • ksF φ δ w (ksChart p)

private def ksChartArr (p : Fin 2 → Fin 2 → ℂ) : Fin 2 → Fin 2 → ℂ :=
  Matrix.of.symm
    (!![((Real.sqrt ((p 1 0).re ^ 2) : ℝ) : ℂ), ((p 1 0).re : ℂ) * p 1 1; 0, ((Real.sqrt ((p 1 0).im ^ 2) : ℝ) : ℂ)] *
      ((unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))

private def ksPos : Set (Fin 2 → Fin 2 → ℂ) := {p | 0 < (p 1 0).re ∧ 0 < (p 1 0).im}

open scoped Classical in
private theorem ksChart_eq_piecewise : ksChart = ksPos.piecewise ksChartArr (fun _ => Matrix.of.symm 1) := by
  funext p
  by_cases hp : 0 < (p 1 0).re ∧ 0 < (p 1 0).im
  · rw [Set.piecewise_eq_of_mem _ _ _ (show p ∈ ksPos from hp)]
    unfold ksChart ksChartArr
    rw [dif_pos hp, Units.val_mul, Orbit.coe_twistedSplitElt]
  · rw [Set.piecewise_eq_of_notMem _ _ _ (show p ∉ ksPos from hp)]
    unfold ksChart
    rw [dif_neg hp, Units.val_one]

private theorem continuous_ksChartArr : Continuous ksChartArr := by
  have hc : ∀ i j : Fin 2, Continuous fun p : Fin 2 → Fin 2 → ℂ => p i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have hre : ∀ i j : Fin 2, Continuous fun p : Fin 2 → Fin 2 → ℂ => (p i j).re :=
    fun i j => Complex.continuous_re.comp (hc i j)
  have him : ∀ i j : Fin 2, Continuous fun p : Fin 2 → Fin 2 → ℂ => (p i j).im :=
    fun i j => Complex.continuous_im.comp (hc i j)
  have hU : Continuous fun p : Fin 2 → Fin 2 → ℂ =>
      ((unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    Units.continuous_val.comp (Window.continuous_unitaryElt_comp (hre 0 0) (him 0 0) (hre 0 1) (him 0 1))
  have hM : Continuous fun p : Fin 2 → Fin 2 → ℂ =>
      !![((Real.sqrt ((p 1 0).re ^ 2) : ℝ) : ℂ), ((p 1 0).re : ℂ) * p 1 1;
        0, ((Real.sqrt ((p 1 0).im ^ 2) : ℝ) : ℂ)] := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ((hre 1 0).pow 2))
    · exact (Complex.continuous_ofReal.comp (hre 1 0)).mul (hc 1 1)
    · exact continuous_const
    · exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ((him 1 0).pow 2))
  unfold ksChartArr
  exact hM.mul hU

private theorem measurable_ksChart : Measurable ksChart := by
  have hre : Continuous fun p : Fin 2 → Fin 2 → ℂ => (p 1 0).re :=
    Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_apply 1))
  have him : Continuous fun p : Fin 2 → Fin 2 → ℂ => (p 1 0).im :=
    Complex.continuous_im.comp ((continuous_apply 0).comp (continuous_apply 1))
  have hS : MeasurableSet ksPos :=
    ((isOpen_lt continuous_const hre).inter (isOpen_lt continuous_const him)).measurableSet
  rw [ksChart_eq_piecewise]
  exact Measurable.piecewise hS continuous_ksChartArr.measurable measurable_const

private theorem measurable_ksF (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hwm : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ w) : Measurable (ksF φ δ w) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  unfold ksF
  exact HaarRef.measurable_densℂ.ennreal_toReal.smul (((measurable_orbF φ hφ δ).comp HaarRef.measurable_glOfℂ).mul
    (Complex.measurable_ofReal.comp ((measurable_wE w hwm).comp HaarRef.measurable_glOfℂ)))

private theorem measurable_ksKp (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hwm : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ w) : Measurable (ksKp φ δ w) := by
  unfold ksKp
  exact measurable_ksJ.ennreal_toReal.smul ((measurable_ksF φ hφ δ w hwm).comp measurable_ksChart)

private theorem ksKp_eq (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ ksDom) :
    ksKp φ δ w p = (2 * Real.sin (p 0 0).im * Real.cos (p 0 0).im : ℂ) * secF φ a₁ a₂ h (p 0 0, p 0 1) (p 1 1) *
      ((((p 1 0).re * (p 1 0).im)⁻¹ * wE w (torA ((p 1 0).re, (p 1 0).im) * secY (p 0 0, p 0 1) (p 1 1)) : ℝ) :
        ℂ) := by
  have hp' := hp
  simp only [ksDom, Set.mem_setOf_eq] at hp'
  obtain ⟨hb₁, hb₂, -⟩ := hp'
  have hb₁' : ((p 1 0).re : ℂ) ≠ 0 := by exact_mod_cast hb₁.ne'
  have hb₂' : ((p 1 0).im : ℂ) ≠ 0 := by exact_mod_cast hb₂.ne'
  unfold ksKp ksF
  rw [ksJ_toReal hp, densℂ_ksChart hp, glOfℂ_ksChart hp, orbF, orbitFactor_torA_mul φ a₁ a₂ δ hδ,
    orbitFactor_secY φ a₁ a₂ h δ hδ, smul_smul, Complex.real_smul]
  push_cast
  field_simp

private theorem measurableSet_bSet : MeasurableSet TorusSlot.bSet :=
  ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)).measurableSet

private theorem measurableSet_aSet : MeasurableSet aSet := by
  have hre1 : Continuous fun α : ℂ × ℂ => α.1.re := Complex.continuous_re.comp continuous_fst
  have him1 : Continuous fun α : ℂ × ℂ => α.1.im := Complex.continuous_im.comp continuous_fst
  have hre2 : Continuous fun α : ℂ × ℂ => α.2.re := Complex.continuous_re.comp continuous_snd
  have him2 : Continuous fun α : ℂ × ℂ => α.2.im := Complex.continuous_im.comp continuous_snd
  refine IsOpen.measurableSet ?_
  simp only [aSet, Set.setOf_and]
  exact (isOpen_lt continuous_const hre1).inter ((isOpen_lt hre1 continuous_const).inter
    ((isOpen_lt continuous_const him1).inter ((isOpen_lt him1 continuous_const).inter
    ((isOpen_lt continuous_const hre2).inter ((isOpen_lt hre2 continuous_const).inter
    ((isOpen_lt continuous_const him2).inter (isOpen_lt him2 continuous_const)))))))

private def ksK (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (q : ℂ × ((ℂ × ℂ) × ℂ)) : ℂ :=
  (2 * Real.sin q.2.1.1.im * Real.cos q.2.1.1.im : ℂ) * secF φ a₁ a₂ h q.2.1 q.2.2 *
    (((q.1.re * q.1.im)⁻¹ * wE w (torA (q.1.re, q.1.im) * secY q.2.1 q.2.2) : ℝ) : ℂ)

private theorem ks_pointwise (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ ksDom) :
    ksKp φ δ w p = ksK φ a₁ a₂ h w (shuf p) := by
  rw [ksKp_eq φ a₁ a₂ h δ hδ w hp, shuf_apply]
  rfl

private theorem ks_inner (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
          (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w)
    (σ : (ℂ × ℂ) × ℂ) :
    IntegrableOn (fun b : ℂ => ksK φ a₁ a₂ h w (b, σ)) TorusSlot.bSet ∧
      ∫ b in TorusSlot.bSet, ksK φ a₁ a₂ h w (b, σ) =
        (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) * secF φ a₁ a₂ h σ.1 σ.2 * (((4 * cT : ℝ) : ℂ))⁻¹ ∧
      ∫ b in TorusSlot.bSet, ‖ksK φ a₁ a₂ h w (b, σ)‖ =
        ‖(2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) * secF φ a₁ a₂ h σ.1 σ.2‖ * (4 * cT : ℝ)⁻¹ := by
  have hw0 : ∀ y, 0 ≤ w y := hw.1

  obtain ⟨C, hC⟩ : ∃ C : ℂ, C = (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) * secF φ a₁ a₂ h σ.1 σ.2 :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℝ, g = fun b => (b.re * b.im)⁻¹ * wE w (torA (b.re, b.im) * secY σ.1 σ.2) := ⟨_, rfl⟩
  have hK : ∀ b, ksK φ a₁ a₂ h w (b, σ) = C * (g b : ℂ) := fun b => by
    rw [hC, hg]
    rfl
  have hg0 : ∀ b ∈ TorusSlot.bSet, 0 ≤ g b := fun b hb => by
    rw [hg]
    exact mul_nonneg (inv_nonneg.2 (mul_pos hb.1 hb.2).le) (wE_nonneg w hw0 _)
  simp only [hK]
  rw [← hC]
  by_cases hfs : secF φ a₁ a₂ h σ.1 σ.2 = 0
  · have hC0 : C = 0 := by rw [hC, hfs, mul_zero]
    refine ⟨?_, ?_, ?_⟩
    · refine (integrableOn_zero).congr_fun (fun b _ => ?_) measurableSet_bSet
      rw [hC0, zero_mul]
    · have h0 : ∫ b in TorusSlot.bSet, C * (g b : ℂ) = ∫ b in TorusSlot.bSet, (0 : ℂ) :=
        setIntegral_congr_fun measurableSet_bSet fun b _ => by rw [hC0, zero_mul]
      rw [h0, hC0, zero_mul, integral_zero]
    · have h0 : ∫ b in TorusSlot.bSet, ‖C * (g b : ℂ)‖ = ∫ b in TorusSlot.bSet, (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_bSet fun b _ => by rw [hC0, zero_mul, norm_zero]
      rw [h0, hC0, norm_zero, zero_mul, integral_zero]
  ·
    have hx : (fun y => φ (TwistedTorus.Rid.ridGL y))
        ((secY σ.1 σ.2)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (secY σ.1 σ.2)) ≠ 0 := by
      change φ (TwistedTorus.Rid.ridGL ((secY σ.1 σ.2)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (secY σ.1 σ.2))) ≠ 0
      rw [orbitFactor_secY φ a₁ a₂ h δ hδ]
      exact hfs
    obtain ⟨hi₁, hi₂, hi₃, hi₄, hsum⟩ :=
      TorusSlot.split_slot δ τ cT hcT hτ (fun y => φ (TwistedTorus.Rid.ridGL y)) w hw (secY σ.1 σ.2) hx

    have hwE : ∀ b ∈ TorusSlot.bSet, g b = 4⁻¹ * ((b.re * b.im)⁻¹ *
        (w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, b.im)) * secY σ.1 σ.2) +
          w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, b.im)) * secY σ.1 σ.2) +
          w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, -b.im)) * secY σ.1 σ.2) +
          w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, -b.im)) * secY σ.1 σ.2))) := by
      intro b hb
      have hb0 : (b.re, b.im).1 * (b.re, b.im).2 ≠ 0 := (mul_pos hb.1 hb.2).ne'
      have e₂ : torA (-1, 1) * torA (b.re, b.im) = torA (-b.re, b.im) := by
        rw [torA_sign_mul (-1) 1 (Or.inr rfl) (Or.inl rfl) _ hb0, neg_one_mul, one_mul]
      have e₃ : torA (1, -1) * torA (b.re, b.im) = torA (b.re, -b.im) := by
        rw [torA_sign_mul 1 (-1) (Or.inl rfl) (Or.inr rfl) _ hb0, neg_one_mul, one_mul]
      have e₄ : torA (-1, -1) * torA (b.re, b.im) = torA (-b.re, -b.im) := by
        rw [torA_sign_mul (-1) (-1) (Or.inr rfl) (Or.inr rfl) _ hb0, neg_one_mul, neg_one_mul]
      rw [hg]
      simp only [wE]
      rw [← mul_assoc (torA (-1, 1)), ← mul_assoc (torA (1, -1)), ← mul_assoc (torA (-1, -1)), e₂, e₃, e₄]
      simp only [torA]
      ring
    have hI : IntegrableOn g TorusSlot.bSet := by
      have hs : IntegrableOn (fun b : ℂ => 4⁻¹ * ((b.re * b.im)⁻¹ *
          (w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, b.im)) * secY σ.1 σ.2) +
            w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, b.im)) * secY σ.1 σ.2) +
            w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (b.re, -b.im)) * secY σ.1 σ.2) +
            w (toTensorGL ℝ ℂ ℝ (Transfer.diagElt (-b.re, -b.im)) * secY σ.1 σ.2)))) TorusSlot.bSet := by
        have h4 := ((hi₁.add hi₂).add hi₃).add hi₄
        refine IntegrableOn.congr_fun (h4.const_mul 4⁻¹) (fun b _ => ?_) measurableSet_bSet
        simp only [Pi.add_apply]
        ring
      exact hs.congr_fun (fun b hb => (hwE b hb).symm) measurableSet_bSet
    have hval : ∫ b in TorusSlot.bSet, g b = 4⁻¹ * (cT : ℝ)⁻¹ := by
      rw [setIntegral_congr_fun measurableSet_bSet hwE, integral_const_mul, hsum]
    refine ⟨hI.ofReal.const_mul _, ?_, ?_⟩
    · rw [integral_const_mul, integral_complex_ofReal, hval]
      push_cast
      ring
    · have hn : ∀ b ∈ TorusSlot.bSet, ‖C * (g b : ℂ)‖ = ‖C‖ * g b := fun b hb => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 b hb)]
      rw [setIntegral_congr_fun measurableSet_bSet hn, integral_const_mul, hval]
      ring

private theorem aSet_subset_closedBall : aSet ⊆ Metric.closedBall (0 : ℂ × ℂ) 20 := by
  intro α hα
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hα
  have hπ := Real.pi_le_four
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [abs_of_pos h1, abs_of_pos h3]
    linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [abs_of_pos h5, abs_of_pos h7]
    linarith

private theorem integrableOn_secFactor (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (ζ : ℂ → ℂ) (hζ : Continuous ζ) (κ : ℝ) (hκ : 0 < κ)
    (hcoer : ∀ z, κ * ‖z‖ ≤ ‖ζ z‖) :
    IntegrableOn (fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
      φ ((kU σ.1)⁻¹ * twistedSplitElt a₁ a₂ (ζ σ.2) h * conjEntries (kU σ.1))) (aSet ×ˢ (Set.univ : Set ℂ)) := by
  obtain ⟨R, hR⟩ := Proper.exists_bound_split φ hφc a₁ a₂ h
  have hP : Continuous fun σ : (ℂ × ℂ) × ℂ => ((σ.1.1.re, σ.1.1.im, σ.1.2.re, σ.1.2.im), ζ σ.2) :=
    ((Complex.continuous_re.comp (continuous_fst.comp continuous_fst)).prodMk
      ((Complex.continuous_im.comp (continuous_fst.comp continuous_fst)).prodMk
      ((Complex.continuous_re.comp (continuous_snd.comp continuous_fst)).prodMk
      (Complex.continuous_im.comp (continuous_snd.comp continuous_fst))))).prodMk (hζ.comp continuous_snd)
  have hc := (Proper.continuous_orbitFactor_split φ hφ a₁ a₂ h).comp hP
  have hc' : Continuous fun σ : (ℂ × ℂ) × ℂ =>
      φ ((kU σ.1)⁻¹ * twistedSplitElt a₁ a₂ (ζ σ.2) h * conjEntries (kU σ.1)) := hc
  have hcont : Continuous fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
      φ ((kU σ.1)⁻¹ * twistedSplitElt a₁ a₂ (ζ σ.2) h * conjEntries (kU σ.1)) :=
    (by fun_prop : Continuous fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ)).mul hc'
  have hK : IsCompact (Metric.closedBall (0 : ℂ × ℂ) 20 ×ˢ Metric.closedBall (0 : ℂ) (R / κ)) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hint := hcont.continuousOn.integrableOn_compact (μ := volume) hK
  refine hint.of_forall_diff_eq_zero (measurableSet_aSet.prod MeasurableSet.univ) ?_
  rintro ⟨α, z⟩ ⟨hs, hnot⟩
  have hα : α ∈ Metric.closedBall (0 : ℂ × ℂ) 20 := aSet_subset_closedBall (Set.mem_prod.1 hs).1
  have hz : z ∉ Metric.closedBall (0 : ℂ) (R / κ) := fun hz => hnot (Set.mem_prod.2 ⟨hα, hz⟩)
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  have hzero : φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ (ζ z) h * conjEntries (kU α)) = 0 := by
    by_contra hne
    have hb : ‖ζ z‖ ≤ R := hR α.1.re α.1.im α.2.re α.2.im (ζ z) hne
    have hzle : ‖z‖ ≤ R / κ := by
      rw [le_div_iff₀ hκ, mul_comm]
      exact (hcoer z).trans hb
    exact absurd hzle (not_le.2 hz)
  simp only [hzero, mul_zero]

private theorem integrableOn_secF (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (hne : a₁ ≠ a₂) :
    IntegrableOn (fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
      secF φ a₁ a₂ h σ.1 σ.2) (aSet ×ˢ (Set.univ : Set ℂ)) := by
  have hs : Real.sqrt a₁ ≠ Real.sqrt a₂ := fun heq => hne ((Real.sqrt_inj h.1.le h.2.le).1 heq)
  have hκ : 0 < |Real.sqrt a₁ - Real.sqrt a₂| := abs_pos.2 (sub_ne_zero.2 hs)
  have hζ : Continuous fun z : ℂ => (Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) z - (Real.sqrt a₂ : ℂ) * z :=
    (continuous_const.mul Complex.continuous_conj).sub (continuous_const.mul continuous_id)
  have hcoer : ∀ z : ℂ, |Real.sqrt a₁ - Real.sqrt a₂| * ‖z‖ ≤
      ‖(Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) z - (Real.sqrt a₂ : ℂ) * z‖ := fun z => by
    have h1 : ‖(Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) z‖ = Real.sqrt a₁ * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_conj]
    have h2 : ‖(Real.sqrt a₂ : ℂ) * z‖ = Real.sqrt a₂ * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h3 := abs_norm_sub_norm_le ((Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) z) ((Real.sqrt a₂ : ℂ) * z)
    rw [h1, h2, ← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg z)] at h3
    exact h3
  refine (integrableOn_secFactor φ hφ hφc a₁ a₂ h
    (fun z : ℂ => (Real.sqrt a₁ : ℂ) * (starRingEnd ℂ) z - (Real.sqrt a₂ : ℂ) * z) hζ
    |Real.sqrt a₁ - Real.sqrt a₂| hκ hcoer).congr_fun (fun σ _ => ?_) (measurableSet_aSet.prod MeasurableSet.univ)
  simp only [secF]

private scoped instance volume_pi_isAddHaarMeasure₁ : Measure.IsAddHaarMeasure (volume : Measure (Fin 2 → ℂ)) :=
  Measure.pi.isAddHaarMeasure _

private scoped instance volume_pi_isAddHaarMeasure₂ : Measure.IsAddHaarMeasure (volume : Measure (Fin 2 → Fin 2 → ℂ)) :=
  Measure.pi.isAddHaarMeasure _

private theorem split_transport (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (hne : a₁ ≠ a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) (c : NNReal)
    (hμc : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) HaarRef.glOfℂ HaarRef.refMeasureℂ)
    (hKS : Measure.map ksChart ((volume.restrict ksDom).withDensity ksJ) = volume.restrict ksLocus)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
          (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w) :
    Integrable (fun x => orbF φ δ x * (wE w x : ℂ)) μ ∧
      ∫ x, orbF φ δ x * (w x : ℂ) ∂μ =
        (c : ℂ) * (((4 * cT : ℝ) : ℂ))⁻¹ * ∫ σ in aSet ×ˢ (Set.univ : Set ℂ),
          (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) * secF φ a₁ a₂ h σ.1 σ.2 := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI := hμ
  have hw0 : ∀ y, 0 ≤ w y := hw.1
  have hwm : Measurable w := hw.2.1

  have hKpm : Measurable (ksKp φ δ w) := measurable_ksKp φ hφ δ w hwm
  have hS : MeasurableSet (aSet ×ˢ (Set.univ : Set ℂ)) := measurableSet_aSet.prod MeasurableSet.univ
  have hmem : ∀ q ∈ TorusSlot.bSet ×ˢ (aSet ×ˢ (Set.univ : Set ℂ)), shuf.symm q ∈ ksDom := fun q hq => by
    rw [ksDom_eq_preimage, Set.mem_preimage, MeasurableEquiv.apply_symm_apply]
    exact hq
  have hKae : (fun q => ksKp φ δ w (shuf.symm q)) =ᵐ[volume.restrict (TorusSlot.bSet ×ˢ (aSet ×ˢ Set.univ))]
      ksK φ a₁ a₂ h w := by
    refine (ae_restrict_iff' (measurableSet_bSet.prod hS)).2 (Filter.Eventually.of_forall fun q hq => ?_)
    show ksKp φ δ w (shuf.symm q) = ksK φ a₁ a₂ h w q
    rw [ks_pointwise φ a₁ a₂ h δ hδ w (hmem q hq), MeasurableEquiv.apply_symm_apply]
  have hKm : AEStronglyMeasurable (ksK φ a₁ a₂ h w)
      ((volume.restrict TorusSlot.bSet).prod (volume.restrict (aSet ×ˢ (Set.univ : Set ℂ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ((hKpm.comp shuf.symm.measurable).aestronglyMeasurable).congr hKae

  have hsecI := integrableOn_secF φ hφ hφc a₁ a₂ h hne
  have hprod : Integrable (ksK φ a₁ a₂ h w)
      ((volume.restrict TorusSlot.bSet).prod (volume.restrict (aSet ×ˢ (Set.univ : Set ℂ)))) := by
    refine (integrable_prod_iff' hKm).2 ⟨Filter.Eventually.of_forall fun σ =>
      (ks_inner φ a₁ a₂ h δ hδ τ cT hcT hτ w hw σ).1, ?_⟩
    have hn : (fun σ : (ℂ × ℂ) × ℂ => ∫ b, ‖ksK φ a₁ a₂ h w (b, σ)‖ ∂(volume.restrict TorusSlot.bSet)) =
        fun σ => ‖(2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) * secF φ a₁ a₂ h σ.1 σ.2‖ * (4 * cT : ℝ)⁻¹ :=
      funext fun σ => (ks_inner φ a₁ a₂ h δ hδ τ cT hcT hτ w hw σ).2.2
    rw [hn]
    have hsecI' : Integrable (fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
        secF φ a₁ a₂ h σ.1 σ.2) (volume.restrict (aSet ×ˢ (Set.univ : Set ℂ))) := hsecI
    exact hsecI'.norm.mul_const _
  have hprod' : IntegrableOn (ksK φ a₁ a₂ h w) (TorusSlot.bSet ×ˢ (aSet ×ˢ (Set.univ : Set ℂ))) volume := by
    have h1 := hprod
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h1
    exact h1

  have hDK : IntegrableOn (fun q => ksKp φ δ w (shuf.symm q)) (TorusSlot.bSet ×ˢ (aSet ×ˢ (Set.univ : Set ℂ)))
      volume := hprod'.congr_fun_ae hKae.symm
  have hD : IntegrableOn (ksKp φ δ w) ksDom volume := by
    have h1 : IntegrableOn (fun p => (fun q => ksKp φ δ w (shuf.symm q)) (shuf p)) ksDom volume := by
      rw [ksDom_eq_preimage]
      exact (measurePreserving_shuf.integrableOn_comp_preimage shuf.measurableEmbedding).2 hDK
    refine h1.congr_fun (fun p _ => ?_) measurableSet_ksDom
    simp only [MeasurableEquiv.symm_apply_apply]
  have hvol : volume HaarRef.regSetℂ ≠ 0 := by
    refine HaarRef.isOpen_regSetℂ.measure_ne_zero volume ⟨Matrix.of.symm 1, ?_⟩
    change (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hKS' : Measure.map ksChart ((volume.restrict ksDom).withDensity ksJ) = volume.restrict HaarRef.regSetℂ := by
    rw [hKS, ksLocus_eq_regSetℂ]
  have hFm : Measurable (ksF φ δ w) := measurable_ksF φ hφ δ w hwm
  have hL : IntegrableOn (ksF φ δ w) HaarRef.regSetℂ volume :=
    (HaarRef.integrableOn_iff_of_map_eq measurable_ksJ ksJ_lt_top hKS' hvol (ksF φ δ w)
      hFm.aestronglyMeasurable).2 hD
  have hHm : Measurable fun x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => orbF φ δ x * (wE w x : ℂ) :=
    (measurable_orbF φ hφ δ).mul (Complex.measurable_ofReal.comp (measurable_wE w hwm))
  have hintG : Integrable (fun x => orbF φ δ x * (wE w x : ℂ)) μ := by
    rw [hμc]
    refine Integrable.smul_measure_nnreal ?_
    refine (integrable_map_measure hHm.aestronglyMeasurable HaarRef.measurable_glOfℂ.aemeasurable).2 ?_
    unfold HaarRef.refMeasureℂ
    exact (integrable_withDensity_iff_integrable_smul' HaarRef.measurable_densℂ
      (Filter.Eventually.of_forall HaarRef.densℂ_lt_top)).2 hL
  refine ⟨hintG, ?_⟩

  have hI : ∫ x, orbF φ δ x * (w x : ℂ) ∂μ = ∫ x, orbF φ δ x * (wE w x : ℂ) ∂μ :=
    integral_orbF_mul_wE φ hφ a₁ a₂ δ hδ μ hμ w hw0 hwm hintG
  have hhaar : ∫ x, orbF φ δ x * (wE w x : ℂ) ∂μ = (c : ℝ) • ∫ A in HaarRef.regSetℂ, ksF φ δ w A :=
    HaarRef.integral_haar_eqℂ μ c hμc _ hHm
  obtain ⟨htr, -⟩ := HaarRef.setIntegral_eq_of_map_eq measurable_ksJ ksJ_lt_top hKS' hvol (ksF φ δ w) hL
  have htr' : ∫ A in HaarRef.regSetℂ, ksF φ δ w A = ∫ p in ksDom, ksKp φ δ w p := htr
  have hshuf : ∫ p in ksDom, ksKp φ δ w p =
      ∫ q in TorusSlot.bSet ×ˢ (aSet ×ˢ (Set.univ : Set ℂ)), ksK φ a₁ a₂ h w q := by
    have h1 : ∫ p in ksDom, ksKp φ δ w p = ∫ p in ksDom, (fun q => ksKp φ δ w (shuf.symm q)) (shuf p) :=
      setIntegral_congr_fun measurableSet_ksDom fun p _ => by simp only [MeasurableEquiv.symm_apply_apply]
    rw [h1, ksDom_eq_preimage, measurePreserving_shuf.setIntegral_preimage_emb shuf.measurableEmbedding
      (fun q => ksKp φ δ w (shuf.symm q)) (TorusSlot.bSet ×ˢ (aSet ×ˢ (Set.univ : Set ℂ)))]
    exact integral_congr_ae hKae
  have hfub : ∫ q in TorusSlot.bSet ×ˢ (aSet ×ˢ (Set.univ : Set ℂ)), ksK φ a₁ a₂ h w q =
      ∫ σ in aSet ×ˢ (Set.univ : Set ℂ), ∫ b in TorusSlot.bSet, ksK φ a₁ a₂ h w (b, σ) := by
    rw [Measure.volume_eq_prod ℂ ((ℂ × ℂ) × ℂ), ← Measure.prod_restrict]
    exact integral_prod_symm _ hprod
  have hinner : ∫ σ in aSet ×ˢ (Set.univ : Set ℂ), ∫ b in TorusSlot.bSet, ksK φ a₁ a₂ h w (b, σ) =
      ∫ σ in aSet ×ˢ (Set.univ : Set ℂ), (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
        secF φ a₁ a₂ h σ.1 σ.2 * (((4 * cT : ℝ) : ℂ))⁻¹ :=
    integral_congr_ae (Filter.Eventually.of_forall fun σ => (ks_inner φ a₁ a₂ h δ hδ τ cT hcT hτ w hw σ).2.1)
  rw [hI, hhaar, htr', hshuf, hfub, hinner, integral_mul_const, Complex.real_smul]
  ring

private def angEquiv : ℂ × ℂ ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  Complex.measurableEquivRealProd.prodCongr Complex.measurableEquivRealProd

private theorem angEquiv_apply (α : ℂ × ℂ) : angEquiv α = ((α.1.re, α.1.im), (α.2.re, α.2.im)) := rfl

private theorem measurePreserving_angEquiv : MeasurePreserving angEquiv volume volume := by
  have h2 := Complex.volume_preserving_equiv_real_prod.prod Complex.volume_preserving_equiv_real_prod
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h2
  exact h2

private def boxA : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

private def boxB : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (2 * Real.pi) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)

private theorem aSet_eq_preimage : aSet = angEquiv ⁻¹' (boxA ×ˢ boxB) := by
  ext α
  simp only [aSet, boxA, boxB, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, Set.mem_setOf_eq, angEquiv_apply,
    and_assoc]

private def boxG (F : GL (Fin 2) ℂ → ℂ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  (2 * Real.sin p.1.2 * Real.cos p.1.2 : ℂ) * F (unitaryElt p.1.1 p.1.2 p.2.1 p.2.2)

private theorem continuous_boxG (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) : Continuous (boxG F) := by
  have hU : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => unitaryElt p.1.1 p.1.2 p.2.1 p.2.2 :=
    Window.continuous_unitaryElt_comp (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hFU : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => F (unitaryElt p.1.1 p.1.2 p.2.1 p.2.2) := by
    have hc := hF.comp hU
    exact hc
  unfold boxG
  exact (by fun_prop : Continuous fun p : (ℝ × ℝ) × (ℝ × ℝ) => (2 * Real.sin p.1.2 * Real.cos p.1.2 : ℂ)).mul hFU

private theorem setIntegral_Ioo_eq (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ) :
    ∫ x in Set.Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

private theorem window_integral (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) :
    ∫ α in aSet, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) * F (kU α) =
      ((4 * Real.pi ^ 3 : ℝ) : ℂ) * unitaryAverage F := by
  have hπ := Real.pi_pos
  have hg := continuous_boxG F hF

  have h1 : ∫ α in aSet, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) * F (kU α) = ∫ p in boxA ×ˢ boxB, boxG F p := by
    change ∫ α in aSet, boxG F (angEquiv α) = _
    rw [aSet_eq_preimage]
    exact measurePreserving_angEquiv.setIntegral_preimage_emb angEquiv.measurableEmbedding _ _

  have hK : IsCompact ((Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  have hsub : boxA ×ˢ boxB ⊆ (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    Set.prod_mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  have hI : IntegrableOn (boxG F) (boxA ×ˢ boxB) ((volume : Measure (ℝ × ℝ)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hg.continuousOn.integrableOn_compact hK).mono_set hsub

  have h2 : ∫ p in boxA ×ˢ boxB, boxG F p = ∫ a in boxA, ∫ b in boxB, boxG F (a, b) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ)]
    exact setIntegral_prod _ hI

  have hKB : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have h3 : ∀ a : ℝ × ℝ, ∫ b in boxB, boxG F (a, b) =
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), boxG F (a, (ξ₁, ξ₂)) := by
    intro a
    have hga : Continuous fun b : ℝ × ℝ => boxG F (a, b) :=
      hg.comp (continuous_const.prodMk continuous_id : Continuous fun b : ℝ × ℝ => ((a, b) : (ℝ × ℝ) × ℝ × ℝ))
    have hIa : IntegrableOn (fun b : ℝ × ℝ => boxG F (a, b)) boxB ((volume : Measure ℝ).prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact (hga.continuousOn.integrableOn_compact hKB).mono_set
        (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
    rw [Measure.volume_eq_prod ℝ ℝ, boxB, setIntegral_prod _ hIa,
      setIntegral_Ioo_eq _ _ (mul_pos two_pos hπ).le]
    refine intervalIntegral.integral_congr fun ξ₁ _ => ?_
    exact setIntegral_Ioo_eq _ _ (mul_pos two_pos hπ).le _

  have hH : IntegrableOn (fun a : ℝ × ℝ => ∫ b in boxB, boxG F (a, b)) boxA ((volume : Measure ℝ).prod volume) := by
    have hi : Integrable (boxG F) ((volume.restrict boxA).prod (volume.restrict boxB)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hI
    have hl := hi.integral_prod_left
    rw [← Measure.volume_eq_prod]
    exact hl
  have h4 : ∫ a in boxA, ∫ b in boxB, boxG F (a, b) =
      ∫ ψ in (0 : ℝ)..Real.pi, ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ b in boxB, boxG F ((ψ, η), b) := by
    have e1 : ∫ a in boxA, ∫ b in boxB, boxG F (a, b) =
        ∫ ψ in Set.Ioo (0 : ℝ) Real.pi, ∫ η in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫ b in boxB, boxG F ((ψ, η), b) :=
      setIntegral_prod _ hH
    rw [e1, setIntegral_Ioo_eq _ _ hπ.le]
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    exact setIntegral_Ioo_eq _ _ (half_pos hπ).le _

  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  have h5 : ((4 * Real.pi ^ 3 : ℝ) : ℂ) * unitaryAverage F =
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
        ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
          (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂) := by
    unfold unitaryAverage
    push_cast
    field_simp
  rw [h1, h2, h4, h5, Window.box_integral_eq_two_mul F hF]
  simp_rw [h3]
  simp only [boxG, intervalIntegral.integral_const_mul, mul_assoc]

private theorem section_eval (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (a₁ a₂ : ℝ)
    (h : 0 < a₁ ∧ 0 < a₂) (hne : a₁ ≠ a₂) :
    ∫ σ in aSet ×ˢ (Set.univ : Set ℂ), (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) * secF φ a₁ a₂ h σ.1 σ.2 =
      ((4 * Real.pi ^ 3 * |a₁ - a₂|⁻¹ : ℝ) : ℂ) * twistedSplitTransform φ a₁ a₂ := by

  have hGI : IntegrableOn (fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
      φ ((kU σ.1)⁻¹ * twistedSplitElt a₁ a₂ σ.2 h * conjEntries (kU σ.1))) (aSet ×ˢ (Set.univ : Set ℂ)) :=
    integrableOn_secFactor φ hφ hφc a₁ a₂ h (fun z : ℂ => z) continuous_id 1 one_pos fun z => (one_mul _).le
  have hFI := integrableOn_secF φ hφ hφc a₁ a₂ h hne

  have h1 : ∫ σ in aSet ×ˢ (Set.univ : Set ℂ), (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
      secF φ a₁ a₂ h σ.1 σ.2 =
      ∫ α in aSet, ∫ z, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) * secF φ a₁ a₂ h α z := by
    have hFI' : IntegrableOn (fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
        secF φ a₁ a₂ h σ.1 σ.2) (aSet ×ˢ (Set.univ : Set ℂ)) ((volume : Measure (ℂ × ℂ)).prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact hFI
    rw [Measure.volume_eq_prod (ℂ × ℂ) ℂ, setIntegral_prod _ hFI', Measure.restrict_univ]

  have h2 : ∀ α : ℂ × ℂ, ∫ z, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) * secF φ a₁ a₂ h α z =
      ((|a₁ - a₂|⁻¹ : ℝ) : ℂ) * ∫ v, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) *
        φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (kU α)) := by
    intro α
    have hsub := Substitution.integral_comp_twistShear a₁ a₂ h.1 h.2 hne
      (fun v => φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (kU α)))
    rw [integral_const_mul, integral_const_mul]
    simp only [secF]
    rw [hsub, Complex.real_smul]
    ring

  have h3 : ∫ α in aSet, ∫ v, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) *
      φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (kU α)) =
      ∫ v, ∫ α in aSet, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) *
        φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (kU α)) := by
    have hGI' : Integrable (fun σ : (ℂ × ℂ) × ℂ => (2 * Real.sin σ.1.1.im * Real.cos σ.1.1.im : ℂ) *
        φ ((kU σ.1)⁻¹ * twistedSplitElt a₁ a₂ σ.2 h * conjEntries (kU σ.1)))
        ((volume.restrict aSet).prod (volume.restrict (Set.univ : Set ℂ))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hGI
    have hsw := integral_integral_swap (show Integrable (Function.uncurry fun (α : ℂ × ℂ) (z : ℂ) =>
        (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) * φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ z h * conjEntries (kU α)))
      ((volume.restrict aSet).prod (volume.restrict (Set.univ : Set ℂ))) from hGI')
    rw [Measure.restrict_univ] at hsw
    exact hsw

  have h4 : ∀ v : ℂ, ∫ α in aSet, (2 * Real.sin α.1.im * Real.cos α.1.im : ℂ) *
      φ ((kU α)⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries (kU α)) =
      ((4 * Real.pi ^ 3 : ℝ) : ℂ) * unitaryAverage fun k => φ (k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k) := by
    intro v
    have hFv : Continuous fun k : GL (Fin 2) ℂ => φ (k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k) :=
      hφ.comp ((continuous_inv.mul continuous_const).mul (TwistedTorus.Rid.continuous_glMap Complex.continuous_conj))
    exact window_integral _ hFv
  have h5 : twistedSplitTransform φ a₁ a₂ =
      ∫ v : ℂ, unitaryAverage fun k => φ (k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k) := by
    unfold twistedSplitTransform
    rw [dif_pos h]
  rw [h1]
  simp_rw [h2]
  rw [integral_const_mul, h3]
  simp_rw [h4]
  rw [integral_const_mul, h5]
  push_cast
  ring

private theorem split_core (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (a₁ a₂ : ℝ) (h : 0 < a₁ ∧ 0 < a₂) (hne : a₁ ≠ a₂) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)])
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) (c : NNReal)
    (hμc : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) HaarRef.glOfℂ HaarRef.refMeasureℂ)
    (hKS : Measure.map ksChart ((volume.restrict ksDom).withDensity ksJ) = volume.restrict ksLocus)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun α : ℝ × ℝ => if hα : α.1 * α.2 ≠ 0 then upperTriangular α.1 α.2 0 hα else 1)
        ((volume.restrict {α : ℝ × ℝ | α.1 * α.2 ≠ 0}).withDensity
          (fun α => ENNReal.ofReal |α.1 * α.2|⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w) :
    ∫ x, (fun y => φ (TwistedTorus.Rid.ridGL y)) (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) * (w x : ℂ) ∂μ =
      (((4 * Real.pi ^ 3 * c / cT : ℝ)) : ℂ) * twistedSplitTransform φ a₁ a₂ / (((4 * |a₁ - a₂| : ℝ)) : ℂ) := by
  have hcT' : ((cT : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'
  have hne' : ((|a₁ - a₂| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.2 (sub_ne_zero.2 hne)).ne'
  obtain ⟨-, hval⟩ := split_transport φ hφ hφc a₁ a₂ h hne δ hδ μ hμ c hμc hKS τ cT hcT hτ w hw
  change ∫ x, orbF φ δ x * (w x : ℂ) ∂μ = _
  rw [hval, section_eval φ hφ hφc a₁ a₂ h hne]
  push_cast
  field_simp

end TwistedOrbit.SplitCore
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit
namespace MuBox

private def muBox : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
  {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
      ((TwistedTorus.Rid.ridGL g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}

private theorem upper_mul_rowIsometry_inj (b₁ b₂ b₁' b₂' : ℝ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₁' : 0 < b₁')
    (hb₂' : 0 < b₂') (w w' : ℂ) (k k' : GL (Fin 2) ℂ) (hk : AutomorphicForm.WindowedSiegel.IsRowIsometry k)
    (hk' : AutomorphicForm.WindowedSiegel.IsRowIsometry k')
    (h : !![(b₁ : ℂ), w; 0, (b₂ : ℂ)] * (k : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(b₁' : ℂ), w'; 0, (b₂' : ℂ)] * (k' : Matrix (Fin 2) (Fin 2) ℂ)) :
    b₁ = b₁' ∧ b₂ = b₂' ∧ w = w' ∧ k = k' := by
  have e : ∀ i j : Fin 2, (!![(b₁ : ℂ), w; 0, (b₂ : ℂ)] * (k : Matrix (Fin 2) (Fin 2) ℂ)) i j =
      (!![(b₁' : ℂ), w'; 0, (b₂' : ℂ)] * (k' : Matrix (Fin 2) (Fin 2) ℂ)) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at e00 e01 e10 e11

  have r0 : (0 : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (b₂ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      (0 : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (b₂' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    linear_combination e10
  have r1 : (0 : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + (b₂ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (0 : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + (b₂' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    linear_combination e11
  have n2 := hk.2 (0 : ℂ) (b₂ : ℂ)
  have n2' := hk'.2 (0 : ℂ) (b₂' : ℂ)
  rw [r0, r1] at n2
  have key2 := n2.symm.trans n2'
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.zero_re, Complex.zero_im, Complex.ofReal_re,
    Complex.ofReal_im] at key2
  have hb2 : b₂ = b₂' := by nlinarith [key2, hb₂, hb₂']
  subst hb2

  have s0 : (b₁ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + w * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      (b₁' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + w' * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    linear_combination e00
  have s1 : (b₁ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + w * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (b₁' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + w' * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    linear_combination e01
  have t0 : (b₁ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (w + b₂) * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      (b₁' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (w' + b₂) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    linear_combination e00 + e10
  have t1 : (b₁ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + (w + b₂) * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (b₁' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + (w' + b₂) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    linear_combination e01 + e11
  have u0 : (b₁ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
        (w + b₂ * Complex.I) * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      (b₁' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
        (w' + b₂ * Complex.I) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    linear_combination e00 + Complex.I * e10
  have u1 : (b₁ : ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 +
        (w + b₂ * Complex.I) * (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (b₁' : ℂ) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 1 +
        (w' + b₂ * Complex.I) * (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    linear_combination e01 + Complex.I * e11
  have m0 := hk.2 (b₁ : ℂ) w
  have m0' := hk'.2 (b₁' : ℂ) w'
  rw [s0, s1] at m0
  have key0 := m0.symm.trans m0'
  have m1 := hk.2 (b₁ : ℂ) (w + b₂)
  have m1' := hk'.2 (b₁' : ℂ) (w' + b₂)
  rw [t0, t1] at m1
  have key1 := m1.symm.trans m1'
  have m2 := hk.2 (b₁ : ℂ) (w + b₂ * Complex.I)
  have m2' := hk'.2 (b₁' : ℂ) (w' + b₂ * Complex.I)
  rw [u0, u1] at m2
  have key3 := m2.symm.trans m2'
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at key0 key1 key3
  have hre : b₂ * (w.re - w'.re) = 0 := by linarith [key0, key1]
  have him : b₂ * (w.im - w'.im) = 0 := by linarith [key0, key3]
  have hw : w = w' := by
    apply Complex.ext
    · exact sub_eq_zero.1 ((mul_eq_zero.1 hre).resolve_left hb₂.ne')
    · exact sub_eq_zero.1 ((mul_eq_zero.1 him).resolve_left hb₂.ne')
  subst hw
  have hb1 : b₁ = b₁' := by nlinarith [key0, hb₁, hb₁']
  subst hb1

  have hb₁c : (b₁ : ℂ) ≠ 0 := by exact_mod_cast hb₁.ne'
  have hb₂c : (b₂ : ℂ) ≠ 0 := by exact_mod_cast hb₂.ne'
  have h10 : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 0 :=
    mul_left_cancel₀ hb₂c (by linear_combination e10)
  have h11 : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (k' : Matrix (Fin 2) (Fin 2) ℂ) 1 1 :=
    mul_left_cancel₀ hb₂c (by linear_combination e11)
  have h00 : (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    mul_left_cancel₀ hb₁c (by linear_combination e00 - w * h10)
  have h01 : (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = (k' : Matrix (Fin 2) (Fin 2) ℂ) 0 1 :=
    mul_left_cancel₀ hb₁c (by linear_combination e01 - w * h11)
  refine ⟨rfl, rfl, rfl, Units.ext ?_⟩
  rw [Matrix.eta_fin_two (k : Matrix (Fin 2) (Fin 2) ℂ), Matrix.eta_fin_two (k' : Matrix (Fin 2) (Fin 2) ℂ), h00,
    h01, h10, h11]

private def uniSet : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | ‖A.det‖ = 1} ∩
    {A | ∀ x y : ℂ, ‖x * A 0 0 + y * A 1 0‖ ^ 2 + ‖x * A 0 1 + y * A 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2}

private theorem coe_mem_uniSet (k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ) :
    ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ∈ uniSet :=
  ⟨k.2.1, k.2.2⟩

private theorem exists_of_mem_uniSet {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ uniSet) :
    ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A := by
  have hdet : A.det ≠ 0 := fun h0 => by
    have h1 : ‖A.det‖ = 1 := hA.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ⟨hA.1, hA.2⟩⟩, rfl⟩

private theorem isClosed_uniSet : IsClosed uniSet := by
  unfold uniSet
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_det.norm continuous_const) ?_
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  exact (((continuous_const.mul (continuous_id.matrix_elem 0 0)).add
      (continuous_const.mul (continuous_id.matrix_elem 1 0))).norm.pow 2).add
    (((continuous_const.mul (continuous_id.matrix_elem 0 1)).add
      (continuous_const.mul (continuous_id.matrix_elem 1 1))).norm.pow 2)

private theorem norm_entry_le_of_mem_uniSet {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ uniSet) (i j : Fin 2) :
    ‖A i j‖ ≤ 1 := by
  have h0 := hA.2 1 0
  have h1 := hA.2 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero] at h0 h1
  fin_cases i <;> fin_cases j
  · exact (by nlinarith [norm_nonneg (A 0 0), norm_nonneg (A 0 1), h0] : ‖A 0 0‖ ≤ 1)
  · exact (by nlinarith [norm_nonneg (A 0 0), norm_nonneg (A 0 1), h0] : ‖A 0 1‖ ≤ 1)
  · exact (by nlinarith [norm_nonneg (A 1 0), norm_nonneg (A 1 1), h1] : ‖A 1 0‖ ≤ 1)
  · exact (by nlinarith [norm_nonneg (A 1 0), norm_nonneg (A 1 1), h1] : ‖A 1 1‖ ≤ 1)

private theorem isCompact_uniSet : IsCompact uniSet := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset isClosed_uniSet fun A hA => ?_
  refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
  rw [mem_closedBall_zero_iff]
  exact norm_entry_le_of_mem_uniSet hA i j

private def boxParam (q : ((ℝ × ℝ) × (ℝ × ℝ)) × Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.1.1.1 : ℂ), (q.1.1.1 : ℂ) * ((q.1.2.1 : ℂ) + (q.1.2.2 : ℂ) * Complex.I); 0, (q.1.1.2 : ℂ)] * q.2

private def paramBox : Set (((ℝ × ℝ) × (ℝ × ℝ)) × Matrix (Fin 2) (Fin 2) ℂ) :=
  ((Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1)) ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) ×ˢ
    uniSet

private theorem continuous_boxParam : Continuous boxParam := by
  unfold boxParam
  refine Continuous.matrix_mul ?_ continuous_snd
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] <;>
    fun_prop

private theorem isCompact_paramBox : IsCompact paramBox :=
  ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_uniSet

private theorem muBox_eq_preimage :
    muBox =
      (fun g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => ((TwistedTorus.Rid.ridGL g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) ⁻¹'
        (boxParam '' paramBox) := by
  ext g
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, v, hvre, hvim, k, hg⟩
    refine ⟨(((b₁, b₂), (v.re, v.im)), ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)),
      ⟨⟨⟨hb₁, hb₂⟩, ⟨hvre, hvim⟩⟩, coe_mem_uniSet k⟩, ?_⟩
    simp only [boxParam, Complex.re_add_im]
    exact hg.symm
  · rintro ⟨⟨⟨⟨b₁, b₂⟩, ⟨x, y⟩⟩, A⟩, ⟨⟨⟨hb₁, hb₂⟩, ⟨hx, hy⟩⟩, hA⟩, hq⟩
    obtain ⟨k, hk⟩ := exists_of_mem_uniSet hA
    refine ⟨b₁, hb₁, b₂, hb₂, (x : ℂ) + (y : ℂ) * Complex.I, ?_, ?_, k, ?_⟩
    · simpa using hx
    · simpa using hy
    · rw [hk]
      exact hq.symm

private theorem measurableSet_muBox : @MeasurableSet _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) muBox := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  rw [muBox_eq_preimage]
  exact ((isCompact_paramBox.image continuous_boxParam).isClosed.preimage
    (Units.continuous_val.comp TwistedTorus.Rid.continuous_ridGL)).measurableSet

private theorem coe_ridGL_glOfℂ_ksChart {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ SplitCore.ksDom) :
    ((TwistedTorus.Rid.ridGL (HaarRef.glOfℂ (SplitCore.ksChart p)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((p 1 0).re : ℂ), ((p 1 0).re : ℂ) * p 1 1; 0, ((p 1 0).im : ℂ)] *
        ((unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hb : 0 < (p 1 0).re ∧ 0 < (p 1 0).im := ⟨hp.1, hp.2.1⟩
  have hchart : SplitCore.ksChart p = Matrix.of.symm
      (((twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2) ((p 1 0).re * p 1 1) ⟨pow_pos hb.1 2, pow_pos hb.2 2⟩ *
        unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    unfold SplitCore.ksChart
    rw [dif_pos hb]
  rw [hchart, SplitCore.ridGL_glOfℂ_symm_coe, Units.val_mul, Proper.val_twistedSplitElt, Real.sqrt_sq hb.1.le,
    Real.sqrt_sq hb.2.le]

private theorem ksChart_mem_muBox_iff {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ SplitCore.ksDom) :
    HaarRef.glOfℂ (SplitCore.ksChart p) ∈ muBox ↔
      (p 1 0).re ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧ (p 1 0).im ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
        (p 1 1).re ∈ Set.Icc (0 : ℝ) 1 ∧ (p 1 1).im ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, v, hvre, hvim, k, hg⟩
    rw [coe_ridGL_glOfℂ_ksChart hp] at hg
    obtain ⟨h1, h2, h3, -⟩ := upper_mul_rowIsometry_inj (p 1 0).re (p 1 0).im b₁ b₂ hp.1 hp.2.1
      (one_pos.trans_le hb₁.1) (one_pos.trans_le hb₂.1) (((p 1 0).re : ℂ) * p 1 1) ((b₁ : ℂ) * v)
      (unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im) (k : GL (Fin 2) ℂ)
      (AutomorphicForm.WindowedSiegel.mem_rowIsometrySubgroup_iff.1
        (Window.unitaryElt_mem_rowIsometrySubgroup (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im))
      (AutomorphicForm.WindowedSiegel.mem_rowIsometrySubgroup_iff.1 k.2) hg
    have hb₁c : ((p 1 0).re : ℂ) ≠ 0 := by exact_mod_cast hp.1.ne'
    have hv : p 1 1 = v := by
      rw [h1] at h3 hb₁c
      exact mul_left_cancel₀ hb₁c h3
    rw [h1, h2, hv]
    exact ⟨hb₁, hb₂, hvre, hvim⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(p 1 0).re, h1, (p 1 0).im, h2, p 1 1, h3, h4,
      ⟨unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im,
        Window.unitaryElt_mem_rowIsometrySubgroup (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im⟩,
      coe_ridGL_glOfℂ_ksChart hp⟩

private theorem ksChart_preimage_muBox :
    SplitCore.ksDom ∩ SplitCore.ksChart ⁻¹' (HaarRef.glOfℂ ⁻¹' muBox) =
      {p ∈ SplitCore.ksDom | (p 1 0).re ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧ (p 1 0).im ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧
        (p 1 1).re ∈ Set.Icc (0 : ℝ) 1 ∧ (p 1 1).im ∈ Set.Icc (0 : ℝ) 1} := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sep_iff]
  constructor
  · rintro ⟨hp, hmem⟩
    exact ⟨hp, (ksChart_mem_muBox_iff hp).1 hmem⟩
  · rintro ⟨hp, hbox⟩
    exact ⟨hp, (ksChart_mem_muBox_iff hp).2 hbox⟩

private theorem _root_.TwistedOrbit.MuBox.one_le_exp_one : (1 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

p2m_export "TwistedOrbit.MuBox" "one_le_exp_one"
private def tSet : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1))

private def vSet : Set ℂ := Complex.measurableEquivRealProd ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

private theorem mem_tSet_iff (b : ℂ) :
    b ∈ tSet ↔ b.re ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧ b.im ∈ Set.Icc (1 : ℝ) (Real.exp 1) :=
  Iff.rfl

private theorem mem_vSet_iff (v : ℂ) : v ∈ vSet ↔ v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 :=
  Iff.rfl

private theorem measurableSet_tSet : MeasurableSet tSet :=
  Complex.measurableEquivRealProd.measurable (measurableSet_Icc.prod measurableSet_Icc)

private theorem measurableSet_vSet : MeasurableSet vSet :=
  Complex.measurableEquivRealProd.measurable (measurableSet_Icc.prod measurableSet_Icc)

private theorem tSet_subset_bSet : tSet ⊆ TorusSlot.bSet := fun b hb =>
  ⟨one_pos.trans_le ((mem_tSet_iff b).1 hb).1.1, one_pos.trans_le ((mem_tSet_iff b).1 hb).2.1⟩

private def boxP : Set (Fin 2 → Fin 2 → ℂ) :=
  SplitCore.shuf ⁻¹' (tSet ×ˢ ((Set.univ : Set (ℂ × ℂ)) ×ˢ vSet))

private theorem mem_boxP_iff (p : Fin 2 → Fin 2 → ℂ) : p ∈ boxP ↔ p 1 0 ∈ tSet ∧ p 1 1 ∈ vSet := by
  simp only [boxP, Set.mem_preimage, SplitCore.shuf_apply, Set.mem_prod, Set.mem_univ, true_and]

private theorem measurableSet_boxP : MeasurableSet boxP :=
  SplitCore.shuf.measurable (measurableSet_tSet.prod (MeasurableSet.univ.prod measurableSet_vSet))

private theorem boxP_inter_ksDom :
    boxP ∩ SplitCore.ksDom = SplitCore.shuf ⁻¹' (tSet ×ˢ (SplitCore.aSet ×ˢ vSet)) := by
  rw [SplitCore.ksDom_eq_preimage, boxP, ← Set.preimage_inter, Set.prod_inter_prod, Set.prod_inter_prod,
    Set.univ_inter, Set.inter_univ, Set.inter_eq_left.2 tSet_subset_bSet]

private def tF (b : ℂ) : ENNReal := ENNReal.ofReal ((((b.re * b.im) ^ 2) ^ 2)⁻¹ * (b.re ^ 3 * b.im ^ 3))

private def aF (α : ℂ) : ENNReal := ENNReal.ofReal (2 * (Real.sin α.im * Real.cos α.im))

private theorem measurable_tF : Measurable tF := by
  unfold tF
  exact ((((Complex.measurable_re.mul Complex.measurable_im).pow_const 2).pow_const 2).inv.mul
    ((Complex.measurable_re.pow_const 3).mul (Complex.measurable_im.pow_const 3))).ennreal_ofReal

private theorem measurable_aF : Measurable aF := by
  unfold aF
  exact (measurable_const.mul ((Real.measurable_sin.comp Complex.measurable_im).mul
    (Real.measurable_cos.comp Complex.measurable_im))).ennreal_ofReal

private theorem density_eq_indicator {p : Fin 2 → Fin 2 → ℂ} (hp : p ∈ SplitCore.ksDom) :
    (SplitCore.ksJ * fun p => (HaarRef.glOfℂ ⁻¹' muBox).indicator HaarRef.densℂ (SplitCore.ksChart p)) p =
      boxP.indicator (fun p : Fin 2 → Fin 2 → ℂ => tF (p 1 0) * aF (p 0 0)) p := by
  have hiff : SplitCore.ksChart p ∈ HaarRef.glOfℂ ⁻¹' muBox ↔ p ∈ boxP := by
    rw [Set.mem_preimage, ksChart_mem_muBox_iff hp, mem_boxP_iff, mem_tSet_iff, mem_vSet_iff]
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [Pi.mul_apply]
  by_cases hm : p ∈ boxP
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
    have hb₁ : 0 < (p 1 0).re := hp.1
    have hb₂ : 0 < (p 1 0).im := hp.2.1
    have hJ : SplitCore.ksJ p = ENNReal.ofReal
        (2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im) := rfl
    have hD : HaarRef.densℂ (SplitCore.ksChart p) = ENNReal.ofReal (((((p 1 0).re * (p 1 0).im) ^ 2) ^ 2)⁻¹) := by
      rw [← SplitCore.densℂ_ksChart hp, ENNReal.ofReal_toReal (HaarRef.densℂ_lt_top _).ne]
    have hnn : (0 : ℝ) ≤ ((((p 1 0).re * (p 1 0).im) ^ 2) ^ 2)⁻¹ := by positivity
    have hnn' : (0 : ℝ) ≤ ((((p 1 0).re * (p 1 0).im) ^ 2) ^ 2)⁻¹ * ((p 1 0).re ^ 3 * (p 1 0).im ^ 3) := by
      positivity
    rw [hJ, hD, mul_comm, ← ENNReal.ofReal_mul hnn]
    unfold tF aF
    rw [← ENNReal.ofReal_mul hnn']
    congr 1
    ring
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.1 h)), mul_zero]

private theorem lintegral_prod_set {X Y : Type*} [MeasureSpace X] [MeasureSpace Y] [SigmaFinite (volume : Measure X)]
    [SigmaFinite (volume : Measure Y)] (f : X → ENNReal) (g : Y → ENNReal) (hf : Measurable f) (hg : Measurable g)
    (s : Set X) (t : Set Y) : ∫⁻ z in s ×ˢ t, f z.1 * g z.2 = (∫⁻ x in s, f x) * ∫⁻ y in t, g y := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable hg.aemeasurable]

private theorem lintegral_Icc_one_exp_ofReal_inv :
    ∫⁻ x in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal x⁻¹ = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) := by
    refine continuousOn_inv₀.mono ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (lt_of_lt_of_le one_pos hx.1).ne'
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) (Real.exp 1))] fun x : ℝ => x⁻¹ :=
    ae_restrict_of_forall_mem measurableSet_Icc fun x hx => inv_nonneg.2 (zero_le_one.trans hx.1)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le one_le_exp_one, integral_inv_of_pos one_pos (Real.exp_pos 1), div_one,
    Real.log_exp, ENNReal.ofReal_one]

private theorem tF_integrand (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ENNReal.ofReal ((((x * y) ^ 2) ^ 2)⁻¹ * (x ^ 3 * y ^ 3)) = ENNReal.ofReal x⁻¹ * ENNReal.ofReal y⁻¹ := by
  have hx' : x ≠ 0 := hx.ne'
  have hy' : y ≠ 0 := hy.ne'
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hx.le)]
  congr 1
  field_simp <;> ring

private theorem lintegral_tSet_tF : ∫⁻ b in tSet, tF b = 1 := by
  have hpre : ∫⁻ b in tSet, tF b = ∫⁻ z in Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (1 : ℝ) (Real.exp 1),
      ENNReal.ofReal ((((z.1 * z.2) ^ 2) ^ 2)⁻¹ * (z.1 ^ 3 * z.2 ^ 3)) :=
    Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun z : ℝ × ℝ => ENNReal.ofReal ((((z.1 * z.2) ^ 2) ^ 2)⁻¹ * (z.1 ^ 3 * z.2 ^ 3))) _
  rw [hpre, setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun z hz =>
      tF_integrand z.1 z.2 (one_pos.trans_le hz.1.1) (one_pos.trans_le hz.2.1),
    lintegral_prod_set (fun x : ℝ => ENNReal.ofReal x⁻¹) (fun y : ℝ => ENNReal.ofReal y⁻¹)
      measurable_inv.ennreal_ofReal measurable_inv.ennreal_ofReal,
    lintegral_Icc_one_exp_ofReal_inv, one_mul]

private theorem volume_vSet : volume vSet = 1 := by
  rw [vSet, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

private theorem lintegral_Ioo_two_sin_mul_cos :
    ∫⁻ y in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal (2 * (Real.sin y * Real.cos y)) = 1 := by
  have hint : IntegrableOn (fun y : ℝ => 2 * (Real.sin y * Real.cos y)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((by fun_prop : Continuous fun y : ℝ => 2 * (Real.sin y * Real.cos y)).integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))] fun y : ℝ => 2 * (Real.sin y * Real.cos y) :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun y hy => by
      have h1 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1.le (by linarith [hy.2, Real.pi_pos])
      have h2 : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hy.1, Real.pi_pos], hy.2.le⟩
      positivity
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul, integral_sin_mul_cos₁,
    Real.sin_pi_div_two, Real.sin_zero]
  norm_num

private theorem boxA_eq : SplitCore.boxA = Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := rfl

private theorem boxB_eq : SplitCore.boxB = Set.Ioo (0 : ℝ) (2 * Real.pi) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) := rfl

private theorem lintegral_aSet_aF : ∫⁻ α in SplitCore.aSet, aF α.1 = ENNReal.ofReal (4 * Real.pi ^ 3) := by
  have hpre : ∫⁻ α in SplitCore.aSet, aF α.1 = ∫⁻ y in SplitCore.boxA ×ˢ SplitCore.boxB,
      ENNReal.ofReal (2 * (Real.sin y.1.2 * Real.cos y.1.2)) := by
    rw [SplitCore.aSet_eq_preimage]
    exact SplitCore.measurePreserving_angEquiv.setLIntegral_comp_preimage_emb
      SplitCore.angEquiv.measurableEmbedding
      (fun y : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (2 * (Real.sin y.1.2 * Real.cos y.1.2))) _
  have hm : Measurable fun a : ℝ × ℝ => ENNReal.ofReal (2 * (Real.sin a.2 * Real.cos a.2)) :=
    (measurable_const.mul ((Real.measurable_sin.comp measurable_snd).mul
      (Real.measurable_cos.comp measurable_snd))).ennreal_ofReal
  have hm' : Measurable fun y : ℝ => ENNReal.ofReal (2 * (Real.sin y * Real.cos y)) :=
    (measurable_const.mul (Real.measurable_sin.mul Real.measurable_cos)).ennreal_ofReal
  have houter := lintegral_prod_set (fun a : ℝ × ℝ => ENNReal.ofReal (2 * (Real.sin a.2 * Real.cos a.2)))
    (fun _ : ℝ × ℝ => (1 : ENNReal)) hm measurable_const SplitCore.boxA SplitCore.boxB
  simp only [mul_one, setLIntegral_one] at houter
  have hinner := lintegral_prod_set (fun _ : ℝ => (1 : ENNReal))
    (fun y : ℝ => ENNReal.ofReal (2 * (Real.sin y * Real.cos y))) measurable_const hm'
    (Set.Ioo (0 : ℝ) Real.pi) (Set.Ioo (0 : ℝ) (Real.pi / 2))
  simp only [one_mul, setLIntegral_one] at hinner
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [hpre, houter, boxA_eq, hinner, lintegral_Ioo_two_sin_mul_cos, mul_one, Real.volume_Ioo, sub_zero, boxB_eq,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul h2π,
    ← ENNReal.ofReal_mul hπ]
  congr 1
  ring

private theorem refMeasureℂ_preimage_muBox
    (hKS : Measure.map SplitCore.ksChart ((volume.restrict SplitCore.ksDom).withDensity SplitCore.ksJ) =
      volume.restrict SplitCore.ksLocus) :
    HaarRef.refMeasureℂ (HaarRef.glOfℂ ⁻¹' muBox) = ENNReal.ofReal (4 * Real.pi ^ 3) := by
  have hE : MeasurableSet (HaarRef.glOfℂ ⁻¹' muBox) := HaarRef.measurable_glOfℂ measurableSet_muBox
  unfold HaarRef.refMeasureℂ
  rw [withDensity_apply _ hE, ← lintegral_indicator hE, ← SplitCore.ksLocus_eq_regSetℂ, ← hKS,
    lintegral_map (HaarRef.measurable_densℂ.indicator hE) SplitCore.measurable_ksChart,
    lintegral_withDensity_eq_lintegral_mul _ SplitCore.measurable_ksJ
      ((HaarRef.measurable_densℂ.indicator hE).fun_comp SplitCore.measurable_ksChart),
    setLIntegral_congr_fun SplitCore.measurableSet_ksDom fun p hp => density_eq_indicator hp,
    lintegral_indicator measurableSet_boxP, Measure.restrict_restrict measurableSet_boxP, boxP_inter_ksDom]
  have hpre : ∫⁻ p in SplitCore.shuf ⁻¹' (tSet ×ˢ (SplitCore.aSet ×ˢ vSet)), tF (p 1 0) * aF (p 0 0) =
      ∫⁻ q in tSet ×ˢ (SplitCore.aSet ×ˢ vSet), tF q.1 * aF q.2.1.1 :=
    SplitCore.measurePreserving_shuf.setLIntegral_comp_preimage_emb SplitCore.shuf.measurableEmbedding
      (fun q : ℂ × ((ℂ × ℂ) × ℂ) => tF q.1 * aF q.2.1.1) _
  have hinner := lintegral_prod_set (fun α : ℂ × ℂ => aF α.1) (fun _ : ℂ => (1 : ENNReal))
    (measurable_aF.comp measurable_fst) measurable_const SplitCore.aSet vSet
  simp only [mul_one, setLIntegral_one] at hinner
  rw [hpre, lintegral_prod_set tF (fun r : (ℂ × ℂ) × ℂ => aF r.1.1) measurable_tF
      (measurable_aF.comp (measurable_fst.comp measurable_fst)),
    lintegral_tSet_tF, one_mul, hinner, lintegral_aSet_aF, volume_vSet, mul_one]

private theorem toReal_muBox (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ))) (c : NNReal)
    (hμc : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) HaarRef.glOfℂ HaarRef.refMeasureℂ)
    (hKS : Measure.map SplitCore.ksChart ((volume.restrict SplitCore.ksDom).withDensity SplitCore.ksJ) =
      volume.restrict SplitCore.ksLocus) :
    (μ muBox).toReal = 4 * Real.pi ^ 3 * c := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  have h4 : (0 : ℝ) ≤ 4 * Real.pi ^ 3 := by positivity
  rw [hμc, Measure.smul_apply, Measure.map_apply HaarRef.measurable_glOfℂ measurableSet_muBox,
    refMeasureℂ_preimage_muBox hKS, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal h4]
  ring

end TwistedOrbit.MuBox
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TwistedOrbit
namespace EllCore

private def sC (ε : ℝ) (hε : ε ≠ 0) : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) :=
  HaarRef.glOfℂ (Matrix.of.symm ((Orbit.cayley ε hε : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))

private theorem ridGL_sC (ε : ℝ) (hε : ε ≠ 0) : TwistedTorus.Rid.ridGL (sC ε hε) = Orbit.cayley ε hε :=
  SplitCore.ridGL_glOfℂ_symm_coe _

private def orbA (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : ℂ :=
  φ ((TwistedTorus.Rid.ridGL x)⁻¹ * Orbit.antidiag r α hr * conjEntries (TwistedTorus.Rid.ridGL x))

private theorem orbit_sC_mul (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε : ε ≠ 0)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε) = Orbit.antidiag r α hr)
    (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    (fun y => φ (TwistedTorus.Rid.ridGL y)) ((sC ε hε * x)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (sC ε hε * x)) =
      orbA φ r α hr x := by
  show φ (TwistedTorus.Rid.ridGL ((sC ε hε * x)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (sC ε hε * x))) =
    orbA φ r α hr x
  unfold orbA
  rw [SplitCore.ridGL_orbit, map_mul, ridGL_sC, mul_inv_rev, Orbit.conjEntries_mul, ← hA]
  exact congrArg φ (by simp only [mul_assoc])

private def scalarGL (c : ℝ) (hc : c ≠ 0) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(c : ℂ), 0; 0, (c : ℂ)]
    (by
      rw [Matrix.det_fin_two_of]
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      first
        | (simpa using hc')
        | (simpa using mul_ne_zero hc' hc'))

private theorem coe_scalarGL (c : ℝ) (hc : c ≠ 0) :
    ((scalarGL c hc : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![(c : ℂ), 0; 0, (c : ℂ)] :=
  rfl

private theorem coe_conj_scalarGL (c : ℝ) (hc : c ≠ 0) :
    ((conjEntries (scalarGL c hc) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![(c : ℂ), 0; 0, (c : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Orbit.conjEntries_apply, coe_scalarGL]

private theorem conjEntries_scalarGL (c : ℝ) (hc : c ≠ 0) : conjEntries (scalarGL c hc) = scalarGL c hc :=
  Units.ext (coe_conj_scalarGL c hc)

private theorem scalar_mul_antidiag_eq (c p q : ℂ) :
    !![c, 0; 0, c] * !![0, p; q, 0] = !![0, p; q, 0] * !![c, 0; 0, c] := by
  have h00 : c * 0 + 0 * q = 0 * c + p * 0 := by ring
  have h01 : c * p + 0 * 0 = 0 * 0 + p * c := by ring
  have h10 : 0 * 0 + c * q = q * c + 0 * 0 := by ring
  have h11 : 0 * p + c * 0 = q * 0 + 0 * c := by ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem scalarGL_mul_antidiag (c : ℝ) (hc : c ≠ 0) (r α : ℝ) (hr : 0 < r) :
    scalarGL c hc * Orbit.antidiag r α hr = Orbit.antidiag r α hr * scalarGL c hc := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_scalarGL, Orbit.coe_antidiag]
  exact scalar_mul_antidiag_eq _ _ _

private theorem diag_mul_unipotent_eq (b₁ b₂ ρ z : ℂ) (h : b₁ = b₂ * ρ) :
    !![b₁, 0; 0, b₂] * !![1, z; 0, 1] = !![b₂, 0; 0, b₂] * !![ρ, ρ * z; 0, 1] := by
  have h00 : b₁ * 1 + 0 * 0 = b₂ * ρ + 0 * 0 := by linear_combination h
  have h01 : b₁ * z + 0 * 1 = b₂ * (ρ * z) + 0 * 1 := by linear_combination z * h
  have h10 : 0 * 1 + b₂ * 0 = 0 * ρ + b₂ * 0 := by ring
  have h11 : 0 * z + b₂ * 1 = 0 * (ρ * z) + b₂ * 1 := by ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem ridGL_torA_mul_secY (b : ℝ × ℝ) (hb₁ : 0 < b.1) (hb₂ : 0 < b.2) (α : ℂ × ℂ) (z : ℂ) :
    TwistedTorus.Rid.ridGL (SplitCore.torA b * SplitCore.secY α z) =
      scalarGL b.2 hb₂.ne' * Orbit.shear (b.1 / b.2) z (div_pos hb₁ hb₂) * SplitCore.kU α := by
  rw [map_mul, SplitCore.ridGL_secY, ← mul_assoc]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, SplitCore.coe_ridGL_torA b (mul_ne_zero hb₁.ne' hb₂.ne'), Orbit.coe_unipotent,
    coe_scalarGL, Orbit.coe_shear]
  have hb₂' : (b.2 : ℂ) ≠ 0 := by exact_mod_cast hb₂.ne'
  refine diag_mul_unipotent_eq _ _ _ _ ?_
  first
    | (push_cast; field_simp; done)
    | (push_cast; field_simp; ring)
    | (rw [Complex.ofReal_div, mul_div_cancel₀ _ hb₂'])

private theorem phase_mul_eq (a X Y c e ei : ℂ) :
    !![e, 0; 0, ei] * !![a, X; Y, c] = !![e * a, e * X; ei * Y, ei * c] := by
  have h00 : e * a + 0 * Y = e * a := by ring
  have h01 : e * X + 0 * c = e * X := by ring
  have h10 : 0 * a + ei * Y = ei * Y := by ring
  have h11 : 0 * X + ei * c = ei * c := by ring
  rw [Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem turn_eq (a X Y c a' c' e ei : ℂ) (he : e * ei = 1) (ha : a' = e * e * a) (hc : c' = ei * ei * c) :
    !![e, 0; 0, ei] * !![a, X; Y, c] * !![e, 0; 0, ei] = !![a', X; Y, c'] := by
  have h00 : e * a * e + e * X * 0 = a' := by rw [ha]; ring
  have h01 : e * a * 0 + e * X * ei = X := by linear_combination X * he
  have h10 : ei * Y * e + ei * c * 0 = Y := by linear_combination Y * he
  have h11 : ei * Y * 0 + ei * c * ei = c' := by rw [hc]; ring
  rw [phase_mul_eq, Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem phase_mul_conj_eq (e ei : ℂ) (he : e * ei = 1) :
    !![e, 0; 0, ei] * !![ei, 0; 0, e] = !![1, 0; 0, 1] := by
  have h00 : e * ei + 0 * 0 = 1 := by linear_combination he
  have h01 : e * 0 + 0 * e = 0 := by ring
  have h10 : 0 * ei + ei * 0 = 0 := by ring
  have h11 : 0 * 0 + ei * e = 1 := by linear_combination he
  rw [Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem coe_conj_phase (ψ : ℝ) :
    ((conjEntries (unitaryElt 0 0 ψ 0) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (-(ψ * Complex.I)), 0; 0, Complex.exp (ψ * Complex.I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | (simp [Orbit.conjEntries_apply, Window.coe_unitaryElt_zero_zero, Proper.conj_exp_mul_I,
          Proper.conj_exp_neg_mul_I]; done)
      | (simp only [Orbit.conjEntries_apply, Window.coe_unitaryElt_zero_zero, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
          Fin.zero_eta, Fin.mk_one, Fin.isValue, map_zero, Proper.conj_exp_mul_I,
          Proper.conj_exp_neg_mul_I]; done)

private theorem phase_mul_conjEntries_phase (ψ : ℝ) :
    unitaryElt 0 0 ψ 0 * conjEntries (unitaryElt 0 0 ψ 0) = 1 := by
  apply Units.ext
  rw [Units.val_mul, Window.coe_unitaryElt_zero_zero, coe_conj_phase, Units.val_one, Matrix.one_fin_two]
  exact phase_mul_conj_eq _ _ (Window.exp_mul_I_mul_exp_neg_mul_I ψ)

private theorem phase_mul_twistedEllipticElt_mul_phase (r α ρ : ℝ) (z : ℂ) (hr : 0 < r) (hρ : 0 < ρ) (ψ : ℝ) :
    unitaryElt 0 0 ψ 0 * twistedEllipticElt r α ρ z hr hρ * unitaryElt 0 0 ψ 0 =
      twistedEllipticElt r α ρ (Complex.exp (2 * ψ * Complex.I) * z) hr hρ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Window.coe_unitaryElt_zero_zero, Orbit.coe_twistedEllipticElt,
    Orbit.coe_twistedEllipticElt, Complex.normSq_mul, FibreShift.normSq_exp_two_mul, one_mul,
    Window.exp_two_mul_mul_I]
  refine turn_eq _ _ _ _ _ _ _ _ (Window.exp_mul_I_mul_exp_neg_mul_I ψ) ?_ ?_
  · ring
  · rw [map_mul, map_mul, Proper.conj_exp_mul_I]
    ring

private theorem kU_advance (ψ : ℝ) (p : ℂ × ℂ) :
    SplitCore.kU (p.1, p.2 + (ψ : ℂ) * (1 + Complex.I)) = unitaryElt 0 0 ψ 0 * SplitCore.kU p := by
  have hre : (p.2 + (ψ : ℂ) * (1 + Complex.I)).re = p.2.re + ψ := by
    first
      | (simp; done)
      | (simp; ring)
  have him : (p.2 + (ψ : ℂ) * (1 + Complex.I)).im = p.2.im + ψ := by
    first
      | (simp; done)
      | (simp; ring)
  show unitaryElt p.1.re p.1.im (p.2 + (ψ : ℂ) * (1 + Complex.I)).re (p.2 + (ψ : ℂ) * (1 + Complex.I)).im =
    unitaryElt 0 0 ψ 0 * unitaryElt p.1.re p.1.im p.2.re p.2.im
  rw [hre, him, Window.unitaryElt_zero_zero_mul]

private theorem integral_translate (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε : ε ≠ 0)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε) = Orbit.antidiag r α hr)
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) :
    ∫ x, (fun y => φ (TwistedTorus.Rid.ridGL y)) (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) * (w x : ℂ) ∂μ =
      ∫ x, orbA φ r α hr x * (w (sC ε hε * x) : ℂ) ∂μ := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI := hμ

  have hpt : ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      φ (TwistedTorus.Rid.ridGL ((sC ε hε * x)⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (sC ε hε * x))) =
        orbA φ r α hr x := by
    intro x
    unfold orbA
    rw [SplitCore.ridGL_orbit, map_mul, ridGL_sC, mul_inv_rev, Orbit.conjEntries_mul, ← hA]
    exact congrArg φ (by simp only [mul_assoc])

  have h := integral_mul_left_eq_self (μ := μ)
    (fun x => (fun y => φ (TwistedTorus.Rid.ridGL y)) (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) * (w x : ℂ))
    (sC ε hε)
  refine h.symm.trans ?_
  congr 1
  funext x
  simp only [hpt]

private def ellF (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ρ : ℝ) (σ : (ℂ × ℂ) × ℂ) : ℂ :=
  if hρ : 0 < ρ then φ ((SplitCore.kU σ.1)⁻¹ * twistedEllipticElt r α ρ σ.2 hr hρ * conjEntries (SplitCore.kU σ.1))
  else 0

private theorem orbA_torA_mul_secY (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (b : ℝ × ℝ) (hb₁ : 0 < b.1)
    (hb₂ : 0 < b.2) (σ : (ℂ × ℂ) × ℂ) :
    orbA φ r α hr (SplitCore.torA b * SplitCore.secY σ.1 σ.2) = ellF φ r α hr (b.1 / b.2) σ := by
  unfold orbA ellF
  rw [dif_pos (div_pos hb₁ hb₂), ridGL_torA_mul_secY b hb₁ hb₂ σ.1 σ.2]
  congr 1
  have hS : ∀ g : GL (Fin 2) ℂ,
      (scalarGL b.2 hb₂.ne')⁻¹ * (Orbit.antidiag r α hr * (scalarGL b.2 hb₂.ne' * g)) = Orbit.antidiag r α hr * g := by
    intro g
    rw [← mul_assoc (Orbit.antidiag r α hr), ← scalarGL_mul_antidiag, mul_assoc, inv_mul_cancel_left]
  rw [← Orbit.inv_shear_mul_antidiag_mul_conj r α (b.1 / b.2) σ.2 hr (div_pos hb₁ hb₂), Orbit.conjEntries_mul,
    Orbit.conjEntries_mul, conjEntries_scalarGL, mul_inv_rev, mul_inv_rev]
  simp only [mul_assoc, hS]

private def fibreAct (ϱ ψ : ℝ) (b : ℝ × ℝ) (σ : (ℂ × ℂ) × ℂ) : (ℝ × ℝ) × ((ℂ × ℂ) × ℂ) :=
  ((ϱ * b.1, ϱ * b.2), ((σ.1.1, σ.1.2 + (ψ : ℂ) * (1 + Complex.I)), Complex.exp (2 * ψ * Complex.I) * σ.2))

private theorem coe_ridGL_ellipticElt (ϱ ψ : ℝ) (hϱ : 0 < ϱ) :
    ((TwistedTorus.Rid.ridGL (toTensorGL ℝ ℂ ℝ (ellipticElt ϱ ψ hϱ)) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) =
      !![((ϱ * Real.cos ψ : ℝ) : ℂ), ((ϱ * Real.sin ψ : ℝ) : ℂ);
        -((ϱ * Real.sin ψ : ℝ) : ℂ), ((ϱ * Real.cos ψ : ℝ) : ℂ)] := by
  rw [TwistedTorus.Rid.ridGL_toTensorGL, Transfer.coe_ellipticElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem exp_ofReal_mul_I (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I]
  first
    | (push_cast; ring)
    | (push_cast; done)

private theorem exp_neg_ofReal_mul_I (x : ℝ) :
    Complex.exp (-((x : ℂ) * Complex.I)) = ((Real.cos x : ℝ) : ℂ) - ((Real.sin x : ℝ) : ℂ) * Complex.I := by
  rw [neg_mul_eq_neg_mul, ← Complex.ofReal_neg, exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  first
    | (push_cast; ring)
    | (push_cast; done)

private theorem rotation_entry_add (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (ϱ ψ : ℝ) :
    ((ϱ * Real.cos ψ : ℝ) : ℂ) + (ε : ℂ) * ((ϱ * Real.sin ψ : ℝ) : ℂ) * Complex.I =
      (ϱ : ℂ) * Complex.exp (((ε * ψ : ℝ) : ℂ) * Complex.I) := by
  rw [exp_ofReal_mul_I]
  rcases hε with rfl | rfl <;> simp only [one_mul, neg_one_mul, Real.cos_neg, Real.sin_neg] <;> push_cast <;> ring

private theorem rotation_entry_sub (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (ϱ ψ : ℝ) :
    ((ϱ * Real.cos ψ : ℝ) : ℂ) - (ε : ℂ) * ((ϱ * Real.sin ψ : ℝ) : ℂ) * Complex.I =
      (ϱ : ℂ) * Complex.exp (-(((ε * ψ : ℝ) : ℂ) * Complex.I)) := by
  rw [exp_neg_ofReal_mul_I]
  rcases hε with rfl | rfl <;> simp only [one_mul, neg_one_mul, Real.cos_neg, Real.sin_neg] <;> push_cast <;> ring

private theorem phase_mul_phase_neg (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) * Complex.exp (-((x : ℂ) * Complex.I)) = 1 := by
  rw [← Complex.exp_add]
  first
    | (rw [add_neg_cancel, Complex.exp_zero])
    | (simp; done)

private theorem diag_mul_scalar_eq (A B s : ℂ) :
    !![A, 0; 0, B] * !![s, 0; 0, s] = !![s * A, 0; 0, s * B] := by
  have h00 : A * s + 0 * 0 = s * A := by ring
  have h01 : A * 0 + 0 * s = 0 := by ring
  have h10 : 0 * s + B * 0 = 0 := by ring
  have h11 : 0 * 0 + B * s = s * B := by ring
  rw [Matrix.mul_fin_two, h00, h01, h10, h11]

private theorem scaled_turn_eq (p s t u E Ei d₁ d₂ s' t' u' : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (he : E * Ei = 1)
    (hd₁ : d₁ = p * E) (hd₂ : d₂ = p * Ei) (hs' : s' = p * s) (ht' : t' = t) (hu' : u' = E * E * u) :
    !![d₁, 0; 0, d₂] * (!![s, 0; 0, s] * !![t, t * u; 0, 1] * M) =
      !![s', 0; 0, s'] * !![t', t' * u'; 0, 1] * (!![E, 0; 0, Ei] * M) := by
  rw [ht']
  subst hd₁ hd₂ hs' hu'
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, diag_mul_scalar_eq, phase_mul_eq, phase_mul_eq, Matrix.mul_fin_two]
  have h00 : s * (p * E) * t = p * s * t * E + p * s * (t * (E * E * u)) * 0 := by ring
  have h01 : s * (p * E) * (t * u) = p * s * t * 0 + p * s * (t * (E * E * u)) * Ei := by
    linear_combination (-(p * s * t * u * E)) * he
  have h10 : s * (p * Ei) * 0 = p * s * 0 * E + p * s * 1 * 0 := by ring
  have h11 : s * (p * Ei) * 1 = p * s * 0 * 0 + p * s * 1 * Ei := by ring
  rw [h00, h01, h10, h11]

private theorem inv_sC_mul_torus_mul_sC_mul (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hε0 : ε ≠ 0) (ϱ ψ : ℝ) (hϱ : 0 < ϱ)
    (b : ℝ × ℝ) (hb₁ : 0 < b.1) (hb₂ : 0 < b.2) (σ : (ℂ × ℂ) × ℂ) :
    (sC ε hε0)⁻¹ * toTensorGL ℝ ℂ ℝ (ellipticElt ϱ ψ hϱ) * sC ε hε0 * (SplitCore.torA b * SplitCore.secY σ.1 σ.2) =
      SplitCore.torA (fibreAct ϱ (ε * ψ) b σ).1 *
        SplitCore.secY (fibreAct ϱ (ε * ψ) b σ).2.1 (fibreAct ϱ (ε * ψ) b σ).2.2 := by
  apply TwistedTorus.Rid.injective_ridGL
  simp only [fibreAct]
  rw [map_mul, ridGL_torA_mul_secY b hb₁ hb₂ σ.1 σ.2, map_mul, map_mul, map_inv, ridGL_sC,
    ridGL_torA_mul_secY (ϱ * b.1, ϱ * b.2) (mul_pos hϱ hb₁) (mul_pos hϱ hb₂), kU_advance]
  apply Units.ext
  rw [Units.val_mul, Orbit.coe_inv_cayley_mul_torus_mul_cayley (ϱ * Real.cos ψ) (ϱ * Real.sin ψ) ε hε
    (Orbit.cayley ε hε0) _ (Orbit.coe_cayley ε hε0) (coe_ridGL_ellipticElt ϱ ψ hϱ)]
  simp only [Units.val_mul, coe_scalarGL, Orbit.coe_shear, Window.coe_unitaryElt_zero_zero]
  have hϱ0 : ϱ ≠ 0 := hϱ.ne'
  have hb20 : b.2 ≠ 0 := hb₂.ne'
  have ht : ((ϱ * b.1 / (ϱ * b.2) : ℝ) : ℂ) = ((b.1 / b.2 : ℝ) : ℂ) := by
    congr 1
    first
      | (field_simp; done)
      | (field_simp; ring)
  have hu : Complex.exp (2 * ((ε * ψ : ℝ) : ℂ) * Complex.I) * σ.2 =
      Complex.exp (((ε * ψ : ℝ) : ℂ) * Complex.I) * Complex.exp (((ε * ψ : ℝ) : ℂ) * Complex.I) * σ.2 := by
    have h2 : (2 : ℂ) * ((ε * ψ : ℝ) : ℂ) * Complex.I =
        ((ε * ψ : ℝ) : ℂ) * Complex.I + ((ε * ψ : ℝ) : ℂ) * Complex.I := by ring
    rw [h2, Complex.exp_add]
  exact scaled_turn_eq _ _ _ _ _ _ _ _ _ _ _ _ (phase_mul_phase_neg (ε * ψ)) (rotation_entry_add ε hε ϱ ψ)
    (rotation_entry_sub ε hε ϱ ψ) (Complex.ofReal_mul ϱ b.2) ht hu

private theorem ellF_turn_advance (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ρ ψ : ℝ) (σ : (ℂ × ℂ) × ℂ) :
    ellF φ r α hr ρ ((σ.1.1, σ.1.2 + (ψ : ℂ) * (1 + Complex.I)), Complex.exp (2 * ψ * Complex.I) * σ.2) =
      ellF φ r α hr ρ σ := by
  have hd : ∀ g : GL (Fin 2) ℂ, unitaryElt 0 0 ψ 0 * (conjEntries (unitaryElt 0 0 ψ 0) * g) = g := by
    intro g
    rw [← mul_assoc, phase_mul_conjEntries_phase, one_mul]
  by_cases hρ : 0 < ρ
  ·
    have hA : (SplitCore.kU (σ.1.1, σ.1.2 + (ψ : ℂ) * (1 + Complex.I)))⁻¹ *
          twistedEllipticElt r α ρ (Complex.exp (2 * ψ * Complex.I) * σ.2) hr hρ *
            conjEntries (SplitCore.kU (σ.1.1, σ.1.2 + (ψ : ℂ) * (1 + Complex.I))) =
        (SplitCore.kU σ.1)⁻¹ * twistedEllipticElt r α ρ σ.2 hr hρ * conjEntries (SplitCore.kU σ.1) := by
      rw [← phase_mul_twistedEllipticElt_mul_phase, kU_advance, mul_inv_rev, Orbit.conjEntries_mul]
      simp only [mul_assoc, inv_mul_cancel_left, hd]
    simp only [ellF, dif_pos hρ, hA]
  · simp only [ellF, dif_neg hρ]

private theorem orbA_fibreAct (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ϱ ψ : ℝ) (hϱ : 0 < ϱ) (b : ℝ × ℝ)
    (hb₁ : 0 < b.1) (hb₂ : 0 < b.2) (σ : (ℂ × ℂ) × ℂ) :
    orbA φ r α hr (SplitCore.torA (fibreAct ϱ ψ b σ).1 *
        SplitCore.secY (fibreAct ϱ ψ b σ).2.1 (fibreAct ϱ ψ b σ).2.2) =
      orbA φ r α hr (SplitCore.torA b * SplitCore.secY σ.1 σ.2) := by
  have h₁ : 0 < (fibreAct ϱ ψ b σ).1.1 := mul_pos hϱ hb₁
  have h₂ : 0 < (fibreAct ϱ ψ b σ).1.2 := mul_pos hϱ hb₂
  rw [orbA_torA_mul_secY φ r α hr (fibreAct ϱ ψ b σ).1 h₁ h₂ (fibreAct ϱ ψ b σ).2,
    orbA_torA_mul_secY φ r α hr b hb₁ hb₂ σ]
  have hratio : (fibreAct ϱ ψ b σ).1.1 / (fibreAct ϱ ψ b σ).1.2 = b.1 / b.2 := by
    show ϱ * b.1 / (ϱ * b.2) = b.1 / b.2
    first
      | (rw [mul_div_mul_left _ _ hϱ.ne'])
      | (field_simp)
  rw [hratio]
  exact ellF_turn_advance φ r α hr (b.1 / b.2) ψ σ

private theorem exp_two_mul_add_two_pi_mul_I (ψ : ℝ) :
    Complex.exp (2 * ((ψ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp (2 * (ψ : ℂ) * Complex.I) := by
  have h : 2 * ((ψ + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
      2 * (ψ : ℂ) * Complex.I + 2 * Real.pi * Complex.I + 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, mul_one]

private theorem secY_advance_add_two_pi (p : ℂ × ℂ) (ψ : ℝ) (z : ℂ) :
    SplitCore.secY (p.1, p.2 + ((ψ + 2 * Real.pi : ℝ) : ℂ) * (1 + Complex.I)) z =
      SplitCore.secY (p.1, p.2 + (ψ : ℂ) * (1 + Complex.I)) z := by
  unfold SplitCore.secY
  rw [kU_advance, kU_advance, Window.unitaryElt_add_two_pi_left]

private theorem torA_mul_secY_fibreAct_add_two_pi (ϱ ψ : ℝ) (b : ℝ × ℝ) (σ : (ℂ × ℂ) × ℂ) :
    SplitCore.torA (fibreAct ϱ (ψ + 2 * Real.pi) b σ).1 *
        SplitCore.secY (fibreAct ϱ (ψ + 2 * Real.pi) b σ).2.1 (fibreAct ϱ (ψ + 2 * Real.pi) b σ).2.2 =
      SplitCore.torA (fibreAct ϱ ψ b σ).1 * SplitCore.secY (fibreAct ϱ ψ b σ).2.1 (fibreAct ϱ ψ b σ).2.2 := by
  simp only [fibreAct]
  rw [secY_advance_add_two_pi, exp_two_mul_add_two_pi_mul_I]

private theorem fibre_mass (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hε0 : ε ≠ 0) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) = Orbit.antidiag r α hr)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w)
    (ρ : ℝ) (hρ : 0 < ρ) (σ : (ℂ × ℂ) × ℂ) (hx : orbA φ r α hr (SplitCore.torA (ρ, 1) * SplitCore.secY σ.1 σ.2) ≠ 0) :
    IntegrableOn (fun q : ℝ × ℝ => q.1⁻¹ * w (sC ε hε0 * (SplitCore.torA (fibreAct q.1 q.2 (ρ, 1) σ).1 *
        SplitCore.secY (fibreAct q.1 q.2 (ρ, 1) σ).2.1 (fibreAct q.1 q.2 (ρ, 1) σ).2.2)))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ∧
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), q.1⁻¹ * w (sC ε hε0 *
          (SplitCore.torA (fibreAct q.1 q.2 (ρ, 1) σ).1 *
            SplitCore.secY (fibreAct q.1 q.2 (ρ, 1) σ).2.1 (fibreAct q.1 q.2 (ρ, 1) σ).2.2)) = (cT : ℝ)⁻¹ := by

  have hx' := hx
  rw [← orbit_sC_mul φ r α hr ε hε0 δ hA] at hx'
  obtain ⟨hI, hval⟩ := Transfer.torus_integral_section_elliptic δ τ cT hcT hτ
    (fun y => φ (TwistedTorus.Rid.ridGL y)) w hw (sC ε hε0 * (SplitCore.torA (ρ, 1) * SplitCore.secY σ.1 σ.2)) hx'
  have hS : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hI' : IntegrableOn (fun q : ℝ × ℝ => q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.ellElt q) *
      (sC ε hε0 * (SplitCore.torA (ρ, 1) * SplitCore.secY σ.1 σ.2))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) := hI
  have hval' : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ
      (Transfer.ellElt q) * (sC ε hε0 * (SplitCore.torA (ρ, 1) * SplitCore.secY σ.1 σ.2))) = (cT : ℝ)⁻¹ := hval

  have hpt : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
      toTensorGL ℝ ℂ ℝ (Transfer.ellElt q) * (sC ε hε0 * (SplitCore.torA (ρ, 1) * SplitCore.secY σ.1 σ.2)) =
        sC ε hε0 * (SplitCore.torA (fibreAct q.1 (ε * q.2) (ρ, 1) σ).1 *
          SplitCore.secY (fibreAct q.1 (ε * q.2) (ρ, 1) σ).2.1 (fibreAct q.1 (ε * q.2) (ρ, 1) σ).2.2) := by
    intro q hq
    have hq1 : 0 < q.1 := (Set.mem_prod.mp hq).1
    rw [Transfer.ellElt_apply_of_pos q hq1,
      ← inv_sC_mul_torus_mul_sC_mul ε hε hε0 q.1 q.2 hq1 (ρ, 1) hρ one_pos σ]
    simp only [mul_assoc, mul_inv_cancel_left]
  rcases hε with rfl | rfl
  ·
    refine ⟨hI'.congr_fun (fun q hq => ?_) hS, (setIntegral_congr_fun hS fun q hq => ?_).trans hval'⟩
    · beta_reduce; rw [hpt q hq, one_mul]
    · beta_reduce; rw [hpt q hq, one_mul]
  ·

    let T : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.subLeft (2 * Real.pi))
    have hT1 : ∀ q : ℝ × ℝ, (T q).1 = q.1 := fun q => rfl
    have hT2 : ∀ q : ℝ × ℝ, (T q).2 = 2 * Real.pi - q.2 := fun q => rfl
    have hT : MeasurePreserving T volume volume := by
      have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_sub_left (volume : Measure ℝ) (2 * Real.pi))
      rw [← Measure.volume_eq_prod] at h
      exact h
    have hpre : T ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) =
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
      ext q
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, hT1, hT2]
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨h₁, by linarith, by linarith⟩
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨h₁, by linarith, by linarith⟩

    have hFT : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
        (T q).1⁻¹ * w (sC (-1) hε0 * (SplitCore.torA (fibreAct (T q).1 (T q).2 (ρ, 1) σ).1 *
          SplitCore.secY (fibreAct (T q).1 (T q).2 (ρ, 1) σ).2.1 (fibreAct (T q).1 (T q).2 (ρ, 1) σ).2.2)) =
        q.1⁻¹ * w (toTensorGL ℝ ℂ ℝ (Transfer.ellElt q) *
          (sC (-1) hε0 * (SplitCore.torA (ρ, 1) * SplitCore.secY σ.1 σ.2))) := by
      intro q hq
      rw [hT1, hT2, sub_eq_neg_add, torA_mul_secY_fibreAct_add_two_pi, hpt q hq, neg_one_mul]
    refine ⟨?_, ?_⟩
    · have h1 : IntegrableOn ((fun q : ℝ × ℝ => q.1⁻¹ * w (sC (-1) hε0 *
          (SplitCore.torA (fibreAct q.1 q.2 (ρ, 1) σ).1 *
            SplitCore.secY (fibreAct q.1 q.2 (ρ, 1) σ).2.1 (fibreAct q.1 q.2 (ρ, 1) σ).2.2))) ∘ T)
          (T ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
        rw [hpre]
        exact hI'.congr_fun (fun q hq => (hFT q hq).symm) hS
      exact (hT.integrableOn_comp_preimage T.measurableEmbedding).1 h1
    · have h := hT.setIntegral_preimage_emb T.measurableEmbedding (fun q : ℝ × ℝ => q.1⁻¹ * w (sC (-1) hε0 *
          (SplitCore.torA (fibreAct q.1 q.2 (ρ, 1) σ).1 *
            SplitCore.secY (fibreAct q.1 q.2 (ρ, 1) σ).2.1 (fibreAct q.1 q.2 (ρ, 1) σ).2.2)))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))
      rw [hpre] at h
      exact h.symm.trans ((setIntegral_congr_fun hS hFT).trans hval')

private def midSwap (α β γ δ : Type*) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ) :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl α).prodCongr
        (MeasurableEquiv.prodAssoc.symm.trans
          ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl δ)).trans MeasurableEquiv.prodAssoc))).trans
      MeasurableEquiv.prodAssoc.symm)

private theorem midSwap_apply {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (x : (α × β) × (γ × δ)) : midSwap α β γ δ x = ((x.1.1, x.2.1), (x.1.2, x.2.2)) :=
  rfl

private theorem measurePreserving_midSwap (α β γ δ : Type*) [MeasureSpace α] [MeasureSpace β] [MeasureSpace γ]
    [MeasureSpace δ] [SFinite (volume : Measure α)] [SFinite (volume : Measure β)] [SFinite (volume : Measure γ)]
    [SFinite (volume : Measure δ)] : MeasurePreserving (midSwap α β γ δ) volume volume := by
  have h1 := measurePreserving_prodAssoc (volume : Measure α) (volume : Measure β) (volume : Measure (γ × δ))
  have h2 := (MeasurePreserving.id (volume : Measure α)).prod
    ((measurePreserving_prodAssoc (volume : Measure β) (volume : Measure γ) (volume : Measure δ)).symm _)
  have h3 := (MeasurePreserving.id (volume : Measure α)).prod
    ((Measure.measurePreserving_swap (μ := (volume : Measure β)) (ν := (volume : Measure γ))).prod
      (MeasurePreserving.id (volume : Measure δ)))
  have h4 := (MeasurePreserving.id (volume : Measure α)).prod
    (measurePreserving_prodAssoc (volume : Measure γ) (volume : Measure β) (volume : Measure δ))
  have h5 := (measurePreserving_prodAssoc (volume : Measure α) (volume : Measure γ) (volume : Measure (β × δ))).symm
    _
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

private def coords : (Fin 2 → Fin 2 → ℂ) ≃ᵐ ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ) :=
  HaarRef.eqvℂ.trans
    ((((Complex.measurableEquivRealProd.prodCongr Complex.measurableEquivRealProd).prodCongr
        (Complex.measurableEquivRealProd.prodCongr (MeasurableEquiv.refl ℂ))).trans
      (MeasurableEquiv.prodComm.trans
        (((MeasurableEquiv.refl ((ℝ × ℝ) × ℂ)).prodCongr
            (MeasurableEquiv.prodAssoc.symm.trans
              (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℝ)))).trans
          (midSwap (ℝ × ℝ) ℂ (ℝ × (ℝ × ℝ)) ℝ)))))

private theorem coords_apply (p : Fin 2 → Fin 2 → ℂ) :
    coords p = ((((p 1 0).re, (p 1 0).im), ((p 0 1).re, ((p 0 0).re, (p 0 0).im))), (p 1 1, (p 0 1).im)) :=
  rfl

private theorem measurePreserving_coords : MeasurePreserving coords volume volume := by
  have h1 := (Complex.volume_preserving_equiv_real_prod.prod Complex.volume_preserving_equiv_real_prod).prod
    (Complex.volume_preserving_equiv_real_prod.prod (MeasurePreserving.id (volume : Measure ℂ)))
  have h2 := Measure.measurePreserving_swap (μ := (volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))))
    (ν := (volume : Measure ((ℝ × ℝ) × ℂ)))
  have h3 := (MeasurePreserving.id (volume : Measure ((ℝ × ℝ) × ℂ))).prod
    (((Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).prod
        (MeasurePreserving.id (volume : Measure ℝ))).comp
      ((measurePreserving_prodAssoc (volume : Measure (ℝ × ℝ)) (volume : Measure ℝ) (volume : Measure ℝ)).symm _))
  have h4 := measurePreserving_midSwap (ℝ × ℝ) ℂ (ℝ × (ℝ × ℝ)) ℝ
  exact h4.comp (h3.comp (h2.comp (h1.comp HaarRef.measurePreserving_eqvℂ)))

private def arrayOf (b a : ℝ × ℝ) (ξ₁ ξ₂ : ℝ) (z : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![(⟨a.1, a.2⟩ : ℂ), ⟨ξ₁, ξ₂⟩], ![⟨b.1, b.2⟩, z]]

private theorem coords_symm_apply (x : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ)) :
    coords.symm x = arrayOf x.1.1 x.1.2.2 x.1.2.1 x.2.2 x.2.1 := by
  apply coords.injective
  rw [MeasurableEquiv.apply_symm_apply]
  rfl

private def slotWindow : Set (((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ)) :=
  ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ×ˢ (Set.Ioo (0 : ℝ) (2 * Real.pi) ×ˢ SplitCore.boxA)) ×ˢ
    ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))

private theorem measurableSet_boxA : MeasurableSet SplitCore.boxA :=
  (measurableSet_Ioo.prod measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)))

private theorem measurableSet_slotWindow : MeasurableSet slotWindow :=
  ((measurableSet_Ioi.prod measurableSet_Ioi).prod (measurableSet_Ioo.prod measurableSet_boxA)).prod
    (MeasurableSet.univ.prod measurableSet_Ioo)

private theorem ksDom_eq_preimage_coords : SplitCore.ksDom = coords ⁻¹' slotWindow := by
  ext p
  simp only [SplitCore.ksDom, slotWindow, SplitCore.boxA, Set.mem_preimage, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo,
    Set.mem_univ, true_and, Set.mem_setOf_eq, coords_apply]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨⟨⟨h1, h2⟩, ⟨h7, h8⟩, ⟨h3, h4⟩, h5, h6⟩, h9, h10⟩
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h7, h8⟩, ⟨h3, h4⟩, h5, h6⟩, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

private def torusWindow : Set ((ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ))) :=
  (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ×ˢ
    ((Set.Ioo (0 : ℝ) (2 * Real.pi) ×ˢ SplitCore.boxA) ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))

private theorem slotWindow_eq_preimage :
    slotWindow = (MeasurableEquiv.prodAssoc : (((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ)) ≃ᵐ
      (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ))) ⁻¹' torusWindow := by
  ext x
  show x ∈ slotWindow ↔ (x.1.1, (x.1.2, x.2)) ∈ torusWindow
  simp only [slotWindow, torusWindow, Set.mem_prod]
  exact and_assoc

private def fibreCoords : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)) ≃ᵐ (ℝ × ℝ) × (ℝ × ((ℝ × ℝ) × (ℂ × ℝ))) :=
  MeasurableEquiv.prodAssoc.symm.trans
    (((midSwap ℝ ℝ ℝ (ℝ × ℝ)).prodCongr (MeasurableEquiv.refl (ℂ × ℝ))).trans
      (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl (ℝ × ℝ)).prodCongr MeasurableEquiv.prodAssoc)))

private theorem fibreCoords_apply (x : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ))) :
    fibreCoords x = ((x.1.1, x.2.1.1), (x.1.2, (x.2.1.2, x.2.2))) :=
  rfl

private theorem fibreCoords_symm_apply (y : (ℝ × ℝ) × (ℝ × ((ℝ × ℝ) × (ℂ × ℝ)))) :
    fibreCoords.symm y = ((y.1.1, y.2.1), ((y.1.2, y.2.2.1), y.2.2.2)) :=
  rfl

private theorem measurePreserving_fibreCoords : MeasurePreserving fibreCoords volume volume := by
  have h1 := (measurePreserving_prodAssoc (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × (ℝ × ℝ)))
    (volume : Measure (ℂ × ℝ))).symm _
  have h2 := (measurePreserving_midSwap ℝ ℝ ℝ (ℝ × ℝ)).prod (MeasurePreserving.id (volume : Measure (ℂ × ℝ)))
  have h3 := measurePreserving_prodAssoc (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × (ℝ × ℝ)))
    (volume : Measure (ℂ × ℝ))
  have h4 := (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).prod
    (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure (ℝ × ℝ)) (volume : Measure (ℂ × ℝ)))
  exact h4.comp (h3.comp (h2.comp h1))

private def fibreWindow : Set ((ℝ × ℝ) × (ℝ × ((ℝ × ℝ) × (ℂ × ℝ)))) :=
  (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ×ˢ
    (Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))))

private theorem torusWindow_eq_preimage : torusWindow = fibreCoords ⁻¹' fibreWindow := by
  ext x
  show x ∈ torusWindow ↔ ((x.1.1, x.2.1.1), (x.1.2, (x.2.1.2, x.2.2))) ∈ fibreWindow
  simp only [torusWindow, fibreWindow, Set.mem_prod]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨h1, h3⟩, h2, h4, h5⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4, h5⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩

private def slotSwap : (ℝ × ℝ) × (ℂ × ℝ) ≃ᵐ ℂ × ((ℝ × ℝ) × ℝ) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodAssoc)

private theorem slotSwap_apply (x : (ℝ × ℝ) × (ℂ × ℝ)) : slotSwap x = (x.2.1, (x.1, x.2.2)) := rfl

private theorem measurePreserving_slotSwap : MeasurePreserving slotSwap volume volume := by
  have h1 := (measurePreserving_prodAssoc (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) (volume : Measure ℝ)).symm
    _
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℂ))).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have h3 := measurePreserving_prodAssoc (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) (volume : Measure ℝ)
  exact h3.comp (h2.comp h1)

private def eF (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (A : Fin 2 → Fin 2 → ℂ) : ℂ :=
  (HaarRef.densℂ A).toReal • (orbA φ r α hr (HaarRef.glOfℂ A) * (w (sC ε hε0 * HaarRef.glOfℂ A) : ℂ))

private def eKp (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0) (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ)
    (p : Fin 2 → Fin 2 → ℂ) : ℂ :=
  (SplitCore.ksJ p).toReal • eF φ r α hr ε hε0 w (SplitCore.ksChart p)

private theorem measurable_orbA (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r α : ℝ) (hr : 0 < r) (ε : ℝ)
    (hε0 : ε ≠ 0) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) =
      Orbit.antidiag r α hr) :
    @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ (orbA φ r α hr) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  have h : orbA φ r α hr = fun x => SplitCore.orbF φ δ (sC ε hε0 * x) :=
    funext fun x => (orbit_sC_mul φ r α hr ε hε0 δ hA x).symm
  rw [h]
  exact (SplitCore.measurable_orbF φ hφ δ).comp (continuous_const.mul continuous_id).measurable

private theorem measurable_eKp (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r α : ℝ) (hr : 0 < r) (ε : ℝ)
    (hε0 : ε ≠ 0) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) = Orbit.antidiag r α hr)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hwm : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ w) :
    Measurable (eKp φ r α hr ε hε0 w) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  have hs : Measurable fun x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => sC ε hε0 * x := (continuous_const.mul continuous_id).measurable
  have hF : Measurable (eF φ r α hr ε hε0 w) := by
    unfold eF
    exact HaarRef.measurable_densℂ.ennreal_toReal.smul
      (((measurable_orbA φ hφ r α hr ε hε0 δ hA).comp HaarRef.measurable_glOfℂ).mul
        (Complex.measurable_ofReal.comp ((hwm.comp hs).comp HaarRef.measurable_glOfℂ)))
  unfold eKp
  exact SplitCore.measurable_ksJ.ennreal_toReal.smul (hF.comp SplitCore.measurable_ksChart)

private theorem glOfℂ_ksChart_of_pos {p : Fin 2 → Fin 2 → ℂ} (hb₁ : 0 < (p 1 0).re) (hb₂ : 0 < (p 1 0).im) :
    HaarRef.glOfℂ (SplitCore.ksChart p) =
      SplitCore.torA ((p 1 0).re, (p 1 0).im) * SplitCore.secY (p 0 0, p 0 1) (p 1 1) := by
  have hb : ((p 1 0).re, (p 1 0).im).1 * ((p 1 0).re, (p 1 0).im).2 ≠ 0 := mul_ne_zero hb₁.ne' hb₂.ne'
  apply TwistedTorus.Rid.injective_ridGL
  rw [map_mul, SplitCore.ridGL_secY]
  have hc : SplitCore.ksChart p = Matrix.of.symm ((twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2)
      ((p 1 0).re * p 1 1) ⟨pow_pos hb₁ 2, pow_pos hb₂ 2⟩ *
        unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold SplitCore.ksChart
    rw [dif_pos ⟨hb₁, hb₂⟩]
  rw [hc, SplitCore.ridGL_glOfℂ_symm_coe, ← mul_assoc]
  have hk : unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im = SplitCore.kU (p 0 0, p 0 1) := rfl
  rw [hk]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Orbit.coe_twistedSplitElt, SplitCore.coe_ridGL_torA _ hb, Orbit.coe_unipotent,
    Real.sqrt_sq hb₁.le, Real.sqrt_sq hb₂.le]
  have h00 : ((p 1 0).re : ℂ) = ((p 1 0).re : ℂ) * 1 + 0 * 0 := by ring
  have h01 : ((p 1 0).re : ℂ) * p 1 1 = ((p 1 0).re : ℂ) * p 1 1 + 0 * 1 := by ring
  have h10 : (0 : ℂ) = 0 * 1 + ((p 1 0).im : ℂ) * 0 := by ring
  have h11 : ((p 1 0).im : ℂ) = 0 * p 1 1 + ((p 1 0).im : ℂ) * 1 := by ring
  rw [Matrix.mul_fin_two, ← h00, ← h01, ← h10, ← h11]

private theorem densℂ_ksChart_of_pos {p : Fin 2 → Fin 2 → ℂ} (hb₁ : 0 < (p 1 0).re) (hb₂ : 0 < (p 1 0).im) :
    (HaarRef.densℂ (SplitCore.ksChart p)).toReal = ((((p 1 0).re * (p 1 0).im) ^ 2) ^ 2)⁻¹ := by
  have hc : SplitCore.ksChart p = Matrix.of.symm ((twistedSplitElt ((p 1 0).re ^ 2) ((p 1 0).im ^ 2)
      ((p 1 0).re * p 1 1) ⟨pow_pos hb₁ 2, pow_pos hb₂ 2⟩ *
        unitaryElt (p 0 0).re (p 0 0).im (p 0 1).re (p 0 1).im : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    unfold SplitCore.ksChart
    rw [dif_pos ⟨hb₁, hb₂⟩]
  have hE : Complex.normSq (Complex.exp (((p 0 0).re : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hD : Complex.normSq (((Real.sqrt ((p 1 0).re ^ 2) : ℝ) : ℂ) * ((Real.sqrt ((p 1 0).im ^ 2) : ℝ) : ℂ) -
      ((p 1 0).re : ℂ) * p 1 1 * 0) = ((p 1 0).re * (p 1 0).im) ^ 2 := by
    rw [Real.sqrt_sq hb₁.le, Real.sqrt_sq hb₂.le, mul_zero, sub_zero, ← Complex.ofReal_mul, Complex.normSq_ofReal,
      ← sq]
  unfold HaarRef.densℂ
  rw [hc, Equiv.apply_symm_apply, Units.val_mul, Matrix.det_mul, Orbit.coe_twistedSplitElt, Matrix.det_fin_two_of,
    Window.det_coe_unitaryElt, map_mul, map_pow, hE, one_pow, mul_one, hD,
    ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg _))]

private theorem ksJ_toReal_of_pos {p : Fin 2 → Fin 2 → ℂ} (hb₁ : 0 < (p 1 0).re) (hb₂ : 0 < (p 1 0).im)
    (hη0 : 0 < (p 0 0).im) (hηlt : (p 0 0).im < Real.pi / 2) :
    (SplitCore.ksJ p).toReal = 2 * (p 1 0).re ^ 3 * (p 1 0).im ^ 3 * Real.sin (p 0 0).im * Real.cos (p 0 0).im := by
  have hsin : 0 < Real.sin (p 0 0).im := Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (p 0 0).im := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hηlt⟩
  exact ENNReal.toReal_ofReal
    (mul_pos (mul_pos (mul_pos (mul_pos two_pos (pow_pos hb₁ 3)) (pow_pos hb₂ 3)) hsin) hcos).le

private theorem eKp_arrayOf (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (b₁ b₂ : ℝ) (a : ℝ × ℝ) (ξ₁ ξ₂ : ℝ) (z : ℂ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hη0 : 0 < a.2) (hηlt : a.2 < Real.pi / 2) :
    eKp φ r α hr ε hε0 w (arrayOf (b₁, b₂) a ξ₁ ξ₂ z) =
      ((2 * Real.sin a.2 * Real.cos a.2 : ℝ) : ℂ) *
          ellF φ r α hr (b₁ / b₂) ((((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I,
            ((ξ₁ : ℝ) : ℂ) + ((ξ₂ : ℝ) : ℂ) * Complex.I), z) *
        (((b₁ * b₂)⁻¹ * w (sC ε hε0 * (SplitCore.torA (b₁, b₂) *
          SplitCore.secY ((((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I, ((ξ₁ : ℝ) : ℂ) + ((ξ₂ : ℝ) : ℂ) * Complex.I))
            z)) : ℝ) : ℂ) := by
  have e00 : arrayOf (b₁, b₂) a ξ₁ ξ₂ z 0 0 = ⟨a.1, a.2⟩ := rfl
  have e01 : arrayOf (b₁, b₂) a ξ₁ ξ₂ z 0 1 = ⟨ξ₁, ξ₂⟩ := rfl
  have e10 : arrayOf (b₁, b₂) a ξ₁ ξ₂ z 1 0 = ⟨b₁, b₂⟩ := rfl
  have e11 : arrayOf (b₁, b₂) a ξ₁ ξ₂ z 1 1 = z := rfl
  have hb₁' : 0 < (arrayOf (b₁, b₂) a ξ₁ ξ₂ z 1 0).re := hb₁
  have hb₂' : 0 < (arrayOf (b₁, b₂) a ξ₁ ξ₂ z 1 0).im := hb₂
  have hη0' : 0 < (arrayOf (b₁, b₂) a ξ₁ ξ₂ z 0 0).im := hη0
  have hηlt' : (arrayOf (b₁, b₂) a ξ₁ ξ₂ z 0 0).im < Real.pi / 2 := hηlt
  have hbc₁ : (b₁ : ℂ) ≠ 0 := by exact_mod_cast hb₁.ne'
  have hbc₂ : (b₂ : ℂ) ≠ 0 := by exact_mod_cast hb₂.ne'
  unfold eKp eF
  rw [ksJ_toReal_of_pos hb₁' hb₂' hη0' hηlt', densℂ_ksChart_of_pos hb₁' hb₂', glOfℂ_ksChart_of_pos hb₁' hb₂', e00, e01,
    e10, e11]
  show (2 * b₁ ^ 3 * b₂ ^ 3 * Real.sin a.2 * Real.cos a.2) • ((((b₁ * b₂) ^ 2) ^ 2)⁻¹ •
      (orbA φ r α hr (SplitCore.torA (b₁, b₂) * SplitCore.secY ((⟨a.1, a.2⟩ : ℂ), (⟨ξ₁, ξ₂⟩ : ℂ)) z) *
        (w (sC ε hε0 * (SplitCore.torA (b₁, b₂) * SplitCore.secY ((⟨a.1, a.2⟩ : ℂ), (⟨ξ₁, ξ₂⟩ : ℂ)) z)) : ℂ))) = _
  rw [orbA_torA_mul_secY φ r α hr (b₁, b₂) hb₁ hb₂ (((⟨a.1, a.2⟩ : ℂ), (⟨ξ₁, ξ₂⟩ : ℂ)), z), smul_smul,
    Complex.real_smul]
  show (((2 * b₁ ^ 3 * b₂ ^ 3 * Real.sin a.2 * Real.cos a.2 * (((b₁ * b₂) ^ 2) ^ 2)⁻¹) : ℝ) : ℂ) *
      (ellF φ r α hr (b₁ / b₂) (((⟨a.1, a.2⟩ : ℂ), (⟨ξ₁, ξ₂⟩ : ℂ)), z) *
        (w (sC ε hε0 * (SplitCore.torA (b₁, b₂) * SplitCore.secY ((⟨a.1, a.2⟩ : ℂ), (⟨ξ₁, ξ₂⟩ : ℂ)) z)) : ℂ)) = _
  rw [Complex.mk_eq_add_mul_I, Complex.mk_eq_add_mul_I]
  push_cast
  field_simp

private def slotK (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (x : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ)) : ℂ :=
  eKp φ r α hr ε hε0 w (coords.symm x)

private theorem slotK_add_two_pi (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (o : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) (z : ℂ) (ξ : ℝ) :
    slotK φ r α hr ε hε0 w (o, (z, ξ + 2 * Real.pi)) = slotK φ r α hr ε hε0 w (o, (z, ξ)) := by
  unfold slotK
  rw [coords_symm_apply, coords_symm_apply]
  show eKp φ r α hr ε hε0 w (arrayOf o.1 o.2.2 o.2.1 (ξ + 2 * Real.pi) z) =
    eKp φ r α hr ε hε0 w (arrayOf o.1 o.2.2 o.2.1 ξ z)
  have hJ : SplitCore.ksJ (arrayOf o.1 o.2.2 o.2.1 (ξ + 2 * Real.pi) z) =
      SplitCore.ksJ (arrayOf o.1 o.2.2 o.2.1 ξ z) :=
    rfl
  have hC : SplitCore.ksChart (arrayOf o.1 o.2.2 o.2.1 (ξ + 2 * Real.pi) z) =
      SplitCore.ksChart (arrayOf o.1 o.2.2 o.2.1 ξ z) := by
    simp only [SplitCore.ksChart, arrayOf, Matrix.cons_val_zero, Matrix.cons_val_one,
      Window.unitaryElt_add_two_pi_right]
  unfold eKp
  rw [hJ, hC]

private def turnK (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (x : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ)) : ℂ :=
  slotK φ r α hr ε hε0 w (x.1, (Complex.exp (2 * x.1.2.1 * Complex.I) * x.2.1, x.2.2 + x.1.2.1))

private def torK (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (y : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ))) : ℂ :=
  turnK φ r α hr ε hε0 w ((y.1, y.2.1), y.2.2)

private def shearK (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (y : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ))) : ℂ :=
  (y.1.1 : ℂ) * torK φ r α hr ε hε0 w ((y.1.1 * y.1.2, y.1.1), y.2)

private def fibK (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (u : (ℝ × ℝ) × (ℝ × ((ℝ × ℝ) × (ℂ × ℝ)))) : ℂ :=
  shearK φ r α hr ε hε0 w (fibreCoords.symm u)

private def baseK (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (v : ℝ × ((ℝ × ℝ) × (ℂ × ℝ))) : ℂ :=
  (v.1 : ℂ)⁻¹ * ((2 * Real.sin v.2.1.2 * Real.cos v.2.1.2 : ℝ) : ℂ) *
    ellF φ r α hr v.1 ((((v.2.1.1 : ℝ) : ℂ) + ((v.2.1.2 : ℝ) : ℂ) * Complex.I, ((v.2.2.2 : ℝ) : ℂ) * Complex.I),
      v.2.2.1)

private theorem measurable_turnK (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r α : ℝ) (hr : 0 < r) (ε : ℝ)
    (hε0 : ε ≠ 0) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) = Orbit.antidiag r α hr)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hwm : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ w) :
    Measurable (turnK φ r α hr ε hε0 w) := by
  have hT : Continuous fun x : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ) =>
      (x.1, (Complex.exp (2 * x.1.2.1 * Complex.I) * x.2.1, x.2.2 + x.1.2.1)) := by
    fun_prop
  unfold turnK slotK
  exact ((measurable_eKp φ hφ r α hr ε hε0 δ hA w hwm).comp coords.symm.measurable).comp hT.measurable

private theorem measurable_shearK (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r α : ℝ) (hr : 0 < r) (ε : ℝ)
    (hε0 : ε ≠ 0) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) = Orbit.antidiag r α hr)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hwm : @Measurable _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) _ w) :
    Measurable (torK φ r α hr ε hε0 w) ∧ Measurable (shearK φ r α hr ε hε0 w) := by
  have hP : Continuous fun y : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)) => ((y.1, y.2.1), y.2.2) := by fun_prop
  have hS : Continuous fun y : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)) => ((y.1.1 * y.1.2, y.1.1), y.2) := by fun_prop
  have hc : Continuous fun y : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)) => (y.1.1 : ℂ) := by fun_prop
  have h1 : Measurable (torK φ r α hr ε hε0 w) := by
    unfold torK
    exact (measurable_turnK φ hφ r α hr ε hε0 δ hA w hwm).comp hP.measurable
  refine ⟨h1, ?_⟩
  unfold shearK
  exact hc.measurable.mul (h1.comp hS.measurable)

private theorem turn_advance_on_fibres (K : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ) → ℂ) (hKm : Measurable K)
    (hper : ∀ (o : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) (z : ℂ), Function.Periodic (fun ξ : ℝ => K (o, (z, ξ))) (2 * Real.pi))
    (S : Set ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))))
    (hfin : IntegrableOn (fun x : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ) =>
        K (x.1, (Complex.exp (2 * x.1.2.1 * Complex.I) * x.2.1, x.2.2 + x.1.2.1)))
      (S ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) :
    IntegrableOn K (S ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) ∧
      ∫ x in S ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)), K x =
        ∫ x in S ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)),
          K (x.1, (Complex.exp (2 * x.1.2.1 * Complex.I) * x.2.1, x.2.2 + x.1.2.1)) := by
  have hIm : MeasurableSet ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hvol : (volume : Measure (((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ))).restrict
      (S ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) =
        (volume.restrict S).prod (volume.restrict ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
    rw [Measure.volume_eq_prod ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) (ℂ × ℝ), Measure.prod_restrict]
  have hF : Integrable (fun x : ((ℝ × ℝ) × (ℝ × (ℝ × ℝ))) × (ℂ × ℝ) =>
      K (x.1, (Complex.exp (2 * x.1.2.1 * Complex.I) * x.2.1, x.2.2 + x.1.2.1)))
      ((volume.restrict S).prod (volume.restrict ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) := by
    rw [← hvol]
    exact hfin

  have hfib : ∀ o : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)),
      IntegrableOn (fun i : ℂ × ℝ => K (o, (Complex.exp (2 * o.2.1 * Complex.I) * i.1, i.2 + o.2.1)))
        ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) →
      (IntegrableOn (fun i : ℂ × ℝ => K (o, i)) ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ∧
        ∫ i in (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), K (o, i) =
          ∫ i in (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
            K (o, (Complex.exp (2 * o.2.1 * Complex.I) * i.1, i.2 + o.2.1))) ∧
      ∫ i in (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ‖K (o, i)‖ =
        ∫ i in (Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
          ‖K (o, (Complex.exp (2 * o.2.1 * Complex.I) * i.1, i.2 + o.2.1))‖ := by
    intro o ho
    have h0 : 2 * (o.2.1 : ℂ) * Complex.I + 2 * ((-o.2.1 : ℝ) : ℂ) * Complex.I = 0 := by
      push_cast
      ring
    have hback : ∀ i : ℂ × ℝ, K (o, (Complex.exp (2 * o.2.1 * Complex.I) *
        (Complex.exp (2 * ((-o.2.1 : ℝ) : ℂ) * Complex.I) * i.1), i.2 + -o.2.1 + o.2.1)) = K (o, i) := by
      intro i
      rw [neg_add_cancel_right, ← mul_assoc, ← Complex.exp_add, h0, Complex.exp_zero, one_mul]
    have hGper : ∀ z : ℂ, Function.Periodic
        (fun ξ : ℝ => K (o, (Complex.exp (2 * o.2.1 * Complex.I) * z, ξ + o.2.1))) (2 * Real.pi) := by
      intro z ξ
      show K (o, (Complex.exp (2 * o.2.1 * Complex.I) * z, ξ + 2 * Real.pi + o.2.1)) =
        K (o, (Complex.exp (2 * o.2.1 * Complex.I) * z, ξ + o.2.1))
      rw [add_right_comm]
      exact hper o _ (ξ + o.2.1)
    obtain ⟨hI1, hv1⟩ := FibreShift.integral_turn_advance (-o.2.1)
      (fun i : ℂ × ℝ => K (o, (Complex.exp (2 * o.2.1 * Complex.I) * i.1, i.2 + o.2.1))) ho hGper
    have hGn : IntegrableOn
        (fun i : ℂ × ℝ => ((‖K (o, (Complex.exp (2 * o.2.1 * Complex.I) * i.1, i.2 + o.2.1))‖ : ℝ) : ℂ))
        ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) := ho.norm.ofReal
    have hGnper : ∀ z : ℂ, Function.Periodic
        (fun ξ : ℝ => ((‖K (o, (Complex.exp (2 * o.2.1 * Complex.I) * z, ξ + o.2.1))‖ : ℝ) : ℂ)) (2 * Real.pi) := by
      intro z ξ
      show ((‖K (o, (Complex.exp (2 * o.2.1 * Complex.I) * z, ξ + 2 * Real.pi + o.2.1))‖ : ℝ) : ℂ) =
        ((‖K (o, (Complex.exp (2 * o.2.1 * Complex.I) * z, ξ + o.2.1))‖ : ℝ) : ℂ)
      rw [add_right_comm]
      exact congrArg (fun t : ℂ => ((‖t‖ : ℝ) : ℂ)) (hper o (Complex.exp (2 * o.2.1 * Complex.I) * z) (ξ + o.2.1))
    obtain ⟨-, hv2⟩ := FibreShift.integral_turn_advance (-o.2.1) _ hGn hGnper
    have hback' : ∀ i : ℂ × ℝ, ((‖K (o, (Complex.exp (2 * o.2.1 * Complex.I) *
        (Complex.exp (2 * ((-o.2.1 : ℝ) : ℂ) * Complex.I) * i.1), i.2 + -o.2.1 + o.2.1))‖ : ℝ) : ℂ) =
          ((‖K (o, i)‖ : ℝ) : ℂ) := fun i => by
      rw [hback i]
    refine ⟨⟨hI1.congr_fun (fun i _ => hback i) hIm, ((setIntegral_congr_fun hIm fun i _ => (hback i).symm)).trans
      hv1⟩, ?_⟩
    have h := (setIntegral_congr_fun hIm fun i _ => (hback' i).symm).trans hv2
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  have hKae : AEStronglyMeasurable K
      ((volume.restrict S).prod (volume.restrict ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) :=
    hKm.aestronglyMeasurable
  have hslices := hF.prod_right_ae
  have hK : Integrable K
      ((volume.restrict S).prod (volume.restrict ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) := by
    refine (integrable_prod_iff hKae).2 ⟨?_, ?_⟩
    · filter_upwards [hslices] with o ho
      exact (hfib o ho).1.1
    · refine hF.integral_norm_prod_left.congr ?_
      filter_upwards [hslices] with o ho
      exact (hfib o ho).2.symm
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hvol]
    exact hK
  · rw [hvol, integral_prod _ hK, integral_prod _ hF]
    refine integral_congr_ae ?_
    filter_upwards [hslices] with o ho
    exact (hfib o ho).1.2

private theorem scale_shear_on_fibres (K : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)) → ℂ) (hKm : Measurable K)
    (T : Set ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)))
    (hsh : IntegrableOn (fun y : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)) => (y.1.1 : ℂ) * K ((y.1.1 * y.1.2, y.1.1), y.2))
      ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ×ˢ T)) :
    IntegrableOn K ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ×ˢ T) ∧
      ∫ y in (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ×ˢ T, K y =
        ∫ y in (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ×ˢ T, (y.1.1 : ℂ) * K ((y.1.1 * y.1.2, y.1.1), y.2) := by
  have hQ : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := measurableSet_Ioi.prod measurableSet_Ioi
  have hvol : (volume : Measure ((ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)))).restrict
      ((Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ×ˢ T) =
        (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).prod (volume.restrict T) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)), Measure.prod_restrict]
  have hF : Integrable (fun y : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × (ℂ × ℝ)) => (y.1.1 : ℂ) * K ((y.1.1 * y.1.2, y.1.1), y.2))
      ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).prod (volume.restrict T)) := by
    rw [← hvol]
    exact hsh

  have hfib : ∀ t : (ℝ × (ℝ × ℝ)) × (ℂ × ℝ),
      IntegrableOn (fun q : ℝ × ℝ => (q.1 : ℂ) * K ((q.1 * q.2, q.1), t)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) →
      (IntegrableOn (fun b : ℝ × ℝ => K (b, t)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ∧
        ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), K (b, t) =
          ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), (q.1 : ℂ) * K ((q.1 * q.2, q.1), t)) ∧
      ∫ b in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), ‖K (b, t)‖ =
        ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), ‖(q.1 : ℂ) * K ((q.1 * q.2, q.1), t)‖ := by
    intro t ht
    obtain ⟨hiff, hval⟩ := TorusSlot.setIntegral_scaleShear_eq fun b : ℝ × ℝ => K (b, t)
    obtain ⟨-, hvaln⟩ := TorusSlot.setIntegral_scaleShear_eq fun b : ℝ × ℝ => ((‖K (b, t)‖ : ℝ) : ℂ)
    have hn : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ),
        (q.1 : ℂ) * ((‖K ((q.1 * q.2, q.1), t)‖ : ℝ) : ℂ) = ((‖(q.1 : ℂ) * K ((q.1 * q.2, q.1), t)‖ : ℝ) : ℂ) := by
      intro q hq
      have hq1 : 0 < q.1 := (Set.mem_prod.1 hq).1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq1.le]
      push_cast
      ring
    refine ⟨⟨hiff.2 ht, hval⟩, ?_⟩
    have h := hvaln.trans (setIntegral_congr_fun hQ hn)
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  have hKae : AEStronglyMeasurable K
      ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).prod (volume.restrict T)) :=
    hKm.aestronglyMeasurable
  have hslices := hF.prod_left_ae
  have hK : Integrable K ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).prod (volume.restrict T)) := by
    refine (integrable_prod_iff' hKae).2 ⟨?_, ?_⟩
    · filter_upwards [hslices] with t ht
      exact (hfib t ht).1.1
    · refine hF.integral_norm_prod_right.congr ?_
      filter_upwards [hslices] with t ht
      exact (hfib t ht).2.symm
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hvol]
    exact hK
  · rw [hvol, integral_prod_symm _ hK, integral_prod_symm _ hF]
    refine integral_congr_ae ?_
    filter_upwards [hslices] with t ht
    exact (hfib t ht).1.2

private theorem integrableOn_baseK (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (r α : ℝ)
    (hr : 0 < r) (hα : Real.sin α ≠ 0) :
    IntegrableOn (baseK φ r α hr)
      (Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) := by
  obtain ⟨R, ε₀, hε₀, hR⟩ := Proper.exists_bound_elliptic φ hφc r α hr hα
  have hS : MeasurableSet
      (Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) :=
    measurableSet_Ioi.prod (measurableSet_boxA.prod (MeasurableSet.univ.prod measurableSet_Ioo))

  have hP : Continuous fun v : ℝ × ((ℝ × ℝ) × (ℂ × ℝ)) =>
      (((v.2.1.1, (v.2.1.2, ((0 : ℝ), v.2.2.2))) : ℝ × ℝ × ℝ × ℝ), ((v.1, v.2.2.1) : ℝ × ℂ)) := by
    fun_prop
  have hc := (Proper.continuousOn_orbitFactor_elliptic φ hφ r α hr).comp hP.continuousOn (fun v hv => hv)
  have hell : ContinuousOn (fun v : ℝ × ((ℝ × ℝ) × (ℂ × ℝ)) => ellF φ r α hr v.1
      ((((v.2.1.1 : ℝ) : ℂ) + ((v.2.1.2 : ℝ) : ℂ) * Complex.I, ((v.2.2.2 : ℝ) : ℂ) * Complex.I), v.2.2.1))
      {v | 0 < v.1} := by
    refine hc.congr fun v hv => ?_
    have hv' : 0 < v.1 := hv
    simp only [Function.comp_apply, ellF, dif_pos hv', SplitCore.kU, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add]
  have hcont : ContinuousOn (baseK φ r α hr) {v | 0 < v.1} := by
    have h1 : ContinuousOn (fun v : ℝ × ((ℝ × ℝ) × (ℂ × ℝ)) => (v.1 : ℂ)⁻¹) {v | 0 < v.1} :=
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn.inv₀ fun v hv =>
        Complex.ofReal_ne_zero.2 (ne_of_gt hv)
    have h2 : Continuous fun v : ℝ × ((ℝ × ℝ) × (ℂ × ℝ)) =>
        ((2 * Real.sin v.2.1.2 * Real.cos v.2.1.2 : ℝ) : ℂ) := by
      fun_prop
    exact (h1.mul h2.continuousOn).mul hell

  have hK : IsCompact (Set.Icc ε₀ R ×ˢ ((Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ
      (Metric.closedBall (0 : ℂ) R ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)))) :=
    isCompact_Icc.prod ((isCompact_Icc.prod isCompact_Icc).prod ((isCompact_closedBall _ _).prod isCompact_Icc))
  have hKsub : Set.Icc ε₀ R ×ˢ ((Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ
      (Metric.closedBall (0 : ℂ) R ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) ⊆ {v | 0 < v.1} := by
    intro v hv
    exact lt_of_lt_of_le hε₀ (Set.mem_prod.1 hv).1.1
  have hint := (hcont.mono hKsub).integrableOn_compact (μ := volume) hK
  refine hint.of_forall_diff_eq_zero hS ?_
  rintro ⟨ρ, a, z, ξ₂⟩ ⟨hv, hnot⟩
  by_contra hne
  apply hnot
  have hv₁ := Set.mem_prod.1 hv
  have hv₂ := Set.mem_prod.1 hv₁.2
  have hv₃ := Set.mem_prod.1 hv₂.2
  have hρ : 0 < ρ := hv₁.1
  have hξ₂ : ξ₂ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := hv₃.2
  have ha' : a ∈ Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := hv₂.1
  obtain ⟨⟨ha1, ha2⟩, ⟨ha3, ha4⟩⟩ := Set.mem_prod.1 ha'
  have hell0 :
      ellF φ r α hr ρ ((((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I, ((ξ₂ : ℝ) : ℂ) * Complex.I), z) ≠ 0 := by
    intro h0
    apply hne
    show (ρ : ℂ)⁻¹ * ((2 * Real.sin a.2 * Real.cos a.2 : ℝ) : ℂ) *
      ellF φ r α hr ρ ((((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I, ((ξ₂ : ℝ) : ℂ) * Complex.I), z) = 0
    rw [h0, mul_zero]
  have hφne : φ ((SplitCore.kU (((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I, ((ξ₂ : ℝ) : ℂ) * Complex.I))⁻¹ *
      twistedEllipticElt r α ρ z hr hρ *
        conjEntries (SplitCore.kU (((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I, ((ξ₂ : ℝ) : ℂ) * Complex.I))) ≠
      0 := by
    simpa only [ellF, dif_pos hρ] using hell0
  obtain ⟨h1, h2, h3⟩ := hR _ _ _ _ ρ z hρ hφne
  refine Set.mem_prod.2 ⟨⟨h1, h2⟩, Set.mem_prod.2 ⟨Set.mem_prod.2 ⟨⟨ha1.le, ha2.le⟩, ⟨ha3.le, ha4.le⟩⟩,
    Set.mem_prod.2 ⟨mem_closedBall_zero_iff.2 h3, ⟨hξ₂.1.le, hξ₂.2.le⟩⟩⟩⟩

private theorem fibK_apply (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε0 : ε ≠ 0)
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (v : ℝ × ((ℝ × ℝ) × (ℂ × ℝ))) (hρ : 0 < v.1) (hη0 : 0 < v.2.1.2)
    (hηlt : v.2.1.2 < Real.pi / 2) (ϱ ξ₁ : ℝ) (hϱ : 0 < ϱ) (σ : (ℂ × ℂ) × ℂ)
    (hσ : σ = ((((v.2.1.1 : ℝ) : ℂ) + ((v.2.1.2 : ℝ) : ℂ) * Complex.I, ((v.2.2.2 : ℝ) : ℂ) * Complex.I), v.2.2.1)) :
    fibK φ r α hr ε hε0 w ((ϱ, ξ₁), v) =
      baseK φ r α hr v * ((ϱ⁻¹ * w (sC ε hε0 * (SplitCore.torA (fibreAct ϱ ξ₁ (v.1, 1) σ).1 *
        SplitCore.secY (fibreAct ϱ ξ₁ (v.1, 1) σ).2.1 (fibreAct ϱ ξ₁ (v.1, 1) σ).2.2)) : ℝ) : ℂ) := by
  have hϱ' : (ϱ : ℂ) ≠ 0 := by exact_mod_cast hϱ.ne'
  have hρ' : (v.1 : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have e1 : fibK φ r α hr ε hε0 w ((ϱ, ξ₁), v) = (ϱ : ℂ) * eKp φ r α hr ε hε0 w
      (arrayOf (ϱ * v.1, ϱ) v.2.1 ξ₁ (v.2.2.2 + ξ₁) (Complex.exp (2 * ξ₁ * Complex.I) * v.2.2.1)) := by
    simp only [fibK, shearK, torK, turnK, slotK, fibreCoords_symm_apply, coords_symm_apply]
  have h₁ : ((ξ₁ : ℝ) : ℂ) + ((v.2.2.2 + ξ₁ : ℝ) : ℂ) * Complex.I =
      ((v.2.2.2 : ℝ) : ℂ) * Complex.I + (ξ₁ : ℂ) * (1 + Complex.I) := by
    push_cast
    ring
  have h₂ : ellF φ r α hr (ϱ * v.1 / ϱ) ((((v.2.1.1 : ℝ) : ℂ) + ((v.2.1.2 : ℝ) : ℂ) * Complex.I,
      ((ξ₁ : ℝ) : ℂ) + ((v.2.2.2 + ξ₁ : ℝ) : ℂ) * Complex.I), Complex.exp (2 * ξ₁ * Complex.I) * v.2.2.1) =
        ellF φ r α hr v.1 σ := by
    rw [mul_div_cancel_left₀ _ hϱ.ne', h₁, hσ]
    exact ellF_turn_advance φ r α hr v.1 ξ₁
      ((((v.2.1.1 : ℝ) : ℂ) + ((v.2.1.2 : ℝ) : ℂ) * Complex.I, ((v.2.2.2 : ℝ) : ℂ) * Complex.I), v.2.2.1)
  rw [e1, eKp_arrayOf φ r α hr ε hε0 w (ϱ * v.1) ϱ v.2.1 ξ₁ (v.2.2.2 + ξ₁) _ (mul_pos hϱ hρ) hϱ hη0 hηlt, h₂, h₁, hσ]
  unfold baseK
  simp only [fibreAct, mul_one]
  push_cast
  field_simp

private theorem ell_inner (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hε0 : ε ≠ 0) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) = Orbit.antidiag r α hr)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w)
    (v : ℝ × ((ℝ × ℝ) × (ℂ × ℝ))) (hρ : 0 < v.1) (hη0 : 0 < v.2.1.2) (hηlt : v.2.1.2 < Real.pi / 2) :
    IntegrableOn (fun q : ℝ × ℝ => fibK φ r α hr ε hε0 w (q, v)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ∧
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), fibK φ r α hr ε hε0 w (q, v) =
        baseK φ r α hr v * (((cT : ℝ) : ℂ))⁻¹ ∧
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ‖fibK φ r α hr ε hε0 w (q, v)‖ =
        ‖baseK φ r α hr v‖ * (cT : ℝ)⁻¹ := by
  have hw0 : ∀ y, 0 ≤ w y := hw.1
  have hS : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
    measurableSet_Ioi.prod measurableSet_Ioo

  obtain ⟨σ, hσ⟩ : ∃ σ : (ℂ × ℂ) × ℂ,
      σ = ((((v.2.1.1 : ℝ) : ℂ) + ((v.2.1.2 : ℝ) : ℂ) * Complex.I, ((v.2.2.2 : ℝ) : ℂ) * Complex.I), v.2.2.1) :=
    ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℂ, C = baseK φ r α hr v := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ × ℝ → ℝ, g = fun q => q.1⁻¹ * w (sC ε hε0 *
      (SplitCore.torA (fibreAct q.1 q.2 (v.1, 1) σ).1 *
        SplitCore.secY (fibreAct q.1 q.2 (v.1, 1) σ).2.1 (fibreAct q.1 q.2 (v.1, 1) σ).2.2)) := ⟨_, rfl⟩
  have hCell : C = (v.1 : ℂ)⁻¹ * ((2 * Real.sin v.2.1.2 * Real.cos v.2.1.2 : ℝ) : ℂ) * ellF φ r α hr v.1 σ := by
    rw [hC, hσ]
    rfl

  have hK : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), fibK φ r α hr ε hε0 w (q, v) = C * (g q : ℂ) := by
    rintro ⟨ϱ, ξ₁⟩ hq
    rw [hC, hg]
    exact fibK_apply φ r α hr ε hε0 w v hρ hη0 hηlt ϱ ξ₁ (Set.mem_prod.1 hq).1 σ hσ
  have hg0 : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), 0 ≤ g q := fun q hq => by
    rw [hg]
    exact mul_nonneg (inv_nonneg.2 (le_of_lt (Set.mem_prod.1 hq).1)) (hw0 _)
  by_cases hfs : ellF φ r α hr v.1 σ = 0
  · have hC0 : C = 0 := by rw [hCell, hfs, mul_zero]
    refine ⟨?_, ?_, ?_⟩
    · refine integrableOn_zero.congr_fun (fun q hq => ?_) hS
      rw [hK q hq, hC0, zero_mul]
    · rw [setIntegral_congr_fun hS hK, ← hC]
      have h0 : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), C * (g q : ℂ) =
          ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), (0 : ℂ) :=
        setIntegral_congr_fun hS fun q _ => by rw [hC0, zero_mul]
      rw [h0, hC0, zero_mul, integral_zero]
    · have hn : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ‖fibK φ r α hr ε hε0 w (q, v)‖ = (0 : ℝ) :=
        fun q hq => by rw [hK q hq, hC0, zero_mul, norm_zero]
      rw [setIntegral_congr_fun hS hn, ← hC, hC0, norm_zero, zero_mul, integral_zero]
  ·
    have hx : orbA φ r α hr (SplitCore.torA (v.1, 1) * SplitCore.secY σ.1 σ.2) ≠ 0 := by
      rw [orbA_torA_mul_secY φ r α hr (v.1, 1) hρ one_pos σ]
      simpa only [div_one] using hfs
    obtain ⟨hI, hval⟩ := fibre_mass φ r α hr ε hε hε0 δ hA τ cT hcT hτ w hw v.1 hρ σ hx
    have hI' : IntegrableOn g (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
      rw [hg]
      exact hI
    have hval' : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), g q = (cT : ℝ)⁻¹ := by
      rw [hg]
      exact hval
    refine ⟨IntegrableOn.congr_fun (hI'.ofReal.const_mul C) (fun q hq => (hK q hq).symm) hS, ?_, ?_⟩
    · rw [setIntegral_congr_fun hS hK, integral_const_mul, integral_complex_ofReal, hval', ← hC]
      first
        | (push_cast; ring1)
        | push_cast
    · have hn : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ‖fibK φ r α hr ε hε0 w (q, v)‖ = ‖C‖ * g q :=
        fun q hq => by rw [hK q hq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 q hq)]
      rw [setIntegral_congr_fun hS hn, integral_const_mul, hval', ← hC]

private theorem ell_transport (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (r α : ℝ) (hr : 0 < r) (hα : Real.sin α ≠ 0) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hε0 : ε ≠ 0)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) = Orbit.antidiag r α hr)
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) (c : NNReal)
    (hμc : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) HaarRef.glOfℂ HaarRef.refMeasureℂ)
    (hKS : Measure.map SplitCore.ksChart ((volume.restrict SplitCore.ksDom).withDensity SplitCore.ksJ) =
      volume.restrict SplitCore.ksLocus)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w) :
    ∫ x, orbA φ r α hr x * (w (sC ε hε0 * x) : ℂ) ∂μ =
      (c : ℂ) * (((cT : ℝ) : ℂ))⁻¹ *
        ∫ ρ in Set.Ioi (0 : ℝ), ∫ z : ℂ, ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
        (ρ : ℂ)⁻¹ * ((2 * Real.sin a.1.2 * Real.cos a.1.2 : ℝ) : ℂ) *
          ellF φ r α hr ρ ((((a.1.1 : ℝ) : ℂ) + ((a.1.2 : ℝ) : ℂ) * Complex.I, ((a.2 : ℝ) : ℂ) * Complex.I), z) := by
  letI : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI : IsTopologicalGroup (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI := hμ
  have hwm : Measurable w := hw.2.1
  have hs : Measurable fun x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => sC ε hε0 * x := (continuous_const.mul continuous_id).measurable

  have hT : MeasurableSet ((Set.Ioo (0 : ℝ) (2 * Real.pi) ×ˢ SplitCore.boxA) ×ˢ
      ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) :=
    (measurableSet_Ioo.prod measurableSet_boxA).prod (MeasurableSet.univ.prod measurableSet_Ioo)
  have hTW : MeasurableSet torusWindow := (measurableSet_Ioi.prod measurableSet_Ioi).prod hT
  have hFIB : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hBASE : MeasurableSet
      (Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) :=
    measurableSet_Ioi.prod (measurableSet_boxA.prod (MeasurableSet.univ.prod measurableSet_Ioo))
  have hmem : ∀ v ∈ Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))),
      0 < v.1 ∧ 0 < v.2.1.2 ∧ v.2.1.2 < Real.pi / 2 := by
    intro v hv
    have hv₁ := Set.mem_prod.1 hv
    have hv₂ := Set.mem_prod.1 hv₁.2
    have ha : v.2.1 ∈ Set.Ioo (0 : ℝ) Real.pi ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := hv₂.1
    have ha' := Set.mem_prod.1 ha
    exact ⟨hv₁.1, ha'.2.1, ha'.2.2⟩

  have hKpm : Measurable (eKp φ r α hr ε hε0 w) := measurable_eKp φ hφ r α hr ε hε0 δ hA w hwm
  have hslotm : Measurable (slotK φ r α hr ε hε0 w) := by
    unfold slotK
    exact hKpm.comp coords.symm.measurable
  have hturnm : Measurable (turnK φ r α hr ε hε0 w) := measurable_turnK φ hφ r α hr ε hε0 δ hA w hwm
  obtain ⟨htorm, hshm⟩ := measurable_shearK φ hφ r α hr ε hε0 δ hA w hwm
  have hfibm : Measurable (fibK φ r α hr ε hε0 w) := by
    unfold fibK
    exact hshm.comp fibreCoords.symm.measurable

  have hbase := integrableOn_baseK φ hφ hφc r α hr hα
  have hvolC : (volume : Measure ((ℝ × ℝ) × (ℝ × ((ℝ × ℝ) × (ℂ × ℝ))))).restrict fibreWindow =
      (volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))))) := by
    unfold fibreWindow
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ((ℝ × ℝ) × (ℂ × ℝ))), Measure.prod_restrict]
  have hprodC : Integrable (fibK φ r α hr ε hε0 w)
      ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict
          (Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))))) := by
    refine (integrable_prod_iff' hfibm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine (ae_restrict_iff' hBASE).2 (Filter.Eventually.of_forall fun v hv => ?_)
      obtain ⟨hρ, hη0, hηlt⟩ := hmem v hv
      exact (ell_inner φ r α hr ε hε hε0 δ hA τ cT hcT hτ w hw v hρ hη0 hηlt).1
    · refine (hbase.norm.mul_const ((cT : ℝ)⁻¹)).congr ?_
      refine (ae_restrict_iff' hBASE).2 (Filter.Eventually.of_forall fun v hv => ?_)
      obtain ⟨hρ, hη0, hηlt⟩ := hmem v hv
      exact (ell_inner φ r α hr ε hε hε0 δ hA τ cT hcT hτ w hw v hρ hη0 hηlt).2.2.symm
  have hC : IntegrableOn (fibK φ r α hr ε hε0 w) fibreWindow := by
    rw [IntegrableOn, hvolC]
    exact hprodC

  have hshA : IntegrableOn (shearK φ r α hr ε hε0 w) torusWindow := by
    have h1 : IntegrableOn (fun y => fibK φ r α hr ε hε0 w (fibreCoords y)) torusWindow := by
      rw [torusWindow_eq_preimage]
      exact (measurePreserving_fibreCoords.integrableOn_comp_preimage fibreCoords.measurableEmbedding).2 hC
    refine h1.congr_fun (fun y _ => ?_) hTW
    show shearK φ r α hr ε hε0 w (fibreCoords.symm (fibreCoords y)) = shearK φ r α hr ε hε0 w y
    rw [MeasurableEquiv.symm_apply_apply]
  obtain ⟨htorI, htorV⟩ := scale_shear_on_fibres (torK φ r α hr ε hε0 w) htorm _ hshA

  have hturnI : IntegrableOn (turnK φ r α hr ε hε0 w) slotWindow := by
    have h1 : IntegrableOn (fun x => torK φ r α hr ε hε0 w (MeasurableEquiv.prodAssoc x)) slotWindow := by
      rw [slotWindow_eq_preimage]
      exact ((volume_preserving_prodAssoc (α₁ := ℝ × ℝ) (β₁ := ℝ × (ℝ × ℝ)) (γ₁ := ℂ × ℝ)).integrableOn_comp_preimage
        MeasurableEquiv.prodAssoc.measurableEmbedding).2 htorI
    exact h1.congr_fun (fun x _ => rfl) measurableSet_slotWindow
  have hper : ∀ (o : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) (z : ℂ),
      Function.Periodic (fun ξ : ℝ => slotK φ r α hr ε hε0 w (o, (z, ξ))) (2 * Real.pi) :=
    fun o z ξ => slotK_add_two_pi φ r α hr ε hε0 w o z ξ
  obtain ⟨hslotI, hslotV⟩ := turn_advance_on_fibres (slotK φ r α hr ε hε0 w) hslotm hper _ hturnI

  have hD : IntegrableOn (eKp φ r α hr ε hε0 w) SplitCore.ksDom := by
    have h1 : IntegrableOn (fun p => slotK φ r α hr ε hε0 w (coords p)) SplitCore.ksDom := by
      rw [ksDom_eq_preimage_coords]
      exact (measurePreserving_coords.integrableOn_comp_preimage coords.measurableEmbedding).2 hslotI
    refine h1.congr_fun (fun p _ => ?_) SplitCore.measurableSet_ksDom
    show eKp φ r α hr ε hε0 w (coords.symm (coords p)) = eKp φ r α hr ε hε0 w p
    rw [MeasurableEquiv.symm_apply_apply]

  have hvol : volume HaarRef.regSetℂ ≠ 0 := by
    refine HaarRef.isOpen_regSetℂ.measure_ne_zero volume ⟨Matrix.of.symm 1, ?_⟩
    change (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hKS' : Measure.map SplitCore.ksChart ((volume.restrict SplitCore.ksDom).withDensity SplitCore.ksJ) =
      volume.restrict HaarRef.regSetℂ := by
    rw [hKS, SplitCore.ksLocus_eq_regSetℂ]
  have hFm : Measurable (eF φ r α hr ε hε0 w) := by
    unfold eF
    exact HaarRef.measurable_densℂ.ennreal_toReal.smul
      (((measurable_orbA φ hφ r α hr ε hε0 δ hA).comp HaarRef.measurable_glOfℂ).mul
        (Complex.measurable_ofReal.comp ((hwm.comp hs).comp HaarRef.measurable_glOfℂ)))
  have hL : IntegrableOn (eF φ r α hr ε hε0 w) HaarRef.regSetℂ volume :=
    (HaarRef.integrableOn_iff_of_map_eq SplitCore.measurable_ksJ SplitCore.ksJ_lt_top hKS' hvol (eF φ r α hr ε hε0 w)
      hFm.aestronglyMeasurable).2 hD
  have hHm : Measurable fun x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => orbA φ r α hr x * (w (sC ε hε0 * x) : ℂ) :=
    (measurable_orbA φ hφ r α hr ε hε0 δ hA).mul (Complex.measurable_ofReal.comp (hwm.comp hs))

  have hhaar : ∫ x, orbA φ r α hr x * (w (sC ε hε0 * x) : ℂ) ∂μ =
      (c : ℝ) • ∫ A in HaarRef.regSetℂ, eF φ r α hr ε hε0 w A :=
    HaarRef.integral_haar_eqℂ μ c hμc _ hHm
  obtain ⟨htr, -⟩ := HaarRef.setIntegral_eq_of_map_eq SplitCore.measurable_ksJ SplitCore.ksJ_lt_top hKS' hvol
    (eF φ r α hr ε hε0 w) hL
  have htr' : ∫ A in HaarRef.regSetℂ, eF φ r α hr ε hε0 w A = ∫ p in SplitCore.ksDom, eKp φ r α hr ε hε0 w p := htr
  have hcrd : ∫ p in SplitCore.ksDom, eKp φ r α hr ε hε0 w p = ∫ x in slotWindow, slotK φ r α hr ε hε0 w x := by
    have h1 : ∫ p in SplitCore.ksDom, eKp φ r α hr ε hε0 w p =
        ∫ p in SplitCore.ksDom, slotK φ r α hr ε hε0 w (coords p) :=
      setIntegral_congr_fun SplitCore.measurableSet_ksDom fun p _ => by
        show eKp φ r α hr ε hε0 w p = eKp φ r α hr ε hε0 w (coords.symm (coords p))
        rw [MeasurableEquiv.symm_apply_apply]
    rw [h1, ksDom_eq_preimage_coords,
      measurePreserving_coords.setIntegral_preimage_emb coords.measurableEmbedding (slotK φ r α hr ε hε0 w) slotWindow]
  have hslotV' : ∫ x in slotWindow, slotK φ r α hr ε hε0 w x = ∫ x in slotWindow, turnK φ r α hr ε hε0 w x := hslotV
  have hturnV : ∫ x in slotWindow, turnK φ r α hr ε hε0 w x = ∫ y in torusWindow, torK φ r α hr ε hε0 w y := by
    have h1 : ∫ x in slotWindow, turnK φ r α hr ε hε0 w x =
        ∫ x in slotWindow, torK φ r α hr ε hε0 w (MeasurableEquiv.prodAssoc x) :=
      setIntegral_congr_fun measurableSet_slotWindow fun x _ => rfl
    rw [h1, slotWindow_eq_preimage,
      (volume_preserving_prodAssoc (α₁ := ℝ × ℝ) (β₁ := ℝ × (ℝ × ℝ)) (γ₁ := ℂ × ℝ)).setIntegral_preimage_emb
        MeasurableEquiv.prodAssoc.measurableEmbedding (torK φ r α hr ε hε0 w) torusWindow]
  have htorV' : ∫ y in torusWindow, torK φ r α hr ε hε0 w y = ∫ y in torusWindow, shearK φ r α hr ε hε0 w y := htorV
  have hshV : ∫ y in torusWindow, shearK φ r α hr ε hε0 w y = ∫ u in fibreWindow, fibK φ r α hr ε hε0 w u := by
    have h1 : ∫ y in torusWindow, shearK φ r α hr ε hε0 w y =
        ∫ y in torusWindow, fibK φ r α hr ε hε0 w (fibreCoords y) :=
      setIntegral_congr_fun hTW fun y _ => by
        show shearK φ r α hr ε hε0 w y = shearK φ r α hr ε hε0 w (fibreCoords.symm (fibreCoords y))
        rw [MeasurableEquiv.symm_apply_apply]
    rw [h1, torusWindow_eq_preimage,
      measurePreserving_fibreCoords.setIntegral_preimage_emb fibreCoords.measurableEmbedding (fibK φ r α hr ε hε0 w)
        fibreWindow]
  have hfub : ∫ u in fibreWindow, fibK φ r α hr ε hε0 w u =
      ∫ v in Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))),
        ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), fibK φ r α hr ε hε0 w (q, v) := by
    rw [hvolC]
    exact integral_prod_symm _ hprodC
  have hinner : ∫ v in Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))),
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), fibK φ r α hr ε hε0 w (q, v) =
        ∫ v in Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))),
          baseK φ r α hr v * (((cT : ℝ) : ℂ))⁻¹ :=
    setIntegral_congr_fun hBASE fun v hv => by
      obtain ⟨hρ, hη0, hηlt⟩ := hmem v hv
      exact (ell_inner φ r α hr ε hε hε0 δ hA τ cT hcT hτ w hw v hρ hη0 hηlt).2.1

  have hbaseV : ∫ v in Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))),
      baseK φ r α hr v =
        ∫ ρ in Set.Ioi (0 : ℝ), ∫ z : ℂ,
          ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
            (ρ : ℂ)⁻¹ * ((2 * Real.sin a.1.2 * Real.cos a.1.2 : ℝ) : ℂ) *
              ellF φ r α hr ρ ((((a.1.1 : ℝ) : ℂ) + ((a.1.2 : ℝ) : ℂ) * Complex.I, ((a.2 : ℝ) : ℂ) * Complex.I),
                z) := by
    have hv1 : (volume : Measure (ℝ × ((ℝ × ℝ) × (ℂ × ℝ)))).restrict
        (Set.Ioi (0 : ℝ) ×ˢ (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) =
          (volume.restrict (Set.Ioi (0 : ℝ))).prod
            (volume.restrict (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) := by
      rw [Measure.volume_eq_prod ℝ ((ℝ × ℝ) × (ℂ × ℝ)), Measure.prod_restrict]
    have hb' : Integrable (baseK φ r α hr) ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))))) := by
      rw [← hv1]
      exact hbase
    have hpre : SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) =
        slotSwap ⁻¹' ((Set.univ : Set ℂ) ×ˢ (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
      ext t
      show t ∈ SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ↔
        (t.2.1, (t.1, t.2.2)) ∈ (Set.univ : Set ℂ) ×ˢ (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))
      simp only [Set.mem_prod, Set.mem_univ, true_and]
    have hv2 : (volume : Measure (ℂ × ((ℝ × ℝ) × ℝ))).restrict
        ((Set.univ : Set ℂ) ×ˢ (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) =
          (volume : Measure ℂ).prod (volume.restrict (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
      rw [Measure.volume_eq_prod ℂ ((ℝ × ℝ) × ℝ), ← Measure.prod_restrict, Measure.restrict_univ]
    rw [hv1, integral_prod _ hb']
    refine integral_congr_ae ?_
    filter_upwards [hb'.prod_right_ae] with ρ hρI
    have hG : IntegrableOn (fun t : ℂ × ((ℝ × ℝ) × ℝ) => baseK φ r α hr (ρ, (t.2.1, (t.1, t.2.2))))
        ((Set.univ : Set ℂ) ×ˢ (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))) := by
      have h4 : IntegrableOn ((fun t : ℂ × ((ℝ × ℝ) × ℝ) => baseK φ r α hr (ρ, (t.2.1, (t.1, t.2.2)))) ∘ slotSwap)
          (slotSwap ⁻¹' ((Set.univ : Set ℂ) ×ˢ (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) := by
        rw [← hpre]
        exact hρI
      exact (measurePreserving_slotSwap.integrableOn_comp_preimage slotSwap.measurableEmbedding).1 h4
    have hG' : Integrable (fun t : ℂ × ((ℝ × ℝ) × ℝ) => baseK φ r α hr (ρ, (t.2.1, (t.1, t.2.2))))
        ((volume : Measure ℂ).prod (volume.restrict (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))) := by
      rw [← hv2]
      exact hG
    have h2 : ∫ t in SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)), baseK φ r α hr (ρ, t) =
        ∫ t in (Set.univ : Set ℂ) ×ˢ (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)),
          baseK φ r α hr (ρ, (t.2.1, (t.1, t.2.2))) := by
      have h3 : ∫ t in SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)), baseK φ r α hr (ρ, t) =
          ∫ t in SplitCore.boxA ×ˢ ((Set.univ : Set ℂ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)),
            (fun t : ℂ × ((ℝ × ℝ) × ℝ) => baseK φ r α hr (ρ, (t.2.1, (t.1, t.2.2)))) (slotSwap t) :=
        setIntegral_congr_fun (measurableSet_boxA.prod (MeasurableSet.univ.prod measurableSet_Ioo)) fun t _ => rfl
      rw [h3, hpre]
      exact measurePreserving_slotSwap.setIntegral_preimage_emb slotSwap.measurableEmbedding
        (fun t : ℂ × ((ℝ × ℝ) × ℝ) => baseK φ r α hr (ρ, (t.2.1, (t.1, t.2.2))))
        ((Set.univ : Set ℂ) ×ˢ (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)))
    rw [h2, hv2, integral_prod _ hG']
    rfl
  rw [hhaar, htr', hcrd, hslotV', hturnV, htorV', hshV, hfub, hinner, integral_mul_const, hbaseV, Complex.real_smul]
  ring

private def inflF (φ : GL (Fin 2) ℂ → ℂ) (r α ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (u : ℂ) : GL (Fin 2) ℂ → ℂ :=
  fun k => φ (k⁻¹ * twistedEllipticElt r α ρ u hr hρ * conjEntries k)

private theorem continuous_inflF (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r α ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (u : ℂ) :
    Continuous (inflF φ r α ρ hr hρ u) := by
  unfold inflF
  exact hφ.comp ((continuous_inv.mul continuous_const).mul (TwistedTorus.Rid.continuous_glMap Complex.continuous_conj))

private theorem inflF_turn (φ : GL (Fin 2) ℂ → ℂ) (r α ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (a b ψ ξ₂ : ℝ) (u : ℂ) :
    inflF φ r α ρ hr hρ (Complex.exp (2 * ψ * Complex.I) * u) (unitaryElt a b ψ (ξ₂ + ψ)) =
      inflF φ r α ρ hr hρ u (unitaryElt a b 0 ξ₂) := by
  have hd : ∀ g : GL (Fin 2) ℂ, unitaryElt 0 0 ψ 0 * (conjEntries (unitaryElt 0 0 ψ 0) * g) = g := by
    intro g
    rw [← mul_assoc, phase_mul_conjEntries_phase, one_mul]
  have hk : unitaryElt a b ψ (ξ₂ + ψ) = unitaryElt 0 0 ψ 0 * unitaryElt a b 0 ξ₂ := by
    rw [Window.unitaryElt_zero_zero_mul, zero_add]
  simp only [inflF]
  rw [hk, ← phase_mul_twistedEllipticElt_mul_phase, mul_inv_rev, Orbit.conjEntries_mul]
  simp only [mul_assoc, inv_mul_cancel_left, hd]

private theorem boxG_turn (φ : GL (Fin 2) ℂ → ℂ) (r α ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (p₁ : ℝ × ℝ) (ψ ξ₂ : ℝ)
    (u : ℂ) :
    SplitCore.boxG (inflF φ r α ρ hr hρ (Complex.exp (2 * ψ * Complex.I) * u)) (p₁, (ψ, ξ₂ + ψ)) =
      SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)) := by
  first
    | (simp only [SplitCore.boxG, inflF_turn]; done)
    | (unfold SplitCore.boxG; rw [inflF_turn])

private theorem inner_turn (φ : GL (Fin 2) ℂ → ℂ) (r α ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (p₁ : ℝ × ℝ) (ψ : ℝ) :
    (∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, (ψ, ξ₂))) =
      ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)) := by
  have hper : Function.Periodic (fun ξ₂ : ℝ => ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, (ψ, ξ₂)))
      (2 * Real.pi) :=
    fun ξ₂ => by simp only [SplitCore.boxG, Window.unitaryElt_add_two_pi_right]
  obtain ⟨rot, hrotP, hrot⟩ := FibreShift.exists_rotation_measurableEquiv _ (FibreShift.normSq_exp_two_mul ψ)
  have hrt : ∀ ξ : ℝ, (∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, (ψ, ξ + ψ))) =
      ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ)) := by
    intro ξ
    have h := hrotP.integral_comp rot.measurableEmbedding
      (fun u : ℂ => SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, (ψ, ξ + ψ)))
    simp only [hrot, boxG_turn] at h
    exact h.symm
  rw [← FibreShift.setIntegral_Ioo_comp_add_of_periodic _ hper ψ]
  exact setIntegral_congr_fun measurableSet_Ioo fun ξ _ => hrt ξ

private theorem setIntegral_Ioo_two_pi_const (C : ℂ) :
    (∫ _x in Set.Ioo (0 : ℝ) (2 * Real.pi), C) = ((2 * Real.pi : ℝ) : ℂ) * C := by
  rw [SplitCore.setIntegral_Ioo_eq _ _ (mul_pos two_pos Real.pi_pos).le, intervalIntegral.integral_const, sub_zero]
  first
    | (rw [Complex.real_smul]; done)
    | (rw [Complex.real_smul]; push_cast; ring1)
    | (simp only [Complex.real_smul]; push_cast; ring1)

private theorem turn_box (φ : GL (Fin 2) ℂ → ℂ) (r α ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (p₁ : ℝ × ℝ)
    (hq : IntegrableOn (fun q : ℝ × ℝ => ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, q)) SplitCore.boxB) :
    (∫ q in SplitCore.boxB, ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, q)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)) := by
  have hq' : IntegrableOn (fun q : ℝ × ℝ => ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, q)) SplitCore.boxB
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hq
  have h1 : (∫ q in SplitCore.boxB, ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, q)) =
      ∫ ξ₁ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, (ξ₁, ξ₂)) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact setIntegral_prod _ hq'
  have h2 : (∫ ξ₁ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, (ξ₁, ξ₂))) =
      ∫ _ξ₁ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)) :=
    setIntegral_congr_fun measurableSet_Ioo fun ξ₁ _ => inner_turn φ r α ρ hr hρ p₁ ξ₁
  rw [h1, h2, setIntegral_Ioo_two_pi_const]

private theorem inflate_const (X : ℂ) :
    ((2 * Real.pi ^ 2 : ℝ) : ℂ) * (((4 * Real.pi ^ 3 : ℝ) : ℂ)⁻¹ * (((2 * Real.pi : ℝ) : ℂ) * X)) = X := by
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  first
    | (push_cast; field_simp; done)
    | (push_cast; field_simp; ring1)
    | (field_simp; ring1)

private theorem continuous_boxG_joint (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r α ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) :
    Continuous fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × ℂ => SplitCore.boxG (inflF φ r α ρ hr hρ x.2) x.1 := by
  have hm : Continuous fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × ℂ => ((x.1.1.1, x.1.1.2, x.1.2.1, x.1.2.2), (ρ, x.2)) := by
    fun_prop
  have hc := (Proper.continuousOn_orbitFactor_elliptic φ hφ r α hr).comp_continuous hm (fun _ => hρ)
  have hc' : Continuous fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × ℂ =>
      inflF φ r α ρ hr hρ x.2 (unitaryElt x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2) := by
    refine hc.congr fun x => ?_
    simp only [Function.comp_apply, inflF, dif_pos hρ]
  have hs : Continuous fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × ℂ => (2 * Real.sin x.1.1.2 * Real.cos x.1.1.2 : ℂ) := by
    fun_prop
  unfold SplitCore.boxG
  exact hs.mul hc'

private theorem integrableOn_boxG_box (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (r α ρ : ℝ) (hr : 0 < r) (hα : Real.sin α ≠ 0) (hρ : 0 < ρ) :
    IntegrableOn (fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × ℂ => SplitCore.boxG (inflF φ r α ρ hr hρ x.2) x.1)
      ((SplitCore.boxA ×ˢ SplitCore.boxB) ×ˢ (Set.univ : Set ℂ)) := by
  obtain ⟨R, ε, -, hR⟩ := Proper.exists_bound_elliptic φ hφc r α hr hα
  have hcont := continuous_boxG_joint φ hφ r α ρ hr hρ
  have hK : IsCompact (((Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) ×ˢ Metric.closedBall (0 : ℂ) R) :=
    ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)).prod (isCompact_closedBall _ _)
  have hsub : SplitCore.boxA ×ˢ SplitCore.boxB ⊆
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    Set.prod_mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  have hmA : MeasurableSet SplitCore.boxA := by
    unfold SplitCore.boxA
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hmB : MeasurableSet SplitCore.boxB := by
    unfold SplitCore.boxB
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hint := hcont.continuousOn.integrableOn_compact (μ := volume) hK
  refine hint.of_forall_diff_eq_zero ((hmA.prod hmB).prod MeasurableSet.univ) ?_
  rintro ⟨p, u⟩ ⟨hs, hnot⟩
  have hp : p ∈ (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    hsub (Set.mem_prod.1 hs).1
  have hu : u ∉ Metric.closedBall (0 : ℂ) R := fun hu => hnot (Set.mem_prod.2 ⟨hp, hu⟩)
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hu
  have hzero : φ ((unitaryElt p.1.1 p.1.2 p.2.1 p.2.2)⁻¹ * twistedEllipticElt r α ρ u hr hρ *
      conjEntries (unitaryElt p.1.1 p.1.2 p.2.1 p.2.2)) = 0 := by
    by_contra hne
    exact absurd (hR p.1.1 p.1.2 p.2.1 p.2.2 ρ u hρ hne).2.2 (not_le.2 hu)
  simp only [SplitCore.boxG, inflF, hzero, mul_zero]

private theorem integrableOn_boxG_slice (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (r α ρ : ℝ) (hr : 0 < r) (hα : Real.sin α ≠ 0) (hρ : 0 < ρ) :
    IntegrableOn (fun x : ((ℝ × ℝ) × ℝ) × ℂ => SplitCore.boxG (inflF φ r α ρ hr hρ x.2) (x.1.1, ((0 : ℝ), x.1.2)))
      ((SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ×ˢ (Set.univ : Set ℂ)) := by
  obtain ⟨R, ε, -, hR⟩ := Proper.exists_bound_elliptic φ hφc r α hr hα
  have hg : Continuous fun x : ((ℝ × ℝ) × ℝ) × ℂ => (((x.1.1, ((0 : ℝ), x.1.2)) : (ℝ × ℝ) × (ℝ × ℝ)), x.2) := by
    fun_prop
  have hcont : Continuous fun x : ((ℝ × ℝ) × ℝ) × ℂ =>
      SplitCore.boxG (inflF φ r α ρ hr hρ x.2) (x.1.1, ((0 : ℝ), x.1.2)) := by
    refine ((continuous_boxG_joint φ hφ r α ρ hr hρ).comp hg).congr fun x => ?_
    first
      | (simp only [Function.comp_apply]; done)
      | rfl
  have hK : IsCompact (((Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ×ˢ
      Metric.closedBall (0 : ℂ) R) :=
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod (isCompact_closedBall _ _)
  have hsub : SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) ⊆
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) :=
    Set.prod_mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self) Set.Ioo_subset_Icc_self
  have hmA : MeasurableSet SplitCore.boxA := by
    unfold SplitCore.boxA
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hint := hcont.continuousOn.integrableOn_compact (μ := volume) hK
  refine hint.of_forall_diff_eq_zero ((hmA.prod measurableSet_Ioo).prod MeasurableSet.univ) ?_
  rintro ⟨a, u⟩ ⟨hs, hnot⟩
  have ha : a ∈ (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi) :=
    hsub (Set.mem_prod.1 hs).1
  have hu : u ∉ Metric.closedBall (0 : ℂ) R := fun hu => hnot (Set.mem_prod.2 ⟨ha, hu⟩)
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hu
  have hzero : φ ((unitaryElt a.1.1 a.1.2 0 a.2)⁻¹ * twistedEllipticElt r α ρ u hr hρ *
      conjEntries (unitaryElt a.1.1 a.1.2 0 a.2)) = 0 := by
    by_contra hne
    exact absurd (hR a.1.1 a.1.2 0 a.2 ρ u hρ hne).2.2 (not_le.2 hu)
  simp only [SplitCore.boxG, inflF, hzero, mul_zero]

private theorem inflate_integrand_eq (φ : GL (Fin 2) ℂ → ℂ) (r α ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (z : ℂ)
    (a : (ℝ × ℝ) × ℝ) :
        ((2 * Real.sin a.1.2 * Real.cos a.1.2 : ℝ) : ℂ) *
          ellF φ r α hr ρ ((((a.1.1 : ℝ) : ℂ) + ((a.1.2 : ℝ) : ℂ) * Complex.I, ((a.2 : ℝ) : ℂ) * Complex.I), z) =
      SplitCore.boxG (inflF φ r α ρ hr hρ z) (a.1, ((0 : ℝ), a.2)) := by
  simp only [SplitCore.boxG, inflF, ellF, dif_pos hρ, SplitCore.kU]
  first
    | (simp; done)
    | (push_cast; simp; done)
    | (simp [Complex.ext_iff]; done)

private theorem inflate_left (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (r α : ℝ)
    (hr : 0 < r) (hα : Real.sin α ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ z : ℂ, ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
        ((2 * Real.sin a.1.2 * Real.cos a.1.2 : ℝ) : ℂ) *
          ellF φ r α hr ρ ((((a.1.1 : ℝ) : ℂ) + ((a.1.2 : ℝ) : ℂ) * Complex.I, ((a.2 : ℝ) : ℂ) * Complex.I), z)) =
      ∫ p₁ in SplitCore.boxA, ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)) := by
  have hpt := inflate_integrand_eq φ r α ρ hr hρ
  have h0 :
    (∫ z : ℂ, ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
        ((2 * Real.sin a.1.2 * Real.cos a.1.2 : ℝ) : ℂ) *
          ellF φ r α hr ρ ((((a.1.1 : ℝ) : ℂ) + ((a.1.2 : ℝ) : ℂ) * Complex.I, ((a.2 : ℝ) : ℂ) * Complex.I), z)) =
        ∫ z : ℂ, ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
          SplitCore.boxG (inflF φ r α ρ hr hρ z) (a.1, ((0 : ℝ), a.2)) := by
    simp only [hpt]
  have hI : Integrable (fun x : ((ℝ × ℝ) × ℝ) × ℂ =>
      SplitCore.boxG (inflF φ r α ρ hr hρ x.2) (x.1.1, ((0 : ℝ), x.1.2)))
      ((volume.restrict (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict (Set.univ : Set ℂ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integrableOn_boxG_slice φ hφ hφc r α ρ hr hα hρ
  rw [Measure.restrict_univ] at hI
  have hsw := integral_integral_swap (show Integrable (Function.uncurry fun (a : (ℝ × ℝ) × ℝ) (z : ℂ) =>
      SplitCore.boxG (inflF φ r α ρ hr hρ z) (a.1, ((0 : ℝ), a.2)))
      ((volume.restrict (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).prod volume) from hI)
  have h2 : (∫ z : ℂ, ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
        SplitCore.boxG (inflF φ r α ρ hr hρ z) (a.1, ((0 : ℝ), a.2))) =
      ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ z : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ z) (a.1, ((0 : ℝ), a.2)) := hsw.symm
  have hJ : IntegrableOn (fun a : (ℝ × ℝ) × ℝ => ∫ z : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ z) (a.1, ((0 : ℝ), a.2)))
      (SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) ((volume : Measure (ℝ × ℝ)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hI.integral_prod_left
  have h3 : (∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ z : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ z) (a.1, ((0 : ℝ), a.2))) =
      ∫ p₁ in SplitCore.boxA, ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
    exact setIntegral_prod _ hJ
  rw [h0, h2, h3]

private theorem inflate_right (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (r α : ℝ)
    (hr : 0 < r) (hα : Real.sin α ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) :
    (((2 * Real.pi ^ 2 : ℝ) : ℂ) *
        ∫ u : ℂ, unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α ρ u hr hρ * conjEntries k)) =
      ((2 * Real.pi ^ 2 : ℝ) : ℂ) * (((4 * Real.pi ^ 3 : ℝ) : ℂ)⁻¹ * (((2 * Real.pi : ℝ) : ℂ) *
        ∫ p₁ in SplitCore.boxA, ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)))) := by
  have havg : ∀ u : ℂ,
      (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α ρ u hr hρ * conjEntries k)) =
        ((4 * Real.pi ^ 3 : ℝ) : ℂ)⁻¹ * ∫ p in SplitCore.boxA ×ˢ SplitCore.boxB,
          SplitCore.boxG (inflF φ r α ρ hr hρ u) p := by
    intro u
    have hw := SplitCore.window_integral (inflF φ r α ρ hr hρ u) (continuous_inflF φ hφ r α ρ hr hρ u)
    have h1 : (∫ β in SplitCore.aSet,
          (2 * Real.sin β.1.im * Real.cos β.1.im : ℂ) * inflF φ r α ρ hr hρ u (SplitCore.kU β)) =
        ∫ p in SplitCore.boxA ×ˢ SplitCore.boxB, SplitCore.boxG (inflF φ r α ρ hr hρ u) p := by
      change ∫ β in SplitCore.aSet, SplitCore.boxG (inflF φ r α ρ hr hρ u) (SplitCore.angEquiv β) = _
      rw [SplitCore.aSet_eq_preimage]
      exact (SplitCore.measurePreserving_angEquiv).setIntegral_preimage_emb
        (SplitCore.angEquiv).measurableEmbedding _ _
    have hcB : ((4 * Real.pi ^ 3 : ℝ) : ℂ) * unitaryAverage (inflF φ r α ρ hr hρ u) =
        ∫ p in SplitCore.boxA ×ˢ SplitCore.boxB, SplitCore.boxG (inflF φ r α ρ hr hρ u) p := hw.symm.trans h1
    have h4 : ((4 * Real.pi ^ 3 : ℝ) : ℂ) ≠ 0 := by
      first
        | exact Complex.ofReal_ne_zero.2 (by positivity)
        | exact_mod_cast (by positivity : (4 * Real.pi ^ 3 : ℝ) ≠ 0)
    show unitaryAverage (inflF φ r α ρ hr hρ u) = _
    rw [← hcB, inv_mul_cancel_left₀ h4]
  have hI : Integrable (fun x : ((ℝ × ℝ) × (ℝ × ℝ)) × ℂ => SplitCore.boxG (inflF φ r α ρ hr hρ x.2) x.1)
      ((volume.restrict (SplitCore.boxA ×ˢ SplitCore.boxB)).prod (volume.restrict (Set.univ : Set ℂ))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integrableOn_boxG_box φ hφ hφc r α ρ hr hα hρ
  rw [Measure.restrict_univ] at hI
  have hsw := integral_integral_swap (show Integrable (Function.uncurry fun (p : (ℝ × ℝ) × (ℝ × ℝ)) (u : ℂ) =>
      SplitCore.boxG (inflF φ r α ρ hr hρ u) p)
      ((volume.restrict (SplitCore.boxA ×ˢ SplitCore.boxB)).prod volume) from hI)
  have h2 : (∫ u : ℂ, ∫ p in SplitCore.boxA ×ˢ SplitCore.boxB, SplitCore.boxG (inflF φ r α ρ hr hρ u) p) =
      ∫ p in SplitCore.boxA ×ˢ SplitCore.boxB, ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) p := hsw.symm
  have hJ' : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) p)
      ((volume.restrict SplitCore.boxA).prod (volume.restrict SplitCore.boxB)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hI.integral_prod_left
  have hJ : IntegrableOn (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) p)
      (SplitCore.boxA ×ˢ SplitCore.boxB) ((volume : Measure (ℝ × ℝ)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hI.integral_prod_left
  have h3 : (∫ p in SplitCore.boxA ×ˢ SplitCore.boxB, ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) p) =
      ∫ p₁ in SplitCore.boxA, ∫ q in SplitCore.boxB, ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, q) := by
    rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ)]
    exact setIntegral_prod _ hJ
  have h4 : (∫ p₁ in SplitCore.boxA, ∫ q in SplitCore.boxB, ∫ u : ℂ, SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, q)) =
      ∫ p₁ in SplitCore.boxA, ((2 * Real.pi : ℝ) : ℂ) * ∫ ξ₂ in Set.Ioo (0 : ℝ) (2 * Real.pi), ∫ u : ℂ,
        SplitCore.boxG (inflF φ r α ρ hr hρ u) (p₁, ((0 : ℝ), ξ₂)) := by
    refine integral_congr_ae ?_
    filter_upwards [hJ'.prod_right_ae] with p₁ hp₁
    exact turn_box φ r α ρ hr hρ p₁ hp₁
  simp only [havg]
  rw [integral_const_mul, h2, h3, h4, integral_const_mul]

private theorem inflate (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (r α : ℝ)
    (hr : 0 < r) (hα : Real.sin α ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ z : ℂ, ∫ a in SplitCore.boxA ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi),
        ((2 * Real.sin a.1.2 * Real.cos a.1.2 : ℝ) : ℂ) *
          ellF φ r α hr ρ ((((a.1.1 : ℝ) : ℂ) + ((a.1.2 : ℝ) : ℂ) * Complex.I, ((a.2 : ℝ) : ℂ) * Complex.I), z) =
      ((2 * Real.pi ^ 2 : ℝ) : ℂ) *
        ∫ u : ℂ, unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α ρ u hr hρ * conjEntries k) := by
  rw [inflate_left φ hφ hφc r α hr hα ρ hρ, inflate_right φ hφ hφc r α hr hα ρ hρ, inflate_const]

private def angleQuad (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℂ :=
  ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
    ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
      (Real.sin η * Real.cos η : ℂ) * F ψ η ξ₁ ξ₂

private theorem unitaryAverage_eq_angleQuad (G : GL (Fin 2) ℂ → ℂ) :
    unitaryAverage G = (1 / (4 * Real.pi ^ 3) : ℂ) * angleQuad fun ψ η ξ₁ ξ₂ => G (unitaryElt ψ η ξ₁ ξ₂) :=
  rfl

private theorem angleQuad_eq_zero (F : ℝ → ℝ → ℝ → ℝ → ℂ) (hF : ∀ ψ η ξ₁ ξ₂, F ψ η ξ₁ ξ₂ = 0) :
    angleQuad F = 0 := by
  unfold angleQuad
  simp only [hF, mul_zero, intervalIntegral.integral_zero]

private theorem norm_angleQuad_le (F : ℝ → ℝ → ℝ → ℝ → ℂ) (M : ℝ) (hM : ∀ ψ η ξ₁ ξ₂, ‖F ψ η ξ₁ ξ₂‖ ≤ M) :
    ‖angleQuad F‖ ≤
      M * |2 * Real.pi - 0| * |2 * Real.pi - 0| * |Real.pi / 2 - 0| * |2 * Real.pi - 0| := by
  unfold angleQuad
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun ψ _ => ?_
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun η _ => ?_
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun ξ₁ _ => ?_
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun ξ₂ _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hsc : |Real.sin η| * |Real.cos η| ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one η) (abs_nonneg _)).trans
      (by rw [mul_one]; exact Real.abs_sin_le_one η)
  calc |Real.sin η| * |Real.cos η| * ‖F ψ η ξ₁ ξ₂‖ ≤ 1 * ‖F ψ η ξ₁ ξ₂‖ :=
        mul_le_mul_of_nonneg_right hsc (norm_nonneg _)
    _ = ‖F ψ η ξ₁ ξ₂‖ := one_mul _
    _ ≤ M := hM ψ η ξ₁ ξ₂

private theorem continuous_angleQuad {X : Type*} [TopologicalSpace X] (F : X → ℝ → ℝ → ℝ → ℝ → ℂ)
    (hF : Continuous fun p : X × ℝ × ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) :
    Continuous fun x => angleQuad (F x) := by
  unfold angleQuad
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  show Continuous fun p : X × ℝ => ∫ η in (0 : ℝ)..(Real.pi / 2), ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
    ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin η * Real.cos η : ℂ) * F p.1 p.2 η ξ₁ ξ₂
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  show Continuous fun p : (X × ℝ) × ℝ => ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi),
    ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin p.2 * Real.cos p.2 : ℂ) * F p.1.1 p.1.2 p.2 ξ₁ ξ₂
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  show Continuous fun p : ((X × ℝ) × ℝ) × ℝ =>
    ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi), (Real.sin p.1.2 * Real.cos p.1.2 : ℂ) * F p.1.1.1 p.1.1.2 p.1.2 p.2 ξ₂
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  show Continuous fun p : (((X × ℝ) × ℝ) × ℝ) × ℝ =>
    (Real.sin p.1.1.2 * Real.cos p.1.1.2 : ℂ) * F p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2
  have hη : Continuous fun p : (((X × ℝ) × ℝ) × ℝ) × ℝ => p.1.1.2 := by fun_prop
  have hsc : Continuous fun p : (((X × ℝ) × ℝ) × ℝ) × ℝ => (Real.sin p.1.1.2 * Real.cos p.1.1.2 : ℂ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sin.comp hη)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp hη))
  have hre : Continuous fun p : (((X × ℝ) × ℝ) × ℝ) × ℝ =>
      (p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.1.2, p.2) := by fun_prop
  exact hsc.mul (hF.comp hre)

private def rhoAvg (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (p : ℝ × ℂ) : ℂ :=
  unitaryAverage fun k =>
    φ (k⁻¹ * (if hρ : 0 < p.1 then twistedEllipticElt r α p.1 p.2 hr hρ else 1) * conjEntries k)

private theorem norm_rhoAvg_le (φ : GL (Fin 2) ℂ → ℂ) (r α : ℝ) (hr : 0 < r) (M : ℝ) (hM : ∀ g, ‖φ g‖ ≤ M)
    (p : ℝ × ℂ) :
    ‖rhoAvg φ r α hr p‖ ≤ ‖(1 / (4 * Real.pi ^ 3) : ℂ)‖ *
      (M * |2 * Real.pi - 0| * |2 * Real.pi - 0| * |Real.pi / 2 - 0| * |2 * Real.pi - 0|) := by
  unfold rhoAvg
  rw [unitaryAverage_eq_angleQuad, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_angleQuad_le _ M fun _ _ _ _ => hM _) (norm_nonneg _)

private theorem continuousOn_rhoAvg (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (r α : ℝ) (hr : 0 < r) :
    ContinuousOn (rhoAvg φ r α hr) {p : ℝ × ℂ | 0 < p.1} := by
  rw [continuousOn_iff_continuous_restrict]
  have hF : Continuous fun q : {p : ℝ × ℂ // p ∈ {p : ℝ × ℂ | 0 < p.1}} × ℝ × ℝ × ℝ × ℝ =>
      φ ((unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)⁻¹ *
          (if hρ : 0 < (q.1 : ℝ × ℂ).1 then twistedEllipticElt r α (q.1 : ℝ × ℂ).1 (q.1 : ℝ × ℂ).2 hr hρ else 1) *
        conjEntries (unitaryElt q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) :=
    (Proper.continuousOn_orbitFactor_elliptic φ hφ r α hr).comp_continuous
      (f := fun q : {p : ℝ × ℂ // p ∈ {p : ℝ × ℂ | 0 < p.1}} × ℝ × ℝ × ℝ × ℝ => (q.2, (q.1 : ℝ × ℂ)))
      (by fun_prop) fun q => q.1.2
  have hA := continuous_angleQuad
    (fun (q : {p : ℝ × ℂ // p ∈ {p : ℝ × ℂ | 0 < p.1}}) (ψ η ξ₁ ξ₂ : ℝ) =>
      φ ((unitaryElt ψ η ξ₁ ξ₂)⁻¹ *
          (if hρ : 0 < (q : ℝ × ℂ).1 then twistedEllipticElt r α (q : ℝ × ℂ).1 (q : ℝ × ℂ).2 hr hρ else 1) *
        conjEntries (unitaryElt ψ η ξ₁ ξ₂))) hF
  have hC : Continuous fun _ : {p : ℝ × ℂ // p ∈ {p : ℝ × ℂ | 0 < p.1}} => (1 / (4 * Real.pi ^ 3) : ℂ) :=
    continuous_const
  exact (hC.mul hA).congr fun q => rfl

private theorem integrable_rhoU (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) (r α : ℝ)
    (hr : 0 < r) (hα : Real.sin α ≠ 0) :
    Integrable (fun q : ℝ × ℂ =>
        if hρ : 0 < q.1 then
          (q.1 : ℂ)⁻¹ * (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α q.1 q.2 hr hρ * conjEntries k))
        else 0)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨R, ε, hε, hbd⟩ := Proper.exists_bound_elliptic φ hφc r α hr hα
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℂ, ‖rhoAvg φ r α hr p‖ ≤ C :=
    ⟨_, mul_nonneg (norm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hM0 (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _))
        (abs_nonneg _)),
      norm_rhoAvg_le φ r α hr M hM⟩

  have hfun : ∀ q : ℝ × ℂ, 0 < q.1 →
      (if hρ : 0 < q.1 then
          (q.1 : ℂ)⁻¹ * (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α q.1 q.2 hr hρ * conjEntries k))
        else 0) = (q.1 : ℂ)⁻¹ * rhoAvg φ r α hr q := by
    intro q hq
    simp only [rhoAvg, dif_pos hq]

  have hbox : MeasurableSet (Set.Icc ε R ×ˢ Metric.closedBall (0 : ℂ) R) :=
    measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hfin : ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) (Set.Icc ε R ×ˢ Metric.closedBall (0 : ℂ) R) ≠ ⊤ := by
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Icc]
    exact ENNReal.mul_ne_top ((measure_mono Set.inter_subset_left).trans_lt measure_Icc_lt_top).ne
      measure_closedBall_lt_top.ne
  have hdom : Integrable ((Set.Icc ε R ×ˢ Metric.closedBall (0 : ℂ) R).indicator fun _ => ε⁻¹ * C)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    (integrableOn_const hfin).integrable_indicator hbox
  have hg0 : ∀ q : ℝ × ℂ, 0 ≤ (Set.Icc ε R ×ˢ Metric.closedBall (0 : ℂ) R).indicator (fun _ => ε⁻¹ * C) q := by
    intro q
    by_cases hq : q ∈ Set.Icc ε R ×ˢ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hq]
      exact mul_nonneg (inv_nonneg.2 hε.le) hC0
    · rw [Set.indicator_of_notMem hq]

  have hcont : ContinuousOn (fun q : ℝ × ℂ =>
      if hρ : 0 < q.1 then
        (q.1 : ℂ)⁻¹ * (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α q.1 q.2 hr hρ * conjEntries k))
      else 0) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)) := by
    refine ContinuousOn.congr (f := fun q : ℝ × ℂ => (q.1 : ℂ)⁻¹ * rhoAvg φ r α hr q) ?_ fun q hq => hfun q hq.1
    refine ContinuousOn.mul ?_ ((continuousOn_rhoAvg φ hφ r α hr).mono fun q hq => hq.1)
    have h1 : Continuous fun q : ℝ × ℂ => ((q.1 : ℝ) : ℂ) := Complex.continuous_ofReal.comp continuous_fst
    refine h1.continuousOn.inv₀ fun q hq => ?_
    exact_mod_cast (show (0 : ℝ) < q.1 from hq.1).ne'
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℂ =>
      if hρ : 0 < q.1 then
        (q.1 : ℂ)⁻¹ * (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α q.1 q.2 hr hρ * conjEntries k))
      else 0) ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun q => ?_)
  by_cases hρ : 0 < q.1
  · have hq' := hfun q hρ
    simp only [hq']
    by_cases hq : q ∈ Set.Icc ε R ×ˢ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hq, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      exact mul_le_mul (inv_anti₀ hε hq.1.1) (hC q) (norm_nonneg _) (inv_nonneg.2 hε.le)
    ·
      have hzero : rhoAvg φ r α hr q = 0 := by
        unfold rhoAvg
        rw [unitaryAverage_eq_angleQuad, angleQuad_eq_zero, mul_zero]
        intro ψ η ξ₁ ξ₂
        simp only [dif_pos hρ]
        by_contra hne
        obtain ⟨h1, h2, h3⟩ := hbd ψ η ξ₁ ξ₂ q.1 q.2 hρ hne
        exact hq ⟨⟨h1, h2⟩, mem_closedBall_zero_iff.2 h3⟩
      rw [hzero, mul_zero, norm_zero]
      exact hg0 q
  · simp only [dif_neg hρ, norm_zero]
    exact hg0 q

private theorem elliptic_core_at (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (r α : ℝ) (hr : 0 < r) (hα : Real.sin α ≠ 0) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hε0 : ε ≠ 0)
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hA : (Orbit.cayley ε hε0)⁻¹ * TwistedTorus.Rid.ridGL δ * conjEntries (Orbit.cayley ε hε0) = Orbit.antidiag r α hr)
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) (c : NNReal)
    (hμc : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) HaarRef.glOfℂ HaarRef.refMeasureℂ)
    (hKS : Measure.map SplitCore.ksChart ((volume.restrict SplitCore.ksDom).withDensity SplitCore.ksJ) =
      volume.restrict SplitCore.ksLocus)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w) :
    ∫ x, (fun y => φ (TwistedTorus.Rid.ridGL y)) (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) * (w x : ℂ) ∂μ =
      (((2 * Real.pi ^ 2 * c / cT : ℝ)) : ℂ) *
        ∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ,
          if hρ : 0 < ρ then
            (ρ : ℂ)⁻¹ * (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r α ρ u hr hρ * conjEntries k))
          else 0 := by
  refine (integral_translate φ r α hr ε hε0 δ hA μ hμ w).trans ?_
  refine (ell_transport φ hφ hφc r α hr hα ε hε hε0 δ hA μ hμ c hμc hKS τ cT hcT hτ w hw).trans ?_
  have hK : (((2 * Real.pi ^ 2 * c / cT : ℝ)) : ℂ) = (c : ℂ) * (((cT : ℝ) : ℂ))⁻¹ * ((2 * Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hK, mul_assoc ((c : ℂ) * (((cT : ℝ) : ℂ))⁻¹), ← integral_const_mul ((2 * Real.pi ^ 2 : ℝ) : ℂ)]
  first
    | refine congrArg (fun t : ℂ => (c : ℂ) * (((cT : ℝ) : ℂ))⁻¹ * t) ?_
    | congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ' : (0 : ℝ) < ρ := by
    first
      | exact hρ
      | exact Set.mem_Ioi.1 hρ
  simp only [dif_pos hρ', mul_assoc ((ρ : ℂ)⁻¹), integral_const_mul]
  rw [inflate φ hφ hφc r α hr hα ρ hρ']
  first
    | ring
    | (push_cast; ring)

private theorem elliptic_core (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : ((TwistedTorus.Rid.ridGL δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
        ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)])
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) (c : NNReal)
    (hμc : μ = c • @Measure.map _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) HaarRef.glOfℂ HaarRef.refMeasureℂ)
    (hKS : Measure.map SplitCore.ksChart ((volume.restrict SplitCore.ksDom).withDensity SplitCore.ksJ) =
      volume.restrict SplitCore.ksLocus)
    (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (cT : NNReal) (hcT : 0 < cT)
    (hτ : @Measure.map _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) (glBorelOf (ℂ ⊗[ℝ] ℝ))
        Subtype.val τ =
      cT • @Measure.map (ℝ × ℝ) _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ))
        (toTensorGL ℝ ℂ ℝ ∘ fun q : ℝ × ℝ => if hq : 0 < q.1 then ellipticElt q.1 q.2 hq else 1)
        ((volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi))).withDensity
          (fun q => ENNReal.ofReal q.1⁻¹)))
    (w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hw : IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ
      (fun y => φ (TwistedTorus.Rid.ridGL y)) w) :
    ∫ x, (fun y => φ (TwistedTorus.Rid.ridGL y)) (x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x) * (w x : ℂ) ∂μ =
      (((4 * Real.pi ^ 3 * c / (2 * Real.pi * cT) : ℝ)) : ℂ) *
        twistedEllipticTransform φ r θ / (8 * Real.sin θ ^ 2 : ℂ) := by
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  have hm : (-1 : ℝ) ≠ 0 := by norm_num
  have hθ' : Real.sin (-θ) ≠ 0 := by
    rw [Real.sin_neg]
    exact neg_ne_zero.2 hθ
  have hcPos : ((Orbit.cayley 1 h1 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; Complex.I, -Complex.I] := by
    rw [Orbit.coe_cayley]
    first
      | (simp; done)
      | (push_cast; simp; done)
  have hcNeg : ((Orbit.cayley (-1) hm : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, 1; -Complex.I, Complex.I] := by
    rw [Orbit.coe_cayley]
    first
      | (simp; done)
      | (push_cast; simp; done)
  have hAPos := Orbit.inv_mul_rot_mul_conj_of_cayley r θ hr (Orbit.cayley 1 h1) (TwistedTorus.Rid.ridGL δ) hcPos hδ
  have hANeg :=
    Orbit.inv_mul_rot_mul_conj_of_cayley_neg r θ hr (Orbit.cayley (-1) hm) (TwistedTorus.Rid.ridGL δ) hcNeg hδ
  have hPos := elliptic_core_at φ hφ hφc r θ hr hθ 1 (Or.inl rfl) h1 δ hAPos μ hμ c hμc hKS τ cT hcT hτ w hw
  have hNeg :=
    elliptic_core_at φ hφ hφc r (-θ) hr hθ' (-1) (Or.inr rfl) hm δ hANeg μ hμ c hμc hKS τ cT hcT hτ w hw

  have hsplit : ∀ (ρ : ℝ) (u : ℂ),
      (if hρ : 0 < ρ then
          (ρ : ℂ)⁻¹ * ((unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries k)) +
            (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r (-θ) ρ u hr hρ * conjEntries k)))
        else 0) =
        (if hρ : 0 < ρ then
            (ρ : ℂ)⁻¹ * (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries k))
          else 0) +
          (if hρ : 0 < ρ then
            (ρ : ℂ)⁻¹ * (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r (-θ) ρ u hr hρ * conjEntries k))
          else 0) := by
    intro ρ u
    by_cases hρ : 0 < ρ
    · simp only [dif_pos hρ, mul_add]
    · simp only [dif_neg hρ, add_zero]

  have hIntPos := integrable_rhoU φ hφ hφc r θ hr hθ
  have hIntNeg := integrable_rhoU φ hφ hφc r (-θ) hr hθ'
  have hadd := integral_add hIntPos hIntNeg
  have hprod := integral_prod _ (hIntPos.add hIntNeg)
  simp only [Pi.add_apply] at hprod
  rw [hprod, integral_prod _ hIntPos, integral_prod _ hIntNeg] at hadd
  have hconst : ∀ Y : ℂ,
      (((4 * Real.pi ^ 3 * c / (2 * Real.pi * cT) : ℝ)) : ℂ) *
          ((4 * Real.sin θ ^ 2 : ℂ) * Y) / (8 * Real.sin θ ^ 2 : ℂ) =
        (((2 * Real.pi ^ 2 * c / cT : ℝ)) : ℂ) * Y / 2 := by
    intro Y
    have hs : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ
    have hs' : Complex.sin (θ : ℂ) ≠ 0 := by
      first
        | (rw [← Complex.ofReal_sin]; exact hs)
        | (push_cast at hs; exact hs)
        | simpa using hs
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have hcT' : ((cT : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'
    push_cast
    first
      | (field_simp; done)
      | (field_simp; ring1)
  first
    | rw [twistedEllipticTransform, dif_pos hr]
    | (unfold twistedEllipticTransform; rw [dif_pos hr])
  simp only [hsplit]
  first
    | rw [hadd]
    | (simp only [] at hadd; rw [hadd])
    | erw [hadd]
  first
    | rw [hconst]
    | simp only [hconst]
  linear_combination (1 / 2 : ℂ) * hPos + (1 / 2 : ℂ) * hNeg

end TwistedOrbit.EllCore
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div.TwistedOrbit.SplitCore"

set_option autoImplicit false
open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (φ : GL (Fin 2) ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μ) :
    (∀ (a₁ a₂ : ℝ), 0 < a₁ → 0 < a₂ → a₁ ≠ a₂ →
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        ((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] →
        ∀ (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ →
          ∀ I : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ
              (fun y => φ
                (Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ)) I →
            I = (((
              (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
                  ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
                    !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] *
                      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}).toReal /
              (τ {t |
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1) ∧
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1)}).toReal : ℝ) : ℂ) *
                twistedSplitTransform φ a₁ a₂ / ((4 * |a₁ - a₂| : ℝ) : ℂ))) ∧
    (∀ (r θ : ℝ), 0 < r → Real.sin θ ≠ 0 →
      ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        ((Matrix.GeneralLinearGroup.map
          (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
            (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
          δ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
          !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
            ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] →
        ∀ (τ : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ →
          ∀ I : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ
              (fun y => φ
                (Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ)) I →
            I = (((
              (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
                  ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
                    !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] *
                      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}).toReal /
              (τ {t | (Matrix.det
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 2)}).toReal : ℝ) : ℂ) *
                twistedEllipticTransform φ r θ / (8 * Real.sin θ ^ 2 : ℂ))) := by
  obtain ⟨c, hc0, hμc₀⟩ := AutomorphicForm.GL2Twisted.exists_isHaarMeasure_eq_smul_map_normSq_det_sq_inv μ hμ
  have hμc := TwistedOrbit.HaarRef.eq_smul_map_glOfℂ μ c hμc₀
  have hKS : Measure.map TwistedOrbit.SplitCore.ksChart
      ((volume.restrict TwistedOrbit.SplitCore.ksDom).withDensity TwistedOrbit.SplitCore.ksJ) =
        volume.restrict TwistedOrbit.SplitCore.ksLocus :=
    AutomorphicForm.GL2Twisted.map_splitProductChart
  have hS : (μ {g | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
                  ∃ v : ℂ, v.re ∈ Set.Icc (0 : ℝ) 1 ∧ v.im ∈ Set.Icc (0 : ℝ) 1 ∧
                  ∃ k : AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℂ,
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
                    !![(b₁ : ℂ), (b₁ : ℂ) * v; 0, (b₂ : ℂ)] *
                      ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)}).toReal = 4 * Real.pi ^ 3 * c :=
    TwistedOrbit.MuBox.toReal_muBox μ c hμc hKS
  refine ⟨?_, ?_⟩
  · intro a₁ a₂ h₁ h₂ hne δ hδ τ hτ I hI
    obtain ⟨w, hw, rfl⟩ := hI
    have h0 : a₁ * a₂ ≠ 0 := mul_ne_zero h₁.ne' h₂.ne'
    obtain ⟨cT, hcT, hτc⟩ :=
      TwistedTorus.Split.exists_map_val_eq_smul_map_diagonal a₁ a₂ h0 hne h₁ h₂ δ hδ τ hτ
    have hT : (τ {t |
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1) ∧
                  (((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 1)}).toReal = cT :=
      TwistedTorus.Split.toReal_splitBox_of_map_val_eq a₁ a₂ h0 hne h₁ h₂ δ hδ τ hτ cT hτc
    refine (TwistedOrbit.SplitCore.split_core φ hφ hφc a₁ a₂ ⟨h₁, h₂⟩ hne δ hδ μ hμ c hμc hKS τ cT hcT hτc w
      hw).trans ?_
    rw [hS, hT]
  · intro r θ hr hθ δ hδ τ hτ I hI
    obtain ⟨w, hw, rfl⟩ := hI
    obtain ⟨cT, hcT, hτc⟩ := TwistedTorus.Elliptic.exists_map_val_eq_smul_map_rotation r θ hr hθ δ hδ τ hτ
    have hT : (τ {t | (Matrix.det
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
                    (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).re ∈
                    Set.Icc (1 : ℝ) (Real.exp 2)}).toReal = 2 * Real.pi * cT :=
      TwistedTorus.Elliptic.toReal_detBox_of_map_val_eq r θ hr hθ δ hδ τ hτ cT hτc
    refine (TwistedOrbit.EllCore.elliptic_core φ hφ hφc r θ hr hθ δ hδ μ hμ c hμc hKS τ cT hcT hτc w hw).trans ?_
    rw [hS, hT]

end S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div
end P2MW
export P2MW.S_AutomorphicForm_GL2Twisted_twistedOrbitalIntegral_eq_twistedSplitTransform_div_and_eq_twistedEllipticTransform_div (solution)
