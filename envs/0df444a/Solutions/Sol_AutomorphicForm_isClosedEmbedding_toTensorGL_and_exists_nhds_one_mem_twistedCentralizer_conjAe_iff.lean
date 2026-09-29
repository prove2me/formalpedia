-- Prove2me | solution 1 for AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/788215b8-e4cb-5898-a658-aa097f315611

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor toTensorGL sigmaTensor sigmaGL twistedCentralizer mem_sigmaCentralizer_iff"
namespace TwistedDescentD1a
p2m_open "AutomorphicForm"

open scoped TensorProduct

def ιr : ℝ →+* ℂ ⊗[ℝ] ℝ := (Algebra.TensorProduct.includeRight : ℝ →ₐ[ℝ] ℂ ⊗[ℝ] ℝ).toRingHom

def σr : ℂ ⊗[ℝ] ℝ →+* ℂ ⊗[ℝ] ℝ := sigmaTensor ℝ ℂ ℝ Complex.conjAe

def e : ℂ ⊗[ℝ] ℝ ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

end AutomorphicForm.TwistedDescentD1a

end

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor toTensorGL sigmaTensor sigmaGL twistedCentralizer mem_sigmaCentralizer_iff"
namespace TwistedDescentD1a
p2m_open "AutomorphicForm"

open ComplexConjugate

theorem toTensorGL_eq : toTensorGL ℝ ℂ ℝ = Matrix.GeneralLinearGroup.map ιr := rfl

theorem sigmaGL_eq : sigmaGL ℝ ℂ ℝ Complex.conjAe = Matrix.GeneralLinearGroup.map σr := rfl

theorem coe_toTensorGL (m : GL (Fin 2) ℝ) :
    ((toTensorGL ℝ ℂ ℝ m : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
      (m : Matrix (Fin 2) (Fin 2) ℝ).map ιr := rfl

theorem coe_sigmaGL (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    ((sigmaGL ℝ ℂ ℝ Complex.conjAe x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
      (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).map σr := rfl

theorem ιr_apply (a : ℝ) : ιr a = (1 : ℂ) ⊗ₜ[ℝ] a := rfl

theorem σr_tmul (w : ℂ) (b : ℝ) : σr (w ⊗ₜ[ℝ] b) = (conj w) ⊗ₜ[ℝ] b := by
  simp [σr, sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem e_tmul (w : ℂ) (b : ℝ) : e (w ⊗ₜ[ℝ] b) = (b : ℂ) * w := by
  simp [e, Algebra.TensorProduct.rid_tmul, Complex.real_smul]

theorem e_ιr (a : ℝ) : e (ιr a) = (a : ℂ) := by
  rw [ιr_apply, e_tmul, mul_one]

theorem e_σr (z : ℂ ⊗[ℝ] ℝ) : e (σr z) = conj (e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => rw [σr_tmul, e_tmul, e_tmul, map_mul, Complex.conj_ofReal]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem σr_ιr (a : ℝ) : σr (ιr a) = ιr a := by
  rw [ιr_apply, σr_tmul, map_one]

theorem σr_σr (z : ℂ ⊗[ℝ] ℝ) : σr (σr z) = z := by
  apply e.injective
  rw [e_σr, e_σr, Complex.conj_conj]

theorem ιr_injective : Function.Injective ιr := by
  intro a b h
  have h' := congrArg e h
  rwa [e_ιr, e_ιr, Complex.ofReal_inj] at h'

def reT (z : ℂ ⊗[ℝ] ℝ) : ℝ := (e z).re

theorem reT_ιr (a : ℝ) : reT (ιr a) = a := by
  simp [reT, e_ιr]

theorem ιr_reT_of_σr_eq {z : ℂ ⊗[ℝ] ℝ} (h : σr z = z) : ιr (reT z) = z := by
  apply e.injective
  rw [e_ιr, reT]
  have h' : conj (e z) = e z := by rw [← e_σr, h]
  exact Complex.conj_eq_iff_re.mp h'

theorem exists_eq_ιr_of_σr_eq {z : ℂ ⊗[ℝ] ℝ} (h : σr z = z) : ∃ a : ℝ, z = ιr a :=
  ⟨reT z, (ιr_reT_of_σr_eq h).symm⟩

theorem σr_comp_ιr : (σr : ℂ ⊗[ℝ] ℝ → ℂ ⊗[ℝ] ℝ) ∘ (ιr : ℝ → ℂ ⊗[ℝ] ℝ) = ιr :=
  funext σr_ιr

theorem σr_comp_σr : (σr : ℂ ⊗[ℝ] ℝ → ℂ ⊗[ℝ] ℝ) ∘ (σr : ℂ ⊗[ℝ] ℝ → ℂ ⊗[ℝ] ℝ) = id :=
  funext σr_σr

theorem reT_comp_ιr : reT ∘ (ιr : ℝ → ℂ ⊗[ℝ] ℝ) = id :=
  funext reT_ιr

section Matrices

variable {S : Type} [CommRing S]

theorem mul_self_eq_two (T : Matrix (Fin 2) (Fin 2) S) :
    T * T = Matrix.trace T • T - T.det • (1 : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem commute_of_commute_mul_self {T X : Matrix (Fin 2) (Fin 2) S} (hu : IsUnit (Matrix.trace T))
    (h : X * (T * T) = (T * T) * X) : X * T = T * X := by
  rw [mul_self_eq_two, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, one_mul, sub_left_inj] at h
  exact (hu.smul_left_cancel).mp h

end Matrices

theorem map_σr_map_ιr (A : Matrix (Fin 2) (Fin 2) ℝ) : (A.map ιr).map σr = A.map ιr := by
  rw [Matrix.map_map, σr_comp_ιr]

theorem map_σr_map_σr (B : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) : (B.map σr).map σr = B := by
  rw [Matrix.map_map, σr_comp_σr, Matrix.map_id]

theorem map_ιr_map_reT_of_map_σr_eq {B : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)} (h : B.map σr = B) :
    (B.map reT).map ιr = B := by
  ext i j
  exact ιr_reT_of_σr_eq (congrFun (congrFun h i) j)

theorem sigmaGL_toTensorGL (m : GL (Fin 2) ℝ) :
    sigmaGL ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ m) = toTensorGL ℝ ℂ ℝ m :=
  Units.ext (by rw [coe_sigmaGL, coe_toTensorGL, map_σr_map_ιr])

theorem coe_toTensorGL_scalar (d : ℝˣ) :
    ((toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
        Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = Matrix.scalar (Fin 2) (ιr (d : ℝ)) := by
  rw [coe_toTensorGL]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]
  · simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, hij]

theorem toTensorGL_scalar_mul_comm (d : ℝˣ) (y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) * y =
      y * toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_toTensorGL_scalar]
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem mem_twistedCentralizer_mul_scalar_iff (d : ℝˣ) (t : GL (Fin 2) ℝ) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
      x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ t) := by
  rw [twistedCentralizer, twistedCentralizer, mem_sigmaCentralizer_iff, mem_sigmaCentralizer_iff, map_mul]
  have hc : ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) * y =
        y * toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) :=
    toTensorGL_scalar_mul_comm d
  have key : x * (toTensorGL ℝ ℂ ℝ t * toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) *
        ((sigmaGL ℝ ℂ ℝ Complex.conjAe) x)⁻¹ =
      x * toTensorGL ℝ ℂ ℝ t * ((sigmaGL ℝ ℂ ℝ Complex.conjAe) x)⁻¹ *
        toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by
    rw [← mul_assoc x, mul_assoc (x * toTensorGL ℝ ℂ ℝ t), hc, ← mul_assoc]
  rw [key]
  exact mul_left_inj _

theorem mem_twistedCentralizer_toTensorGL_iff (t : GL (Fin 2) ℝ)
    (ht : Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ t) ↔
      ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m := by
  rw [twistedCentralizer, mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h

    have hM : (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * (t : Matrix (Fin 2) (Fin 2) ℝ).map ιr =
        (t : Matrix (Fin 2) (Fin 2) ℝ).map ιr * (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).map σr := by
      have := congrArg (Units.val : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → _) h
      rwa [Units.val_mul, Units.val_mul, coe_toTensorGL, coe_sigmaGL] at this

    have hM' : (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).map σr * (t : Matrix (Fin 2) (Fin 2) ℝ).map ιr =
        (t : Matrix (Fin 2) (Fin 2) ℝ).map ιr * (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
      have := congrArg (fun B : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) => B.map σr) hM
      simp only [Matrix.map_mul, map_σr_map_ιr, map_σr_map_σr] at this
      exact this

    have hTT : (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) *
          ((t : Matrix (Fin 2) (Fin 2) ℝ).map ιr * (t : Matrix (Fin 2) (Fin 2) ℝ).map ιr) =
        ((t : Matrix (Fin 2) (Fin 2) ℝ).map ιr * (t : Matrix (Fin 2) (Fin 2) ℝ).map ιr) *
          (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
      rw [← mul_assoc, hM, mul_assoc, hM', mul_assoc]
    have htr : Matrix.trace ((t : Matrix (Fin 2) (Fin 2) ℝ).map ιr) = ιr (Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ)) := by
      simp [Matrix.trace_fin_two]
    have hu : IsUnit (Matrix.trace ((t : Matrix (Fin 2) (Fin 2) ℝ).map ιr)) := by
      rw [htr]; exact (isUnit_iff_ne_zero.mpr ht).map ιr
    have hXT := commute_of_commute_mul_self hu hTT

    have hfix : (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).map σr = (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
      have hTu : IsUnit ((t : Matrix (Fin 2) (Fin 2) ℝ).map ιr) := (toTensorGL ℝ ℂ ℝ t).isUnit
      exact hTu.mul_left_cancel (hM.symm.trans hXT)

    set A : Matrix (Fin 2) (Fin 2) ℝ := (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).map reT with hA
    have hAx : A.map ιr = (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := map_ιr_map_reT_of_map_σr_eq hfix
    have hAu : IsUnit A := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h0
      have hdx : IsUnit (x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)).det := (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
      rw [← hAx] at hdx
      change IsUnit (ιr.mapMatrix A).det at hdx
      rw [← RingHom.map_det, h0, map_zero] at hdx
      exact not_isUnit_zero hdx
    refine ⟨hAu.unit, ?_, Units.ext ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Units.ext
      apply Matrix.map_injective ιr_injective
      change ((hAu.unit : Matrix (Fin 2) (Fin 2) ℝ) * (t : Matrix (Fin 2) (Fin 2) ℝ)).map ιr =
        ((t : Matrix (Fin 2) (Fin 2) ℝ) * (hAu.unit : Matrix (Fin 2) (Fin 2) ℝ)).map ιr
      rw [Matrix.map_mul, Matrix.map_mul, IsUnit.unit_spec, hAx, hXT]
    · rw [coe_toTensorGL, IsUnit.unit_spec, hAx]
  · rintro ⟨m, hm, rfl⟩
    rw [sigmaGL_toTensorGL, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.mp hm

theorem mem_twistedCentralizer_iff (d : ℝˣ) (t : GL (Fin 2) ℝ)
    (ht : Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
      ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m :=
  (mem_twistedCentralizer_mul_scalar_iff d t x).trans (mem_twistedCentralizer_toTensorGL_iff t ht x)

theorem isOpen_setOf_trace_ne_zero :
    IsOpen {t : GL (Fin 2) ℝ | Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_trace Units.continuous_val) continuous_const

theorem setOf_trace_ne_zero_mem_nhds_one :
    {t : GL (Fin 2) ℝ | Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0} ∈ nhds (1 : GL (Fin 2) ℝ) := by
  refine isOpen_setOf_trace_ne_zero.mem_nhds ?_
  show Matrix.trace ((1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0
  rw [Units.val_one, Matrix.trace_one]
  norm_num

def eR : (ℂ ⊗[ℝ] ℝ) ≃ₗ[ℝ] ℂ :=
  (TensorProduct.RightActions.Module.TensorProduct.comm ℝ ℝ ℂ).symm.trans (TensorProduct.lid ℝ ℂ)

theorem eR_apply (z : ℂ ⊗[ℝ] ℝ) : eR z = e z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w b =>
      simp [eR, e_tmul, TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul,
        TensorProduct.lid_tmul, Complex.real_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem continuous_e : Continuous e := by
  have h : Continuous eR.toLinearMap := IsModuleTopology.continuous_of_linearMap eR.toLinearMap
  have hfun : (fun z : ℂ ⊗[ℝ] ℝ => e z) = fun z => eR.toLinearMap z := funext fun z => (eR_apply z).symm
  show Continuous fun z : ℂ ⊗[ℝ] ℝ => e z
  rw [hfun]
  exact h

theorem continuous_e_symm : Continuous e.symm := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  have h : Continuous eR.symm.toLinearMap := LinearMap.continuous_of_finiteDimensional eR.symm.toLinearMap
  have hfun : (fun c : ℂ => e.symm c) = fun c => eR.symm.toLinearMap c := funext fun c => by
    apply eR.injective
    change eR (e.symm c) = eR (eR.symm c)
    rw [LinearEquiv.apply_symm_apply, eR_apply, RingEquiv.apply_symm_apply]
  show Continuous fun c : ℂ => e.symm c
  rw [hfun]
  exact h

theorem continuous_ιr : Continuous ιr := by
  have h : (ιr : ℝ → ℂ ⊗[ℝ] ℝ) = fun a : ℝ => e.symm (a : ℂ) := by
    funext a
    apply e.injective
    rw [e_ιr, RingEquiv.apply_symm_apply]
  rw [h]
  exact continuous_e_symm.comp Complex.continuous_ofReal

theorem continuous_reT : Continuous reT :=
  Complex.continuous_re.comp continuous_e

theorem isClosedEmbedding_map_ιr :
    Topology.IsClosedEmbedding (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.map ιr) := by
  haveI := t2Space_tensor ℝ ℂ ℝ
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℂ ⊗[ℝ] ℝ))
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun B : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) => B.map reT) (fun A => ?_) ?_ ?_
  · show (A.map ιr).map reT = A
    rw [Matrix.map_map, reT_comp_ιr, Matrix.map_id]
  · exact Continuous.matrix_map continuous_id continuous_reT
  · exact Continuous.matrix_map continuous_id continuous_ιr

theorem isClosedEmbedding_toTensorGL : Topology.IsClosedEmbedding (toTensorGL ℝ ℂ ℝ) := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := t2Space_tensor ℝ ℂ ℝ
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℂ ⊗[ℝ] ℝ))
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℝ))
  have hF : Topology.IsClosedEmbedding (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.map ιr) := isClosedEmbedding_map_ιr
  have hG : Topology.IsClosedEmbedding
      (fun A : (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ => MulOpposite.op ((MulOpposite.unop A).map ιr)) :=
    (MulOpposite.opHomeomorph.isClosedEmbedding.comp hF).comp MulOpposite.opHomeomorph.symm.isClosedEmbedding
  have hcomp : (Units.embedProduct (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) : _ → _) ∘ (toTensorGL ℝ ℂ ℝ : _ → _) =
      Prod.map (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.map ιr)
          (fun A : (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ => MulOpposite.op ((MulOpposite.unop A).map ιr)) ∘
        (Units.embedProduct (Matrix (Fin 2) (Fin 2) ℝ) : _ → _) := by
    funext u
    rfl
  have h : Topology.IsClosedEmbedding
      ((Units.embedProduct (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) : _ → _) ∘ (toTensorGL ℝ ℂ ℝ : _ → _)) := by
    rw [hcomp]
    exact (hF.prodMap hG).comp Units.isClosedEmbedding_embedProduct
  exact Units.isClosedEmbedding_embedProduct.of_comp_iff.mp h

end AutomorphicForm.TwistedDescentD1a

end

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (d : ℝˣ) :
    Topology.IsClosedEmbedding (toTensorGL ℝ ℂ ℝ) ∧
    ∃ U ∈ nhds (1 : GL (Fin 2) ℝ),
      (∀ t ∈ U, ∀ x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        x ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) ↔
          ∃ m : GL (Fin 2) ℝ, m ∈ Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) ∧ x = toTensorGL ℝ ℂ ℝ m) :=
  ⟨AutomorphicForm.TwistedDescentD1a.isClosedEmbedding_toTensorGL, _,
    AutomorphicForm.TwistedDescentD1a.setOf_trace_ne_zero_mem_nhds_one,
    fun t ht x => AutomorphicForm.TwistedDescentD1a.mem_twistedCentralizer_iff d t ht x⟩

end S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff
end P2MW
export P2MW.S_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_mem_twistedCentralizer_conjAe_iff (solution)
