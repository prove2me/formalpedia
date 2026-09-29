-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/55088c59-dbb5-5976-9ef4-b2fa599998fc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
import Theorems.Thm_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
import Theorems.Thm_AutomorphicForm_exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg
import Theorems.Thm_MeasureTheory_exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
import Theorems.Thm_MeasureTheory_tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
import Theorems.Thm_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL glBorelOf borelSpace_glBorelOf toTensorGL sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn IsRegularSemisimple mem_sigmaCentralizer_iff mem_sigmaCentralizer_iff_inv exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg"
p2m_open "AutomorphicForm"
namespace TwLimH

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  let ι := Module.Free.ChooseBasisIndex A (L ⊗[K] A)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A (L ⊗[K] A)
  let b : Module.Basis ι A (L ⊗[K] A) := Module.Free.chooseBasis A (L ⊗[K] A)
  let e : (L ⊗[K] A) ≃ₗ[A] (ι → A) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (ι → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

end TensorTopology

section GroupIdentities

variable {G : Type*} [Group G]

theorem conj_mul_of_central (z k u : G) (hz : ∀ g : G, g * z = z * g) : (z * k)⁻¹ * u * (z * k) = k⁻¹ * u * k := by
  rw [mul_inv_rev, show k⁻¹ * z⁻¹ * u * (z * k) = k⁻¹ * (z⁻¹ * (u * z)) * k by simp only [mul_assoc], hz u,
    inv_mul_cancel_left]

theorem twisted_conj_mul (s : G →* G) (δ t d u : G) (ht : t⁻¹ * δ * s t = δ) :
    (t * d)⁻¹ * (u * δ) * s (t * d) = d⁻¹ * ((t⁻¹ * u * t) * δ) * s d := by
  rw [mul_inv_rev, map_mul]
  calc d⁻¹ * t⁻¹ * (u * δ) * (s t * s d) = d⁻¹ * (t⁻¹ * u * t * (t⁻¹ * δ * s t)) * s d := by group
    _ = d⁻¹ * ((t⁻¹ * u * t) * δ) * s d := by rw [ht]

theorem twisted_conj_one (s : G →* G) (δ t d : G) (ht : t⁻¹ * δ * s t = δ) :
    (t * d)⁻¹ * δ * s (t * d) = d⁻¹ * δ * s d := by
  rw [mul_inv_rev, map_mul]
  calc d⁻¹ * t⁻¹ * δ * (s t * s d) = d⁻¹ * (t⁻¹ * δ * s t) * s d := by group
    _ = d⁻¹ * δ * s d := by rw [ht]

end GroupIdentities

section SubgroupCover

variable {Γ : Type*} [Group Γ]

theorem comm_of_coe_central (Tg : Subgroup Γ) (z g : Tg) (hz : ∀ x : Γ, x * (z : Γ) = (z : Γ) * x) :
    g * z = z * g :=
  Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hz g)

theorem comm_of_coe_coe_central (Tg : Subgroup Γ) (H : Subgroup Tg) (z g : H)
    (hz : ∀ x : Γ, x * ((z : Tg) : Γ) = ((z : Tg) : Γ) * x) : g * z = z * g :=
  Subtype.ext (comm_of_coe_central Tg (z : Tg) (g : Tg) hz)

theorem exists_mul_of_cover (Tg : Subgroup Γ) (Z C : Set Γ) (hZ : Z ⊆ Tg)
    (hcov : ∀ t ∈ Tg, ∃ z ∈ Z, ∃ k ∈ C, t = z * k) (g : Tg) :
    ∃ z ∈ {z : Tg | (z : Γ) ∈ Z}, ∃ k ∈ {k : Tg | (k : Γ) ∈ C}, g = z * k := by
  obtain ⟨z, hz, k, hk, hgk⟩ := hcov g g.2
  have hkT : k ∈ Tg := by
    have h : k = z⁻¹ * g := by rw [hgk, inv_mul_cancel_left]
    rw [h]
    exact Tg.mul_mem (Tg.inv_mem (hZ hz)) g.2
  exact ⟨⟨z, hZ hz⟩, hz, ⟨k, hkT⟩, hk, Subtype.ext hgk⟩

theorem exists_mul_of_cover_subgroupOf (Tg Sg : Subgroup Γ) (hST : Sg ≤ Tg) (Z C : Set Γ) (hZ : Z ⊆ Sg)
    (hcov : ∀ t ∈ Tg, ∃ z ∈ Z, ∃ k ∈ C, t = z * k) (g : Sg.subgroupOf Tg) :
    ∃ z ∈ {z : Sg.subgroupOf Tg | ((z : Tg) : Γ) ∈ Z}, ∃ k ∈ {k : Sg.subgroupOf Tg | ((k : Tg) : Γ) ∈ C},
      g = z * k := by
  obtain ⟨z, hz, k, hk, hgk⟩ := hcov ((g : Tg) : Γ) (g : Tg).2
  have hzS : (⟨z, hST (hZ hz)⟩ : Tg) ∈ Sg.subgroupOf Tg := by
    rw [Subgroup.mem_subgroupOf]
    exact hZ hz
  refine ⟨⟨⟨z, hST (hZ hz)⟩, hzS⟩, hz, ⟨⟨z, hST (hZ hz)⟩, hzS⟩⁻¹ * g, ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv, hgk, inv_mul_cancel_left]
  exact hk

theorem exists_subgroupOf_mul_of_cover (Tg Sg : Subgroup Γ) (hST : Sg ≤ Tg) (Z C : Set Γ) (hZ : Z ⊆ Sg)
    (hcov : ∀ t ∈ Tg, ∃ z ∈ Z, ∃ k ∈ C, t = z * k) (g : Tg) :
    ∃ s : Sg.subgroupOf Tg, ∃ k ∈ {k : Tg | (k : Γ) ∈ C}, g = (s : Tg) * k := by
  obtain ⟨z, hz, k, hk, hgk⟩ := hcov g g.2
  have hzS : (⟨z, hST (hZ hz)⟩ : Tg) ∈ Sg.subgroupOf Tg := by
    rw [Subgroup.mem_subgroupOf]
    exact hZ hz
  have hkT : k ∈ Tg := by
    have h : k = z⁻¹ * g := by rw [hgk, inv_mul_cancel_left]
    rw [h]
    exact Tg.mul_mem (Tg.inv_mem (hST (hZ hz))) g.2
  exact ⟨⟨⟨z, hST (hZ hz)⟩, hzS⟩, ⟨k, hkT⟩, hk, Subtype.ext hgk⟩

end SubgroupCover

section Local

local notation "𝔼" => ℂ ⊗[ℝ] ℝ
local notation "G𝔼" => GL (Fin 2) (ℂ ⊗[ℝ] ℝ)

def scalarE (e : ℝˣ) : G𝔼 := toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) e)

theorem scalarE_val (e : ℝˣ) :
    ((scalarE e : G𝔼) : Matrix (Fin 2) (Fin 2) 𝔼) = Matrix.scalar (Fin 2) ((1 : ℂ) ⊗ₜ[ℝ] (e : ℝ)) := by
  change RingHom.mapMatrix _ (Matrix.scalar (Fin 2) (e : ℝ)) = _
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Algebra.TensorProduct.includeRight_apply]
  · simp [hij]

theorem mul_scalarE_comm (e : ℝˣ) (g : G𝔼) : g * scalarE e = scalarE e * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalarE_val]
  exact ((Matrix.scalar_commute ((1 : ℂ) ⊗ₜ[ℝ] (e : ℝ)) (fun r' => Commute.all _ r') (g : Matrix (Fin 2) (Fin 2) 𝔼)).eq).symm

theorem sigmaTensor_one_tmul (x : ℝ) : sigmaTensor ℝ ℂ ℝ Complex.conjAe ((1 : ℂ) ⊗ₜ[ℝ] x) = (1 : ℂ) ⊗ₜ[ℝ] x := by
  rw [sigmaTensor]
  show (Algebra.TensorProduct.map Complex.conjAe.toAlgHom (AlgHom.id ℝ ℝ)) ((1 : ℂ) ⊗ₜ[ℝ] x) = (1 : ℂ) ⊗ₜ[ℝ] x
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigmaGL_scalarE (e : ℝˣ) : sigmaGL ℝ ℂ ℝ Complex.conjAe (scalarE e) = scalarE e := by
  apply Units.ext
  change (sigmaTensor ℝ ℂ ℝ Complex.conjAe).mapMatrix ((scalarE e : G𝔼) : Matrix (Fin 2) (Fin 2) 𝔼) = _
  rw [scalarE_val]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [sigmaTensor_one_tmul]
  · simp [hij]

theorem scalarE_mem_twistedCentralizer (e : ℝˣ) (δ : G𝔼) : scalarE e ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ := by
  rw [twistedCentralizer, mem_sigmaCentralizer_iff, sigmaGL_scalarE, ← mul_scalarE_comm, mul_inv_cancel_right]

end Local

section StrMap

theorem continuous_ringHom_of_tensor (K L A B : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [CommRing A] [Algebra K A] [TopologicalSpace A] [Ring B] [TopologicalSpace B]
    [IsTopologicalRing B] (f : L ⊗[K] A →+* B) (hf : Continuous (f.comp (algebraMap A (L ⊗[K] A)))) :
    Continuous f :=
  IsModuleTopology.continuous_of_ringHom f hf

theorem continuous_ridHom :
    Continuous
      (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom := by
  refine continuous_ringHom_of_tensor ℝ ℂ ℝ ℂ _ ?_
  convert Complex.continuous_ofReal using 1
  funext x
  change x • (1 : ℂ) = (x : ℂ)
  rw [Complex.real_smul, mul_one]

def strGL : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) →* GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.map
    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom

def strGLinv : GL (Fin 2) ℂ →* GL (Fin 2) (ℂ ⊗[ℝ] ℝ) :=
  Matrix.GeneralLinearGroup.map
    (@AlgEquiv.toRingEquiv ℝ ℂ (ℂ ⊗[ℝ] ℝ) _ _ _ _ Algebra.TensorProduct.leftAlgebra
        (@AlgEquiv.symm ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ))).toRingHom

theorem strGL_strGLinv (g : GL (Fin 2) ℂ) : strGL (strGLinv g) = g := by
  apply Units.ext
  ext i j
  exact @AlgEquiv.apply_symm_apply ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)

theorem strGLinv_strGL (g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : strGLinv (strGL g) = g := by
  apply Units.ext
  ext i j
  exact @AlgEquiv.symm_apply_apply ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ) ((g : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j)

theorem continuous_ridInv :
    Continuous
      (@AlgEquiv.toRingEquiv ℝ ℂ (ℂ ⊗[ℝ] ℝ) _ _ _ _ Algebra.TensorProduct.leftAlgebra
        (@AlgEquiv.symm ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ))).toRingHom := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  have h1 : Continuous fun r : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] r : ℂ ⊗[ℝ] ℝ) := continuous_algebraMap ℝ (ℂ ⊗[ℝ] ℝ)
  have h2 : Continuous fun r : ℝ => (Complex.I ⊗ₜ[ℝ] r : ℂ ⊗[ℝ] ℝ) := by
    have e : (fun r : ℝ => (Complex.I ⊗ₜ[ℝ] r : ℂ ⊗[ℝ] ℝ)) =
        fun r : ℝ => (Complex.I ⊗ₜ[ℝ] (1 : ℝ) : ℂ ⊗[ℝ] ℝ) * ((1 : ℂ) ⊗ₜ[ℝ] r) := by
      funext r
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact continuous_const.mul h1
  have e : ((@AlgEquiv.toRingEquiv ℝ ℂ (ℂ ⊗[ℝ] ℝ) _ _ _ _ Algebra.TensorProduct.leftAlgebra
        (@AlgEquiv.symm ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ))).toRingHom : ℂ → ℂ ⊗[ℝ] ℝ) =
      fun z : ℂ => ((1 : ℂ) ⊗ₜ[ℝ] z.re : ℂ ⊗[ℝ] ℝ) + Complex.I ⊗ₜ[ℝ] z.im := by
    funext z
    have k1 : ∀ r : ℝ, ((r : ℂ) ⊗ₜ[ℝ] (1 : ℝ) : ℂ ⊗[ℝ] ℝ) = (1 : ℂ) ⊗ₜ[ℝ] r := fun r => by
      rw [show ((r : ℂ)) = r • (1 : ℂ) by rw [Complex.real_smul, mul_one], TensorProduct.smul_tmul, smul_eq_mul,
        mul_one]
    have k2 : ∀ r : ℝ, (((r : ℂ) * Complex.I) ⊗ₜ[ℝ] (1 : ℝ) : ℂ ⊗[ℝ] ℝ) = Complex.I ⊗ₜ[ℝ] r := fun r => by
      rw [show (r : ℂ) * Complex.I = r • Complex.I by rw [Complex.real_smul], TensorProduct.smul_tmul, smul_eq_mul,
        mul_one]
    change z ⊗ₜ[ℝ] (1 : ℝ) = _
    conv_lhs => rw [← Complex.re_add_im z]
    rw [TensorProduct.add_tmul, k1, k2]
  rw [e]
  exact (h1.comp Complex.continuous_re).add (h2.comp Complex.continuous_im)

theorem continuous_strGLinv : Continuous (strGLinv : GL (Fin 2) ℂ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := by
  unfold strGLinv Matrix.GeneralLinearGroup.map
  exact Continuous.units_map _ (continuous_id.matrix_map continuous_ridInv)

theorem continuous_strGL : Continuous (strGL : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → GL (Fin 2) ℂ) := by
  unfold strGL Matrix.GeneralLinearGroup.map
  exact Continuous.units_map _ (continuous_id.matrix_map continuous_ridHom)

def strHomeo : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) ≃ₜ GL (Fin 2) ℂ where
  toFun := strGL
  invFun := strGLinv
  left_inv := strGLinv_strGL
  right_inv := strGL_strGLinv
  continuous_toFun := continuous_strGL
  continuous_invFun := continuous_strGLinv

theorem continuous_and_hasCompactSupport_comp_strGL (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ) :
    Continuous (fun z : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => φ (strGL z)) ∧
      HasCompactSupport (fun z : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => φ (strGL z)) := by
  obtain ⟨⟨Φ, hΦ, hφΦ⟩, hφc⟩ := hφ
  have hφcont : Continuous φ := by
    have : φ = fun g : GL (Fin 2) ℂ => Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) := funext hφΦ
    rw [this]
    exact hΦ.continuous.comp (continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j)
  exact ⟨hφcont.comp continuous_strGL, hφc.comp_homeomorph strHomeo⟩

end StrMap

section Assembly

local notation "𝔼" => ℂ ⊗[ℝ] ℝ
local notation "G𝔼" => GL (Fin 2) (ℂ ⊗[ℝ] ℝ)
local notation "σ'" => sigmaGL ℝ ℂ ℝ Complex.conjAe

theorem integrand_mul_left (δ' : G𝔼) (φv : G𝔼 → ℂ) (t : G𝔼) (ht : t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ') (x : G𝔼) :
    φv ((t * x)⁻¹ * δ' * σ' (t * x)) = φv (x⁻¹ * δ' * σ' x) := by
  have key : t⁻¹ * δ' * σ' t = δ' := mem_sigmaCentralizer_iff_inv.1 ht
  have h : (t * x)⁻¹ * δ' * σ' (t * x) = x⁻¹ * δ' * σ' x := by
    calc (t * x)⁻¹ * δ' * σ' (t * x) = x⁻¹ * (t⁻¹ * δ' * σ' t) * σ' x := by
          simp only [mul_inv_rev, map_mul, mul_assoc]
      _ = x⁻¹ * δ' * σ' x := by rw [key]
  rw [h]

def twI (φt : G𝔼 → ℂ) (δ' v x : G𝔼) : ℂ := φt (x⁻¹ * (v * δ') * σ' x)

theorem twI_apply (φt : G𝔼 → ℂ) (δ' v x : G𝔼) : twI φt δ' v x = φt (x⁻¹ * (v * δ') * σ' x) := rfl

theorem twI_one (φt : G𝔼 → ℂ) (δ' x : G𝔼) : twI φt δ' 1 x = φt (x⁻¹ * δ' * σ' x) := by
  rw [twI_apply, one_mul]

theorem continuous_twI (φt : G𝔼 → ℂ) (hφ : Continuous φt) (δ' v : G𝔼) :
    Continuous (twI φt δ' v) := by
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  show Continuous fun x : G𝔼 => φt (x⁻¹ * (v * δ') * σ' x)
  exact hφ.comp ((continuous_inv.mul continuous_const).mul (continuous_sigmaGL ℝ ℂ ℝ Complex.conjAe))

theorem continuous_twI₂ (φt : G𝔼 → ℂ) (hφ : Continuous φt) (δ' : G𝔼) :
    Continuous fun p : G𝔼 × G𝔼 => twI φt δ' p.1 p.2 := by
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  show Continuous fun p : G𝔼 × G𝔼 => φt (p.2⁻¹ * (p.1 * δ') * σ' p.2)
  exact hφ.comp (((continuous_snd.inv).mul (continuous_fst.mul continuous_const)).mul
    ((continuous_sigmaGL ℝ ℂ ℝ Complex.conjAe).comp continuous_snd))

theorem twI_mul_left (φt : G𝔼 → ℂ) (δ' v t : G𝔼) (ht : t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (v * δ')) (x : G𝔼) :
    twI φt δ' v (t * x) = twI φt δ' v x := by
  rw [twI_apply, twI_apply]
  exact integrand_mul_left (v * δ') φt t ht x

theorem continuous_twI_restrict (φt : G𝔼 → ℂ) (hφ : Continuous φt) (δ' : G𝔼) (K : Set G𝔼) :
    Continuous fun p : G𝔼 × ↥K => twI φt δ' p.1 (p.2 : G𝔼) := by
  show Continuous ((fun q : G𝔼 × G𝔼 => twI φt δ' q.1 q.2) ∘ fun p : G𝔼 × ↥K => (p.1, (p.2 : G𝔼)))
  exact (continuous_twI₂ φt hφ δ').comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem continuous_fibre {H : Subgroup G𝔼} (f : G𝔼 → ℂ) (hf : Continuous f) (β : ↥H → ℝ) (hβ : Continuous β) (x : G𝔼) :
    Continuous fun t : ↥H => f ((t : G𝔼) * x) * (β t : ℂ) := by
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  exact (hf.comp (continuous_subtype_val.mul continuous_const)).mul (Complex.continuous_ofReal.comp hβ)

theorem hasCompactSupport_fibre {H : Subgroup G𝔼} (f : G𝔼 → ℂ) (β : ↥H → ℝ) (hβ : HasCompactSupport β) (x : G𝔼) :
    HasCompactSupport fun t : ↥H => f ((t : G𝔼) * x) * (β t : ℂ) :=
  (hβ.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_left

theorem continuous_translate {f : G𝔼 → ℂ} (hf : Continuous f) (t : G𝔼) (b : ℂ) :
    Continuous fun x : G𝔼 => f (t * x) * b := by
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  exact (hf.comp (continuous_const.mul continuous_id)).mul continuous_const

section Fibre

variable {H : Subgroup G𝔼} [MeasurableSpace ↥H] [hHb : BorelSpace ↥H] (τ : Measure ↥H) [hτc : IsFiniteMeasureOnCompacts τ]

theorem integrable_fibre (f : G𝔼 → ℂ) (hf : Continuous f) (β : ↥H → ℝ) (hβc : Continuous β)
    (hβsupp : HasCompactSupport β) (x : G𝔼) :
    Integrable (fun t : ↥H => f ((t : G𝔼) * x) * (β t : ℂ)) τ :=
  (continuous_fibre f hf β hβc x).integrable_of_hasCompactSupport (hasCompactSupport_fibre f β hβsupp x)

theorem fibre_average_of_invariant (f : G𝔼 → ℂ) (β : ↥H → ℝ) (x : G𝔼)
    (hinv : ∀ t : ↥H, f ((t : G𝔼) * x) = f x) :
    ∫ t : ↥H, f ((t : G𝔼) * x) * (β t : ℂ) ∂τ = f x * ((∫ t : ↥H, β t ∂τ : ℝ) : ℂ) := by
  have : (fun t : ↥H => f ((t : G𝔼) * x) * (β t : ℂ)) = fun t : ↥H => f x * (β t : ℂ) := by
    funext t; rw [hinv t]
  rw [this, integral_const_mul, integral_complex_ofReal]

theorem norm_fibre_average_sub_le (f g : G𝔼 → ℂ) (hf : Continuous f) (hg : Continuous g) (β : ↥H → ℝ)
    (hβ0 : ∀ t, 0 ≤ β t) (hβc : Continuous β) (hβsupp : HasCompactSupport β) (x : G𝔼) (ε' : ℝ)
    (hclose : ∀ t : ↥H, t ∈ tsupport β → ‖f ((t : G𝔼) * x) - g ((t : G𝔼) * x)‖ ≤ ε') :
    ‖(∫ t : ↥H, f ((t : G𝔼) * x) * (β t : ℂ) ∂τ) - ∫ t : ↥H, g ((t : G𝔼) * x) * (β t : ℂ) ∂τ‖ ≤ ε' * ∫ t : ↥H, β t ∂τ := by
  rw [← integral_sub (integrable_fibre τ f hf β hβc hβsupp x) (integrable_fibre τ g hg β hβc hβsupp x)]
  have hpt : ∀ t : ↥H, ‖f ((t : G𝔼) * x) * (β t : ℂ) - g ((t : G𝔼) * x) * (β t : ℂ)‖ ≤ ε' * β t := by
    intro t
    rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ0 t)]
    by_cases ht : t ∈ tsupport β
    · exact mul_le_mul_of_nonneg_right (hclose t ht) (hβ0 t)
    · rw [image_eq_zero_of_notMem_tsupport ht, mul_zero, mul_zero]
  calc ‖∫ t : ↥H, (f ((t : G𝔼) * x) * (β t : ℂ) - g ((t : G𝔼) * x) * (β t : ℂ)) ∂τ‖
      ≤ ∫ t : ↥H, ε' * β t ∂τ := norm_integral_le_of_norm_le ((hβc.integrable_of_hasCompactSupport hβsupp).const_mul ε')
          (Filter.Eventually.of_forall hpt)
    _ = ε' * ∫ t : ↥H, β t ∂τ := integral_const_mul _ _

theorem continuous_fibre_average (f : G𝔼 → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (β : ↥H → ℝ)
    (hβ0 : ∀ t, 0 ≤ β t) (hβc : Continuous β) (hβsupp : HasCompactSupport β) :
    Continuous fun x : G𝔼 => ∫ t : ↥H, f ((t : G𝔼) * x) * (β t : ℂ) ∂τ := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := secondCountableTopology_tensor ℝ ℂ ℝ
  haveI := secondCountableTopology_GL 𝔼
  refine MeasureTheory.continuous_of_dominated (F := fun (x : G𝔼) (t : ↥H) => f ((t : G𝔼) * x) * (β t : ℂ))
    (bound := fun t : ↥H => C * β t) (fun x => ?_) (fun x => Filter.Eventually.of_forall fun t => ?_) ?_
    (Filter.Eventually.of_forall fun t => ?_)
  · exact (continuous_fibre f hf β hβc x).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ0 t)]
    exact mul_le_mul_of_nonneg_right (hC _) (hβ0 t)
  · exact (hβc.integrable_of_hasCompactSupport hβsupp).const_mul C
  · exact continuous_translate hf (t : G𝔼) (β t : ℂ)

end Fibre

variable (c : ℝˣ) (hc : (c : ℝ) < 0) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
  (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
  (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
  (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
  (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))

local notation "T" => (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
local notation "S" => (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))

set_option maxHeartbeats 3200000 in
include hc hδ hτ' in

theorem isMulRightInvariant_tau : (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ; τ'.IsMulRightInvariant) := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := t2Space_tensor ℝ ℂ ℝ
  haveI := locallyCompactSpace_tensor ℝ ℂ ℝ
  haveI := secondCountableTopology_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := t2Space_GL 𝔼
  haveI := secondCountableTopology_GL 𝔼
  haveI := locallyCompactSpace_GL 𝔼
  letI : MeasurableSpace G𝔼 := glBorelOf 𝔼
  haveI : BorelSpace G𝔼 := borelSpace_glBorelOf 𝔼
  letI : MeasurableSpace T := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace T := ⟨rfl⟩
  have hTc : IsClosed (T : Set G𝔼) := isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ
  have hTemb : Topology.IsClosedEmbedding ((↑) : T → G𝔼) := hTc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace T := hTemb.locallyCompactSpace
  haveI : SecondCountableTopology T := hTemb.isInducing.secondCountableTopology
  have hscalT : ∀ e : ℝˣ, scalarE e ∈ T := fun e => scalarE_mem_twistedCentralizer e δ
  haveI : Measure.IsHaarMeasure τ' := hτ'
  obtain ⟨Ca, hCa, hCaT, hcov⟩ :=
    AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg c hc δ y hδ
  have hcov' : ∀ t ∈ T, ∃ z ∈ Set.range scalarE, ∃ k ∈ Ca, t = z * k := fun t ht => by
    obtain ⟨e, k, hk, hgk⟩ := hcov t ht
    exact ⟨scalarE e, ⟨e, rfl⟩, k, hk, hgk⟩
  have hZT : Set.range scalarE ⊆ T := by
    rintro _ ⟨e, rfl⟩
    exact hscalT e
  have hZTc : ∀ z ∈ {z : T | (z : G𝔼) ∈ Set.range scalarE}, ∀ g : T, g * z = z * g := by
    rintro z ⟨e, he⟩ g
    exact comm_of_coe_central _ z g fun x => by rw [← he]; exact mul_scalarE_comm e x
  have hCT : IsCompact {k : T | (k : G𝔼) ∈ Ca} := hTemb.isCompact_preimage hCa
  exact MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact _ _ hZTc hCT
    (exists_mul_of_cover _ _ Ca hZT hcov') τ'

set_option maxHeartbeats 3200000 in
include hc hδ in

theorem isMulRightInvariant_sub
    (ν : @Measure ↥(Subgroup.subgroupOf S T) (borel _)) (hν : @Measure.IsHaarMeasure _ _ _ (borel _) ν) :
    (letI : MeasurableSpace ↥(Subgroup.subgroupOf S T) := borel _; ν.IsMulRightInvariant) := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := t2Space_tensor ℝ ℂ ℝ
  haveI := locallyCompactSpace_tensor ℝ ℂ ℝ
  haveI := secondCountableTopology_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := t2Space_GL 𝔼
  haveI := secondCountableTopology_GL 𝔼
  haveI := locallyCompactSpace_GL 𝔼
  letI : MeasurableSpace G𝔼 := glBorelOf 𝔼
  haveI : BorelSpace G𝔼 := borelSpace_glBorelOf 𝔼
  letI : MeasurableSpace T := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace T := ⟨rfl⟩
  letI : MeasurableSpace ↥S := borel _
  haveI : BorelSpace ↥S := ⟨rfl⟩
  have hTc : IsClosed (T : Set G𝔼) := isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ
  have hSc : IsClosed ((S : Subgroup G𝔼) : Set G𝔼) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ).inter (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))
  have hTemb : Topology.IsClosedEmbedding ((↑) : T → G𝔼) := hTc.isClosedEmbedding_subtypeVal
  have hSemb : Topology.IsClosedEmbedding ((↑) : ↥S → G𝔼) := hSc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace T := hTemb.locallyCompactSpace
  haveI : SecondCountableTopology T := hTemb.isInducing.secondCountableTopology
  haveI : LocallyCompactSpace ↥S := hSemb.locallyCompactSpace
  haveI : SecondCountableTopology ↥S := hSemb.isInducing.secondCountableTopology
  have hscalS : ∀ e : ℝˣ, scalarE e ∈ S := fun e =>
    ⟨scalarE_mem_twistedCentralizer e δ, scalarE_mem_twistedCentralizer e (u₀ * δ)⟩
  have hS'c : IsClosed ((Subgroup.subgroupOf S T : Subgroup T) : Set T) := by
    have h : ((Subgroup.subgroupOf S T : Subgroup T) : Set T) = ((↑) : T → G𝔼) ⁻¹' (S : Set G𝔼) := rfl
    rw [h]
    exact hSc.preimage continuous_subtype_val
  letI : MeasurableSpace ↥(Subgroup.subgroupOf S T) := borel _
  haveI : BorelSpace ↥(Subgroup.subgroupOf S T) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure ν := hν
  have hS'emb : Topology.IsClosedEmbedding ((↑) : ↥(Subgroup.subgroupOf S T) → T) := hS'c.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace ↥(Subgroup.subgroupOf S T) := hS'emb.locallyCompactSpace
  haveI : SecondCountableTopology ↥(Subgroup.subgroupOf S T) := hS'emb.isInducing.secondCountableTopology
  obtain ⟨Ca, hCa, hCaT, hcov⟩ :=
    AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg c hc δ y hδ
  have hcov' : ∀ t ∈ T, ∃ z ∈ Set.range scalarE, ∃ k ∈ Ca, t = z * k := fun t ht => by
    obtain ⟨e, k, hk, hgk⟩ := hcov t ht
    exact ⟨scalarE e, ⟨e, rfl⟩, k, hk, hgk⟩
  have hZS : Set.range scalarE ⊆ S := by
    rintro _ ⟨e, rfl⟩
    exact hscalS e
  have hZSc : ∀ z ∈ {z : ↥(Subgroup.subgroupOf S T) | ((z : T) : G𝔼) ∈ Set.range scalarE},
      ∀ g : ↥(Subgroup.subgroupOf S T), g * z = z * g := by
    rintro z ⟨e, he⟩ g
    exact comm_of_coe_coe_central _ _ z g fun x => by rw [← he]; exact mul_scalarE_comm e x
  have hCS : IsCompact {k : ↥(Subgroup.subgroupOf S T) | ((k : T) : G𝔼) ∈ Ca} := (hTemb.comp hS'emb).isCompact_preimage hCa
  exact MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact _ _ hZSc hCS
    (exists_mul_of_cover_subgroupOf _ _ inf_le_left _ Ca hZS hcov') ν

set_option maxHeartbeats 3200000 in
include hc hδ in

theorem isMulRightInvariant_S (ν : @Measure ↥S (borel _)) (hν : @Measure.IsHaarMeasure _ _ _ (borel _) ν) :
    (letI : MeasurableSpace ↥S := borel _; ν.IsMulRightInvariant) := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := t2Space_tensor ℝ ℂ ℝ
  haveI := locallyCompactSpace_tensor ℝ ℂ ℝ
  haveI := secondCountableTopology_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := t2Space_GL 𝔼
  haveI := secondCountableTopology_GL 𝔼
  haveI := locallyCompactSpace_GL 𝔼
  letI : MeasurableSpace G𝔼 := glBorelOf 𝔼
  haveI : BorelSpace G𝔼 := borelSpace_glBorelOf 𝔼
  letI : MeasurableSpace ↥S := borel _
  haveI : BorelSpace ↥S := ⟨rfl⟩
  have hSc : IsClosed ((S : Subgroup G𝔼) : Set G𝔼) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ).inter (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))
  have hSemb : Topology.IsClosedEmbedding ((↑) : ↥S → G𝔼) := hSc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace ↥S := hSemb.locallyCompactSpace
  haveI : SecondCountableTopology ↥S := hSemb.isInducing.secondCountableTopology
  haveI : Measure.IsHaarMeasure ν := hν
  have hscalS : ∀ e : ℝˣ, scalarE e ∈ S := fun e =>
    ⟨scalarE_mem_twistedCentralizer e δ, scalarE_mem_twistedCentralizer e (u₀ * δ)⟩
  obtain ⟨Ca, hCa, hCaT, hcov⟩ :=
    AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg c hc δ y hδ
  have hcovS : ∀ t ∈ S, ∃ z ∈ Set.range scalarE, ∃ k ∈ Ca, t = z * k := fun t ht => by
    obtain ⟨e, k, hk, hgk⟩ := hcov t ht.1
    exact ⟨scalarE e, ⟨e, rfl⟩, k, hk, hgk⟩
  have hZS : Set.range scalarE ⊆ S := by
    rintro _ ⟨e, rfl⟩
    exact hscalS e
  have hZSc : ∀ z ∈ {z : ↥S | (z : G𝔼) ∈ Set.range scalarE}, ∀ g : ↥S, g * z = z * g := by
    rintro z ⟨e, he⟩ g
    exact comm_of_coe_central _ z g fun x => by rw [← he]; exact mul_scalarE_comm e x
  have hCS : IsCompact {k : ↥S | (k : G𝔼) ∈ Ca} := hSemb.isCompact_preimage hCa
  exact MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact _ _ hZSc hCS
    (exists_mul_of_cover _ _ Ca hZS hcovS) ν

variable (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
  (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)

set_option maxHeartbeats 3200000 in
include hc hδ hτ' hτS in

theorem weil : ∃ κ : ℝ, 0 < κ ∧
    (∃ β : T → ℝ, (∀ t, 0 ≤ β t) ∧ Continuous β ∧ HasCompactSupport β ∧
      ∀ t : T, (letI : MeasurableSpace ↥S := borel _
        ∫ s : ↥S, β ((⟨(s : G𝔼), (inf_le_left : S ≤ T) s.2⟩ : T) * t) ∂τS) = 1) ∧
    ∀ w : T → ℝ, (∀ t, 0 ≤ w t) → (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ; Measurable w) →
      HasCompactSupport w →
      (∀ t : T, (letI : MeasurableSpace ↥S := borel _
        ∫ s : ↥S, w ((⟨(s : G𝔼), (inf_le_left : S ≤ T) s.2⟩ : T) * t) ∂τS) = 1) →
      (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ; ∫ t, w t ∂τ') = κ := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := t2Space_tensor ℝ ℂ ℝ
  haveI := locallyCompactSpace_tensor ℝ ℂ ℝ
  haveI := secondCountableTopology_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := t2Space_GL 𝔼
  haveI := secondCountableTopology_GL 𝔼
  haveI := locallyCompactSpace_GL 𝔼
  letI : MeasurableSpace G𝔼 := glBorelOf 𝔼
  haveI : BorelSpace G𝔼 := borelSpace_glBorelOf 𝔼
  letI : MeasurableSpace T := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace T := ⟨rfl⟩
  letI : MeasurableSpace ↥S := borel _
  haveI : BorelSpace ↥S := ⟨rfl⟩
  have hTc : IsClosed (T : Set G𝔼) := isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ
  have hSc : IsClosed ((S : Subgroup G𝔼) : Set G𝔼) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ).inter (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))
  have hTemb : Topology.IsClosedEmbedding ((↑) : T → G𝔼) := hTc.isClosedEmbedding_subtypeVal
  have hSemb : Topology.IsClosedEmbedding ((↑) : ↥S → G𝔼) := hSc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace T := hTemb.locallyCompactSpace
  haveI : SecondCountableTopology T := hTemb.isInducing.secondCountableTopology
  haveI : LocallyCompactSpace ↥S := hSemb.locallyCompactSpace
  haveI : SecondCountableTopology ↥S := hSemb.isInducing.secondCountableTopology
  have hscalS : ∀ e : ℝˣ, scalarE e ∈ S := fun e =>
    ⟨scalarE_mem_twistedCentralizer e δ, scalarE_mem_twistedCentralizer e (u₀ * δ)⟩
  haveI : Measure.IsHaarMeasure τ' := hτ'
  haveI : Measure.IsHaarMeasure τS := hτS
  haveI : τ'.IsMulRightInvariant := isMulRightInvariant_tau c hc δ y hδ τ' hτ'
  haveI : τ'.IsInvInvariant := MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant τ'

  have hS'c : IsClosed ((Subgroup.subgroupOf S T : Subgroup T) : Set T) := by
    have h : ((Subgroup.subgroupOf S T : Subgroup T) : Set T) = ((↑) : T → G𝔼) ⁻¹' (S : Set G𝔼) := rfl
    rw [h]
    exact hSc.preimage continuous_subtype_val
  letI : MeasurableSpace ↥(Subgroup.subgroupOf S T) := borel _
  haveI : BorelSpace ↥(Subgroup.subgroupOf S T) := ⟨rfl⟩
  have hS'emb : Topology.IsClosedEmbedding ((↑) : ↥(Subgroup.subgroupOf S T) → T) := hS'c.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace ↥(Subgroup.subgroupOf S T) := hS'emb.locallyCompactSpace
  haveI : SecondCountableTopology ↥(Subgroup.subgroupOf S T) := hS'emb.isInducing.secondCountableTopology
  let eS : ↥(Subgroup.subgroupOf S T) ≃* ↥S := Subgroup.subgroupOfEquivOfLe (inf_le_left : S ≤ T)
  have heSc : Continuous eS :=
    continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_subtype_val).congr fun x => rfl)
  have heSc' : Continuous eS.symm :=
    continuous_induced_rng.2 (continuous_induced_rng.2 continuous_subtype_val)
  let eH : ↥S ≃ₜ ↥(Subgroup.subgroupOf S T) :=
    { toEquiv := eS.symm.toEquiv, continuous_toFun := heSc', continuous_invFun := heSc }
  let τd : Measure ↥(Subgroup.subgroupOf S T) := Measure.map eS.symm τS
  haveI hτd : Measure.IsHaarMeasure τd := eS.symm.isHaarMeasure_map τS heSc' heSc
  haveI : τd.IsMulRightInvariant := isMulRightInvariant_sub c hc δ y hδ u₀ τd hτd
  haveI : τd.IsInvInvariant := MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant τd

  obtain ⟨Ca, hCa, hCaT, hcov⟩ :=
    AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg c hc δ y hδ
  have hCT : IsCompact {k : T | (k : G𝔼) ∈ Ca} := hTemb.isCompact_preimage hCa
  have hcov' : ∀ t ∈ T, ∃ z ∈ Set.range scalarE, ∃ k ∈ Ca, t = z * k := fun t ht => by
    obtain ⟨e, k, hk, hgk⟩ := hcov t ht
    exact ⟨scalarE e, ⟨e, rfl⟩, k, hk, hgk⟩
  have hZS : Set.range scalarE ⊆ S := by
    rintro _ ⟨e, rfl⟩
    exact hscalS e
  obtain ⟨κ, hκ, ⟨β, hβ0, hβc, hβsupp, hβ1⟩, hweil⟩ :=
    MeasureTheory.exists_pos_forall_integral_eq_of_forall_integral_subgroup_translate_eq_one_of_isCompact
      (Subgroup.subgroupOf S T) hS'c τ' τd _ hCT (exists_subgroupOf_mul_of_cover _ _ inf_le_left _ Ca hZS hcov')

  have etr : ∀ (f : T → ℝ) (t : T), ∫ s' : ↥(Subgroup.subgroupOf S T), f ((s' : T) * t) ∂τd =
      ∫ s : ↥S, f ((⟨(s : G𝔼), (inf_le_left : S ≤ T) s.2⟩ : T) * t) ∂τS := by
    intro f t
    have h' := integral_map_equiv (μ := τS) eH.toMeasurableEquiv (fun s' : ↥(Subgroup.subgroupOf S T) => f ((s' : T) * t))
    simp only [Homeomorph.toMeasurableEquiv_coe] at h'
    exact h'
  refine ⟨κ, hκ, ⟨β, hβ0, hβc, hβsupp, fun t => ?_⟩, fun w hw0 hwm hwsupp hcl => ?_⟩
  · rw [← etr, hβ1]
  · exact hweil w hw0 hwm hwsupp fun t => by rw [etr]; exact hcl t

set_option maxHeartbeats 6400000 in
include hc hδ hτ' hτS in
theorem main (μL : @Measure G𝔼 (glBorelOf 𝔼)) (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf 𝔼) μL) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ w : ↥T → ℝ,
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         letI : MeasurableSpace ↥S := borel _
         (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
           ∀ t : ↥T, ∫ s : ↥S, w ((⟨(s : G𝔼), (Subgroup.mem_inf.mp s.2).1⟩ : ↥T) * t) ∂τS = 1) →
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∫ t, w t ∂τ' = κ)) ∧
      ∀ (φ : GL (Fin 2) ℂ → ℂ),
        ((∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
          ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ) →
      ∀ (θ₀ : ℝ), 0 < θ₀ →
      ∀ (u : ℝ → G𝔼),
        (∀ θ : ℝ, u θ ∈ S) →
        (letI := glBorelOf 𝔼
         Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) →
        (∀ θ ∈ Set.Ioo 0 θ₀, IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ))) →
      ∀ (τu : ∀ θ : ℝ, @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ))
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))),
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (τu θ)) →
        (∀ θ ∈ Set.Ioo 0 θ₀,
          (letI := glBorelOf 𝔼
           letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
           letI : MeasurableSpace ↥S := borel _
           Measure.map Subtype.val (τu θ) = Measure.map Subtype.val τS)) →
      ∀ (Ψ : ℝ → ℂ),
        (∀ θ ∈ Set.Ioo 0 θ₀,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL (u θ * δ) (τu θ) (fun z => φ (strGL z)) (Ψ θ)) →
      ∀ I' : ℂ,
        IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ' (fun z => φ (strGL z)) I' →
        Filter.Tendsto Ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds ((κ : ℂ) * I')) := by
  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := t2Space_tensor ℝ ℂ ℝ
  haveI := locallyCompactSpace_tensor ℝ ℂ ℝ
  haveI := secondCountableTopology_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := t2Space_GL 𝔼
  haveI := secondCountableTopology_GL 𝔼
  haveI := locallyCompactSpace_GL 𝔼
  letI : MeasurableSpace G𝔼 := glBorelOf 𝔼
  haveI : BorelSpace G𝔼 := borelSpace_glBorelOf 𝔼
  letI : MeasurableSpace T := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace T := ⟨rfl⟩
  letI : MeasurableSpace ↥S := borel _
  haveI : BorelSpace ↥S := ⟨rfl⟩
  have hTc : IsClosed (T : Set G𝔼) := isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ
  have hSc : IsClosed ((S : Subgroup G𝔼) : Set G𝔼) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ).inter (isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))
  have hTemb : Topology.IsClosedEmbedding ((↑) : T → G𝔼) := hTc.isClosedEmbedding_subtypeVal
  have hSemb : Topology.IsClosedEmbedding ((↑) : ↥S → G𝔼) := hSc.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace T := hTemb.locallyCompactSpace
  haveI : SecondCountableTopology T := hTemb.isInducing.secondCountableTopology
  haveI : LocallyCompactSpace ↥S := hSemb.locallyCompactSpace
  haveI : SecondCountableTopology ↥S := hSemb.isInducing.secondCountableTopology
  haveI : Measure.IsHaarMeasure μL := hμL
  haveI : Measure.IsHaarMeasure τ' := hτ'
  haveI : Measure.IsHaarMeasure τS := hτS
  haveI : τ'.IsMulRightInvariant := isMulRightInvariant_tau c hc δ y hδ τ' hτ'
  haveI : τ'.IsInvInvariant := MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant τ'
  haveI : τS.IsMulRightInvariant := isMulRightInvariant_S c hc δ y hδ u₀ τS hτS
  haveI : τS.IsInvInvariant := MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant τS
  have hτ'c : IsFiniteMeasureOnCompacts τ' := hτ'.toIsFiniteMeasureOnCompacts
  have hTb : BorelSpace T := ⟨rfl⟩
  obtain ⟨κ, hκ, ⟨β, hβ0, hβc, hβsupp, hβ1⟩, hweil⟩ := weil c hc δ y hδ τ' hτ' u₀ τS hτS
  refine ⟨κ, hκ, fun w hw => hweil w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2, ?_⟩
  intro φ hφ θ₀ hθ₀ u huS hu1 hreg τu hτu hmap Ψ hΨ I' hI'

  obtain ⟨hφtc, hφts⟩ := continuous_and_hasCompactSupport_comp_strGL φ hφ
  obtain ⟨Cφ, hCφ⟩ : ∃ C : ℝ, ∀ g, ‖(fun z : G𝔼 => φ (strGL z)) g‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hφtc.norm).bddAbove_range_of_hasCompactSupport hφts.norm
    exact ⟨C, fun g => hC (Set.mem_range_self g)⟩
  have hFc : ∀ v, Continuous (twI (fun z : G𝔼 => φ (strGL z)) δ v) := fun v => continuous_twI _ hφtc δ v
  have hF1T : ∀ (t : T) (x : G𝔼), twI (fun z : G𝔼 => φ (strGL z)) δ 1 ((t : G𝔼) * x) = twI (fun z : G𝔼 => φ (strGL z)) δ 1 x :=
    fun t x => twI_mul_left _ δ 1 t (by rw [one_mul]; exact t.2) x

  obtain ⟨U₁, hU₁, Ω, hΩ, hunif⟩ :=
    AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg c hc δ y hδ
      (tsupport (fun z : G𝔼 => φ (strGL z))) hφts
  have hsuppF : ∀ v ∈ U₁, v ∈ T → ∀ x, twI (fun z : G𝔼 => φ (strGL z)) δ v x ≠ 0 →
      ∃ t : T, ∃ k ∈ Ω, x = (t : G𝔼) * k := by
    intro v hv hvT x hx
    have hmem : x⁻¹ * (v * δ) * σ' x ∈ tsupport (fun z : G𝔼 => φ (strGL z)) := subset_tsupport _ hx
    obtain ⟨t, ht, d, hd, hx'⟩ := hunif v hv hvT x hmem
    exact ⟨⟨t, ht⟩, d, hd, hx'⟩
  obtain ⟨W, hW0, hWm, hWc, ⟨BW, hBW⟩, hW1⟩ :=
    MeasureTheory.exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact T hTc τ' Ω hΩ
  have hWb : ∃ B : ℝ, ∀ x, |W x| ≤ B := ⟨BW, fun x => by rw [abs_of_nonneg (hW0 x)]; exact hBW x⟩
  set F : G𝔼 → G𝔼 → ℂ := twI (fun z : G𝔼 => φ (strGL z)) δ with hF
  have hFm : ∀ v, Measurable (F v) := fun v => (hFc v).measurable
  have hFb : ∀ v x, ‖F v x‖ ≤ Cφ := fun v x => hCφ _
  have hβm : Measurable β := hβc.measurable
  have h1U : (1 : G𝔼) ∈ U₁ := mem_of_mem_nhds hU₁

  have hβκ : ∫ t, β t ∂τ' = κ := hweil β hβ0 hβm hβsupp hβ1

  have hA1 : ∀ x : G𝔼, ∫ t : T, F 1 ((t : G𝔼) * x) * (β t : ℂ) ∂τ' = (κ : ℂ) * F 1 x := by
    intro x
    rw [fibre_average_of_invariant (hHb := hTb) (hτc := hτ'c) τ' (F 1) β x (fun t => hF1T t x), hβκ, mul_comm]

  have hId : ∀ θ ∈ Set.Ioo 0 θ₀, u θ ∈ U₁ →
      Ψ θ = ∫ x, (∫ t : T, F (u θ) ((t : G𝔼) * x) * (β t : ℂ) ∂τ') * (W x : ℂ) ∂μL := by
    intro θ hθ hθU
    letI : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ)) :=
      twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
    haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ)) := ⟨rfl⟩
    haveI : Measure.IsHaarMeasure (τu θ) := hτu θ hθ
    obtain ⟨wθ, ⟨hw0, hwm, hwsupp, hwcl⟩, hΨeq⟩ := hΨ θ hθ
    have hTuc : IsClosed ((twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ) : Subgroup G𝔼) : Set G𝔼) :=
      isClosed_twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ)
    have hTuemb : Topology.IsClosedEmbedding ((↑) : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ)) → G𝔼) :=
      hTuc.isClosedEmbedding_subtypeVal

    have hSsub : ∀ s : ↥S, (s : G𝔼) ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ) := by
      intro s
      by_contra hs
      have hO : IsOpen (((↑) : ↥S → G𝔼) ⁻¹' ((twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ) : Subgroup G𝔼) : Set G𝔼)ᶜ) :=
        hTuc.isOpen_compl.preimage continuous_subtype_val
      have hpos := hO.measure_pos τS ⟨s, hs⟩
      have hmeasC : MeasurableSet (((twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ) : Subgroup G𝔼) : Set G𝔼)ᶜ) :=
        hTuc.measurableSet.compl
      have h1 := Measure.map_apply (μ := τS) (continuous_subtype_val.measurable) hmeasC
      have h2 := Measure.map_apply (μ := τu θ) (continuous_subtype_val.measurable) hmeasC
      have h3 : ((↑) : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ)) → G𝔼) ⁻¹'
          (((twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ) : Subgroup G𝔼) : Set G𝔼)ᶜ) = ∅ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_not]
        exact t.2
      rw [← hmap θ hθ, h2, h3, measure_empty] at h1
      exact absurd h1 hpos.ne
    have hFS : ∀ (s : ↥S) (x : G𝔼), F (u θ) ((s : G𝔼) * x) = F (u θ) x := fun s x =>
      twI_mul_left _ δ (u θ) s (hSsub s) x
    have hwS1 : ∀ x : G𝔼, F (u θ) x ≠ 0 → ∫ s : ↥S, wθ ((s : G𝔼) * x) ∂τS = 1 := by
      intro x hx
      have h1 := hwcl x hx
      have e1 : ∫ t' : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ)), wθ ((t' : G𝔼) * x) ∂(τu θ) =
          ∫ g, wθ (g * x) ∂(Measure.map Subtype.val (τu θ)) :=
        (hTuemb.measurableEmbedding.integral_map (μ := τu θ) (fun g : G𝔼 => wθ (g * x))).symm
      have e2 : ∫ s : ↥S, wθ ((s : G𝔼) * x) ∂τS = ∫ g, wθ (g * x) ∂(Measure.map Subtype.val τS) :=
        (hSemb.measurableEmbedding.integral_map (μ := τS) (fun g : G𝔼 => wθ (g * x))).symm
      rw [e2, ← hmap θ hθ, ← e1, h1]
    have hW1' : ∀ x : G𝔼, F (u θ) x ≠ 0 → ∫ t : T, W ((t : G𝔼) * x) ∂τ' = 1 := fun x hx =>
      hW1 x (hsuppF (u θ) hθU (huS θ).1 x hx)
    have key := MeasureTheory.integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one
      T hTc S hSc inf_le_left μL τ' τS (F (u θ)) (hFm _) ⟨Cφ, hFb _⟩ hFS wθ hw0 hwm hwsupp hwS1
      β hβ0 hβm hβsupp hβ1 W hW0 hWm hWc hW1'
    rw [hΨeq]
    exact key

  have hI : I' = ∫ x, F 1 x * (W x : ℂ) ∂μL := by
    obtain ⟨wI, hwI, hIeq⟩ := hI'
    have hwI' : (∀ x, 0 ≤ wI x) ∧ Measurable wI ∧ HasCompactSupport wI ∧
        ∀ x, F 1 x ≠ 0 → ∫ t : T, wI ((t : G𝔼) * x) ∂τ' = 1 := by
      refine ⟨hwI.1, hwI.2.1, hwI.2.2.1, fun x hx => hwI.2.2.2 x ?_⟩
      rwa [hF, twI_one] at hx
    have hW' : (∀ x, 0 ≤ W x) ∧ Measurable W ∧ HasCompactSupport W ∧
        ∀ x, F 1 x ≠ 0 → ∫ t : T, W ((t : G𝔼) * x) ∂τ' = 1 :=
      ⟨hW0, hWm, hWc, fun x hx => hW1 x (hsuppF 1 h1U (Subgroup.one_mem _) x hx)⟩
    rw [hIeq]
    have e : (fun x : G𝔼 => (fun z : G𝔼 => φ (strGL z)) (x⁻¹ * δ * σ' x) * (wI x : ℂ)) = fun x => F 1 x * (wI x : ℂ) := by
      funext x; rw [hF, twI_one]
    rw [e]
    exact MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one T hTc μL τ' (F 1) (hFm 1)
      ⟨Cφ, hFb 1⟩ hF1T wI W hwI' hW'

  have hK : IsCompact ((fun p : T × G𝔼 => (p.1 : G𝔼) * p.2) '' ((tsupport β) ×ˢ (tsupport W))) :=
    (hβsupp.prod hWc).image (by fun_prop)
  set K : Set G𝔼 := (fun p : T × G𝔼 => (p.1 : G𝔼) * p.2) '' ((tsupport β) ×ˢ (tsupport W)) with hKdef
  have hTU : TendstoUniformly (fun (v : G𝔼) (k : ↥K) => F v (k : G𝔼)) (fun k : ↥K => F 1 (k : G𝔼)) (𝓝 (1 : G𝔼)) := by
    haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
    letI : UniformSpace G𝔼 := IsTopologicalGroup.rightUniformSpace G𝔼
    have h2 : Continuous fun p : G𝔼 × ↥K => F p.1 (p.2 : G𝔼) := continuous_twI_restrict _ hφtc δ K
    exact ContinuousOn.tendstoUniformly (U := Set.univ) Filter.univ_mem h2.continuousOn
  have hunifA : TendstoUniformlyOn (fun θ (x : G𝔼) => ∫ t : T, F (u θ) ((t : G𝔼) * x) * (β t : ℂ) ∂τ')
      (fun x => (κ : ℂ) * F 1 x) (nhdsWithin 0 (Set.Ioi 0)) (tsupport W) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set ε' : ℝ := ε / (κ + 1) with hε'
    have hε'pos : 0 < ε' := div_pos hε (by linarith)
    have hε'lt : ε' * κ < ε := by
      rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    have hv := hu1.eventually (Metric.tendstoUniformly_iff.mp hTU ε' hε'pos)
    filter_upwards [hv] with θ hθv x hx
    rw [← hA1 x, dist_eq_norm]
    have hclose : ∀ t : T, t ∈ tsupport β → ‖F 1 ((t : G𝔼) * x) - F (u θ) ((t : G𝔼) * x)‖ ≤ ε' := by
      intro t ht
      have hk : (t : G𝔼) * x ∈ K := ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      have := hθv ⟨(t : G𝔼) * x, hk⟩
      rw [dist_eq_norm] at this
      exact this.le
    calc ‖(∫ t : T, F 1 ((t : G𝔼) * x) * (β t : ℂ) ∂τ') - ∫ t : T, F (u θ) ((t : G𝔼) * x) * (β t : ℂ) ∂τ'‖
        ≤ ε' * ∫ t : T, β t ∂τ' :=
          norm_fibre_average_sub_le (hHb := hTb) (hτc := hτ'c) τ' (F 1) (F (u θ)) (hFc 1) (hFc (u θ)) β hβ0 hβc hβsupp x ε' hclose
      _ = ε' * κ := by rw [hβκ]
      _ < ε := hε'lt

  have hΦm : ∀ θ : ℝ, AEStronglyMeasurable (fun x : G𝔼 => ∫ t : T, F (u θ) ((t : G𝔼) * x) * (β t : ℂ) ∂τ') μL :=
    fun θ => (continuous_fibre_average (hHb := hTb) (hτc := hτ'c) τ' (F (u θ)) (hFc (u θ)) Cφ (hFb (u θ)) β hβ0 hβc hβsupp).aestronglyMeasurable
  have hΦ₀m : AEStronglyMeasurable (fun x : G𝔼 => (κ : ℂ) * F 1 x) μL :=
    (continuous_const.mul (hFc 1)).aestronglyMeasurable
  have hΦ₀b : ∃ B₀ : ℝ, ∀ x ∈ tsupport W, ‖(κ : ℂ) * F 1 x‖ ≤ B₀ :=
    ⟨κ * Cφ, fun x _ => by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]; exact mul_le_mul_of_nonneg_left (hFb 1 x) hκ.le⟩

  have hlim := MeasureTheory.tendsto_integral_mul_nhdsGT_of_tendstoUniformlyOn_tsupport μL W hWm hWc hWb
    (fun θ (x : G𝔼) => ∫ t : T, F (u θ) ((t : G𝔼) * x) * (β t : ℂ) ∂τ') (fun x => (κ : ℂ) * F 1 x) hΦm hΦ₀m hΦ₀b hunifA
  have hval : ∫ x, (κ : ℂ) * F 1 x * (W x : ℂ) ∂μL = (κ : ℂ) * I' := by
    rw [hI, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hval] at hlim
  have hev : ∀ᶠ θ in nhdsWithin 0 (Set.Ioi 0),
      (∫ x, (∫ t : T, F (u θ) ((t : G𝔼) * x) * (β t : ℂ) ∂τ') * (W x : ℂ) ∂μL) = Ψ θ := by
    filter_upwards [Ioo_mem_nhdsGT hθ₀, hu1.eventually_mem hU₁] with θ hθ hθU
    exact (hId θ hθ hθU).symm
  exact hlim.congr' hev

end Assembly

end TwLimH
end AutomorphicForm

end

open MeasureTheory _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer.AutomorphicForm in
theorem solution
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ w : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → ℝ,
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
             twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
         (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
           ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ),
             ∫ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
               w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ :
                 ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∂τS = 1) →
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∫ t, w t ∂τ' = κ)) ∧
      ∀ (φ : GL (Fin 2) ℂ → ℂ),
        ((∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
          ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ) →
      ∀ (θ₀ : ℝ), 0 < θ₀ →
      ∀ (u : ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
        (∀ θ : ℝ, u θ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) →
        (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
         Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) →
        (∀ θ ∈ Set.Ioo 0 θ₀, IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ))) →
      ∀ (τu : ∀ θ : ℝ, @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ))
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))),
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (τu θ)) →
        (∀ θ ∈ Set.Ioo 0 θ₀,
          (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
           letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
           letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
               twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
           Measure.map Subtype.val (τu θ) = Measure.map Subtype.val τS)) →
      ∀ (Ψ : ℝ → ℂ),
        (∀ θ ∈ Set.Ioo 0 θ₀,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL (u θ * δ) (τu θ)
            (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) (Ψ θ)) →
      ∀ I' : ℂ,
        IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
        Filter.Tendsto Ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds ((κ : ℂ) * I')) :=
  AutomorphicForm.TwLimH.main c hc δ y hδ τ' hτ' u₀ τS hτS μL hμL

end S_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer (solution)
