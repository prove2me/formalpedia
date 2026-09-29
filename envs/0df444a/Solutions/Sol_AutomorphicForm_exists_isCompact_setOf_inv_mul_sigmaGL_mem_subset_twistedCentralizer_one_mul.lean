-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2505d3d7-ce85-5dde-b460-0580c9898ed2

import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField
open scoped TensorProduct TensorProduct.RightActions Pointwise

namespace P2mAdelicH90Proper

theorem continuous_generalLinearGroup_map {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Continuous.matrix_map Units.continuous_val hf
  · exact Continuous.matrix_map Units.continuous_coe_inv hf

section Scalars

variable (K : Type) [Field K] [NumberField K]

theorem centralScalar_eq :
    AutomorphicForm.centralScalar (𝓞 K) K = Matrix.GeneralLinearGroup.scalar (Fin 2) := rfl

theorem continuous_centralScalar : Continuous (AutomorphicForm.centralScalar (𝓞 K) K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_val).matrix_diagonal).congr fun u => ?_
    rfl
  · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_coe_inv).matrix_diagonal).congr
      fun u => ?_
    change (Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
      (((AutomorphicForm.centralScalar (𝓞 K) K u)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    rw [← map_inv]
    rfl

theorem isClosedEmbedding_centralScalar :
    Topology.IsClosedEmbedding (AutomorphicForm.centralScalar (𝓞 K) K) := by

  let p : AutomorphicForm.AdelicGL2 (𝓞 K) K → AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    fun g => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0,
      MulOpposite.op (((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0))
  have hp : Continuous p := by
    refine Continuous.prodMk ?_ ?_
    · exact Units.continuous_val.matrix_elem 0 0
    · exact MulOpposite.continuous_op.comp (Units.continuous_coe_inv.matrix_elem 0 0)
  have hcomp : p ∘ AutomorphicForm.centralScalar (𝓞 K) K =
      Units.embedProduct (AdeleRing (𝓞 K) K) := by
    funext u
    change ((((AutomorphicForm.centralScalar (𝓞 K) K u : AutomorphicForm.AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0,
      MulOpposite.op (((((AutomorphicForm.centralScalar (𝓞 K) K u)⁻¹ :
        AutomorphicForm.AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0)) =
      ((u : AdeleRing (𝓞 K) K), MulOpposite.op (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K))
    rw [← map_inv]
    rfl
  have hind : Topology.IsInducing (AutomorphicForm.centralScalar (𝓞 K) K) := by
    refine Topology.IsInducing.of_comp (continuous_centralScalar K) hp ?_
    rw [hcomp]
    exact Units.isInducing_embedProduct
  have hinj : Function.Injective (AutomorphicForm.centralScalar (𝓞 K) K) := by
    intro a b h
    have := congrArg (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0) h
    refine Units.ext ?_
    simpa [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
  refine ⟨⟨hind, hinj⟩, ?_⟩

  have hrange : Set.range (AutomorphicForm.centralScalar (𝓞 K) K) =
      {g : AutomorphicForm.AdelicGL2 (𝓞 K) K |
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 =
          (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1} := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · rintro ⟨h01, h10, h00⟩
      set a : AdeleRing (𝓞 K) K := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 with ha
      have hg : (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = Matrix.diagonal fun _ => a := by
        ext i j
        fin_cases i <;> fin_cases j
        · simp [ha]
        · simpa using h01
        · simpa using h10
        · simp only [Matrix.diagonal_apply_eq]
          exact h00.symm.trans ha
      have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = a * a := by
        rw [hg, Matrix.det_diagonal, Fin.prod_univ_two]
      have ha : IsUnit a := by
        have hu : IsUnit (a * a) := hdet ▸ (Matrix.isUnits_det_units g)
        exact isUnit_of_mul_isUnit_left hu
      refine ⟨ha.unit, Units.ext ?_⟩
      rw [hg]
      ext i j
      simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply]
  rw [hrange]
  refine IsClosed.inter (isClosed_eq (Units.continuous_val.matrix_elem 0 1)
    continuous_const) (IsClosed.inter (isClosed_eq (Units.continuous_val.matrix_elem 1 0)
    continuous_const) (isClosed_eq (Units.continuous_val.matrix_elem 0 0)
    (Units.continuous_val.matrix_elem 1 1)))

theorem exists_eq_centralScalar_of_mem_center {z : AutomorphicForm.AdelicGL2 (𝓞 K) K}
    (hz : z ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 K) K)) :
    ∃ ζ : (AdeleRing (𝓞 K) K)ˣ, z = AutomorphicForm.centralScalar (𝓞 K) K ζ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨ζ, hζ⟩ := hz
  exact ⟨ζ, hζ.symm⟩

end Scalars

section AdeleSide

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem coe_unitsAct (τ : L ≃ₐ[K] L) (u : (AdeleRing (𝓞 L) L)ˣ) :
    ((D.unitsAct τ u : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) =
      (D.act τ) (u : AdeleRing (𝓞 L) L) := rfl

theorem sigmaAdelicAct_centralScalar (τ : L ≃ₐ[K] L) (u : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D τ (AutomorphicForm.centralScalar (𝓞 L) L u) =
      AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct τ u) := by
  ext i j
  change (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom
      (((AutomorphicForm.centralScalar (𝓞 L) L u : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) =
    ((AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct τ u) : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
  simp only [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply, coe_unitsAct]
  split_ifs
  · rfl
  · exact map_zero _

theorem continuous_sigmaAdelicAct : Continuous (AutomorphicForm.sigmaAdelicAct K L D σ) :=
  continuous_generalLinearGroup_map _ (D.continuous_act σ)

variable {K L σ D}

theorem centralScalar_prod_unitsAct_pow (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (ζ : (AdeleRing (𝓞 L) L)ˣ)
    (hz : g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g = AutomorphicForm.centralScalar (𝓞 L) L ζ)
    (m : ℕ) :
    AutomorphicForm.centralScalar (𝓞 L) L (∏ k ∈ Finset.range m, D.unitsAct (σ ^ k) ζ) =
      g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D (σ ^ m) g := by
  induction m with
  | zero =>
    rw [Finset.prod_range_zero, map_one, pow_zero, AutomorphicForm.sigmaAdelicAct_one,
      MonoidHom.id_apply, inv_mul_cancel]
  | succ m ih =>
    have hS : AutomorphicForm.sigmaAdelicAct K L D σ g =
        g * AutomorphicForm.centralScalar (𝓞 L) L ζ := by
      rw [← hz, mul_inv_cancel_left]
    rw [Finset.prod_range_succ, map_mul, ih, pow_succ, AutomorphicForm.sigmaAdelicAct_mul,
      MonoidHom.comp_apply, hS, map_mul, sigmaAdelicAct_centralScalar, mul_assoc]

theorem prod_unitsAct_pow_eq_one (g : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (ζ : (AdeleRing (𝓞 L) L)ˣ)
    (hz : g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g = AutomorphicForm.centralScalar (𝓞 L) L ζ) :
    ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) ζ = 1 := by
  have h := centralScalar_prod_unitsAct_pow g ζ hz (orderOf σ)
  rw [pow_orderOf_eq_one, AutomorphicForm.sigmaAdelicAct_one, MonoidHom.id_apply,
    inv_mul_cancel, ← (AutomorphicForm.centralScalar (𝓞 L) L).map_one] at h
  exact (isClosedEmbedding_centralScalar L).injective h

variable (K L σ D)

theorem exists_isCompact_forall_exists_fixed_mul
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C) :
    ∃ D' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L), IsCompact D' ∧
      ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        x⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ x ∈ C →
          ∃ F d : AutomorphicForm.AdelicGL2 (𝓞 L) L,
            AutomorphicForm.sigmaAdelicAct K L D σ F = F ∧ d ∈ D' ∧ x = F * d := by

  have hScont := continuous_sigmaAdelicAct K L σ D
  have hcs := isClosedEmbedding_centralScalar L

  obtain ⟨C', hC', hmod⟩ :=
    AutomorphicForm.exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul
      K L σ D C hC

  set C'' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    C * (AutomorphicForm.sigmaAdelicAct K L D σ '' C')⁻¹ * C' with hC''def
  have hC'' : IsCompact C'' := (hC.mul (hC'.image hScont).inv).mul hC'
  set Ω : Set (AdeleRing (𝓞 L) L)ˣ := AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C'' with hΩdef
  have hΩ : IsCompact Ω := hcs.isCompact_preimage hC''

  obtain ⟨CZ, hCZ, hZ⟩ :=
    M4aHerbrand.IdeleGaloisDescent.exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem
      K L σ D Ω hΩ
  refine ⟨AutomorphicForm.centralScalar (𝓞 L) L '' CZ * C',
    (hCZ.image (continuous_centralScalar L)).mul hC', ?_⟩
  intro x hx

  have hx' : x⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ x ∈
      (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * C :=
    Set.mem_mul.2 ⟨1, (Subgroup.center _).one_mem, _, hx, one_mul _⟩
  obtain ⟨g, k, hg, hk, hxgk⟩ := hmod x hx'
  obtain ⟨ζ, hζ⟩ := exists_eq_centralScalar_of_mem_center L hg

  have hzC'' : g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g ∈ C'' := by
    have hcomm : k⁻¹ * (g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g) =
        (g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g) * k⁻¹ :=
      ((Subgroup.mem_center_iff.1 hg) k⁻¹)
    have hxz : x⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ x =
        (g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g) * k⁻¹ *
          AutomorphicForm.sigmaAdelicAct K L D σ k := by
      rw [hxgk, mul_inv_rev, map_mul, ← hcomm]
      group
    have hz : g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g =
        (x⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ x) *
          (AutomorphicForm.sigmaAdelicAct K L D σ k)⁻¹ * k := by
      rw [hxz]; group
    rw [hz]
    refine Set.mem_mul.2 ⟨_, Set.mem_mul.2 ⟨_, hx, _, ?_, rfl⟩, k, hk, rfl⟩
    exact Set.inv_mem_inv.2 ⟨k, hk, rfl⟩
  have hζΩ : ζ ∈ Ω := by
    show AutomorphicForm.centralScalar (𝓞 L) L ζ ∈ C''
    rw [← hζ]; exact hzC''

  obtain ⟨w, hw⟩ :=
    M4aHerbrand.IdeleGaloisDescent.exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one K L σ D ζ
      (prod_unitsAct_pow_eq_one g ζ hζ)

  have hwΩ : D.unitsAct σ w * w⁻¹ ∈ Ω := by
    rw [mul_comm, ← hw]; exact hζΩ
  obtain ⟨f, c, hf, hc, hwfc⟩ := hZ w hwΩ

  have hS : AutomorphicForm.sigmaAdelicAct K L D σ g =
      g * AutomorphicForm.centralScalar (𝓞 L) L ζ := by
    rw [← hζ, mul_inv_cancel_left]
  set F : AutomorphicForm.AdelicGL2 (𝓞 L) L :=
    g * (AutomorphicForm.centralScalar (𝓞 L) L w)⁻¹ * AutomorphicForm.centralScalar (𝓞 L) L f
    with hFdef
  have hFfix : AutomorphicForm.sigmaAdelicAct K L D σ F = F := by
    rw [hFdef, map_mul, map_mul, map_inv, hS, sigmaAdelicAct_centralScalar,
      sigmaAdelicAct_centralScalar, hf, hw, map_mul, map_inv]
    group
  refine ⟨F, AutomorphicForm.centralScalar (𝓞 L) L c * k, hFfix,
    Set.mem_mul.2 ⟨_, Set.mem_image_of_mem _ hc, k, hk, rfl⟩, ?_⟩
  rw [hxgk, hFdef, hwfc, map_mul]
  group

end AdeleSide

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def transportEquiv : (L ⊗[K] AdeleRing (𝓞 K) K) ≃+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L))

theorem continuous_transportEquiv :
    Continuous (transportEquiv K L) ∧ Continuous (transportEquiv K L).symm := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L
      (M4aHerbrand.Bridge.continuous_genuineβ K L) (M4aHerbrand.Bridge.genuineTensorEquiv K L)
  let eLin : (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
    (TensorProduct.RightActions.Module.TensorProduct.comm K (AdeleRing (𝓞 K) K) L).symm.trans
      (M4aHerbrand.Bridge.genuineTensorEquiv K L).toLinearEquiv
  have hfun : ∀ x, eLin x = transportEquiv K L x := by
    intro x
    rfl
  let eC := IsModuleTopology.continuousLinearEquiv eLin
  have h1 : Continuous (transportEquiv K L) := by
    have : Continuous eC := eC.continuous
    exact this.congr hfun
  have h2 : Continuous (transportEquiv K L).symm := by
    have hc : Continuous eC.symm := eC.symm.continuous
    refine hc.congr fun y => ?_
    apply (transportEquiv K L).injective
    rw [RingEquiv.apply_symm_apply]
    show transportEquiv K L (eLin.symm y) = y
    rw [← hfun, LinearEquiv.apply_symm_apply]
  exact ⟨h1, h2⟩

noncomputable abbrev GE :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) →* AutomorphicForm.AdelicGL2 (𝓞 L) L :=
  Matrix.GeneralLinearGroup.map (transportEquiv K L).toRingHom

noncomputable abbrev GEi :
    AutomorphicForm.AdelicGL2 (𝓞 L) L →* GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (transportEquiv K L).symm.toRingHom

theorem GEi_GE (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : GEi K L (GE K L g) = g := by
  ext i j
  exact (transportEquiv K L).symm_apply_apply (g.val i j)

theorem GE_GEi (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) : GE K L (GEi K L g) = g := by
  ext i j
  exact (transportEquiv K L).apply_symm_apply (g.val i j)

theorem GE_injective : Function.Injective (GE K L) :=
  Function.LeftInverse.injective (GEi_GE K L)

theorem continuous_GE : Continuous (GE K L) :=
  continuous_generalLinearGroup_map _ (continuous_transportEquiv K L).1

theorem continuous_GEi : Continuous (GEi K L) :=
  continuous_generalLinearGroup_map _ (continuous_transportEquiv K L).2

theorem GE_sigmaGL (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    GE K L (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ g) =
      AutomorphicForm.sigmaAdelicAct K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) σ
        (GE K L g) :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).1 σ g

end Transport

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          x⁻¹ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x ∈ C} ⊆
        ((AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ 1 :
            Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D := by
  set D₀ := M4aHerbrand.GenuineDescent.genuineDescentDatum K L with hD₀

  have hC₁ : IsCompact (GE K L '' C) := hC.image (continuous_GE K L)
  obtain ⟨D₁, hD₁, hdec⟩ := exists_isCompact_forall_exists_fixed_mul K L σ D₀ (GE K L '' C) hC₁
  refine ⟨GEi K L '' D₁, hD₁.image (continuous_GEi K L), ?_⟩
  intro x hx
  have hx₁ : (GE K L x)⁻¹ * AutomorphicForm.sigmaAdelicAct K L D₀ σ (GE K L x) ∈ GE K L '' C :=
    ⟨_, hx, by rw [map_mul, map_inv, GE_sigmaGL]⟩
  obtain ⟨F, d, hF, hd, hxFd⟩ := hdec (GE K L x) hx₁
  refine Set.mem_mul.2 ⟨GEi K L F, ?_, GEi K L d, Set.mem_image_of_mem _ hd, ?_⟩
  ·
    show GEi K L F ∈ AutomorphicForm.sigmaCentralizer
      (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ) 1
    rw [AutomorphicForm.mem_sigmaCentralizer_iff, mul_one, mul_inv_eq_one]
    apply GE_injective K L
    rw [GE_sigmaGL, GE_GEi, ← hD₀, hF]
  · rw [← map_mul, ← hxFd, GEi_GE]

end P2mAdelicH90Proper

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          x⁻¹ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x ∈ C} ⊆
        ((AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ 1 :
            Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D :=
  P2mAdelicH90Proper.main K L σ C hC

end S_AutomorphicForm_exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_setOf_inv_mul_sigmaGL_mem_subset_twistedCentralizer_one_mul (solution)
