-- Prove2me | solution 1 for AutomorphicForm.exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f78a1263-22dd-589d-b67a-19121b83245e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Mathlib
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_IsRegularSemisimple_mul_comm_of_mem_centralizer
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_image_mulEquiv_op_subgroupOf
import Theorems.Thm_AutomorphicForm_eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_exists_adeleRing_of_isRegularSemisimple
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

noncomputable section

namespace TorusBridgeAux

theorem map_scalar {n : Type*} [DecidableEq n] [Fintype n] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar n u) =
      Matrix.GeneralLinearGroup.scalar n (Units.map (f : R →* S) u) := by
  refine Units.ext ?_
  ext i j
  change f ((Matrix.scalar n (u : R)) i j) = (Matrix.scalar n (f u)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

private theorem _root_.TorusBridgeAux.scalar_commute {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R] (u : Rˣ) (g : GL n R) :
    Matrix.GeneralLinearGroup.scalar n u * g = g * Matrix.GeneralLinearGroup.scalar n u := by
  refine Units.ext ?_
  change Matrix.scalar n (u : R) * (g : Matrix n n R) = (g : Matrix n n R) * Matrix.scalar n (u : R)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

p2m_export "TorusBridgeAux" "scalar_commute"
end TorusBridgeAux

theorem TorusBridgeAux.exists_continuousMulEquiv_centralizer_of_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {g g' : G} (h : g = g') :
    ∃ C : Subgroup.centralizer ({g} : Set G) ≃ₜ* Subgroup.centralizer ({g'} : Set G),
      ∀ x, ((C x : Subgroup.centralizer ({g'} : Set G)) : G) = (x : G) := by
  subst h
  exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl⟩

namespace TorusBridge

open AutomorphicForm NumberField.AdelicLevel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def φ : (AutomorphicForm.AdelicGL2 (𝓞 L) L) ≃* (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) where
  toFun := Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom
  invFun := Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom
  left_inv g := by
    show Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ g) = g
    rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
      RingEquiv.toRingHom_comp_symm_toRingHom, Matrix.GeneralLinearGroup.map_id]; rfl
  right_inv g := by
    show Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ g) = g
    rw [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
      RingEquiv.symm_toRingHom_comp_toRingHom, Matrix.GeneralLinearGroup.map_id]; rfl
  map_mul' := map_mul _

theorem φ_apply (g : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
    φ K L g = Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).symm.toRingHom g := rfl

theorem φ_symm_apply (g : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
    (φ K L).symm g = Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom g := rfl

theorem bc_eq : AutomorphicForm.baseChangeGL K L =
    Matrix.GeneralLinearGroup.map (AutomorphicForm.baseChangeEquiv K L).toRingHom := rfl

theorem continuous_φ : Continuous (φ K L) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  exact AutomorphicForm.continuous_glMap _ (AutomorphicForm.continuous_baseChangeEquiv_symm K L)

theorem continuous_φ_symm : Continuous (φ K L).symm := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  exact AutomorphicForm.continuous_glMap _ (AutomorphicForm.continuous_baseChangeEquiv K L)

theorem φ_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (g : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
    φ K L (AutomorphicForm.sigmaAdelicAct K L D τ g) =
      AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) τ (φ K L g) := by
  apply (φ K L).symm.injective
  have h := (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).1 τ (φ K L g)
  have h2 : (φ K L).symm (φ K L g) = g := (φ K L).symm_apply_apply g
  calc (φ K L).symm (φ K L (AutomorphicForm.sigmaAdelicAct K L D τ g))
      = AutomorphicForm.sigmaAdelicAct K L D τ g := (φ K L).symm_apply_apply _
    _ = AutomorphicForm.sigmaAdelicAct K L D τ ((φ K L).symm (φ K L g)) := by rw [h2]
    _ = (φ K L).symm (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) τ (φ K L g)) := h.symm

theorem φ_globalPoints (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (δ : GL (Fin 2) L) :
    φ K L (AutomorphicForm.globalPoints (𝓞 L) L δ) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ := by
  apply (φ K L).symm.injective
  have h := (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).2.2 δ
  calc (φ K L).symm (φ K L (AutomorphicForm.globalPoints (𝓞 L) L δ))
      = AutomorphicForm.globalPoints (𝓞 L) L δ := (φ K L).symm_apply_apply _
    _ = _ := h.symm

theorem φ_symm_toTensorGL (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    (φ K L).symm (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g := by
  exact (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).2.1 g

theorem normString_eq_sigmaNormPow (A : Type) [CommRing A] [Algebra K A] [FiniteDimensional K L] (τ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A τ δ =
      LT.TwistedNorm.sigmaNormPow (AutomorphicForm.sigmaGL K L A τ) (Module.finrank K L) δ := by
  rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  rfl

theorem map_includeLeft_map_sigma (A : Type) [CommRing A] [Algebra K A] (τ : L ≃ₐ[K] L) (x : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (Matrix.GeneralLinearGroup.map (τ : L →+* L) x) =
      AutomorphicForm.sigmaGL K L A τ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Algebra.TensorProduct.includeLeftRingHom (τ ((x : Matrix (Fin 2) (Fin 2) L) i j)) =
    AutomorphicForm.sigmaTensor K L A τ (Algebra.TensorProduct.includeLeftRingHom ((x : Matrix (Fin 2) (Fin 2) L) i j))
  change (τ ((x : Matrix (Fin 2) (Fin 2) L) i j)) ⊗ₜ[K] (1 : A) =
    (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A)) (((x : Matrix (Fin 2) (Fin 2) L) i j) ⊗ₜ[K] (1 : A))
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem map_includeLeft_map_algebraMap (A : Type) [CommRing A] [Algebra K A] (g : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (Matrix.GeneralLinearGroup.map (algebraMap K L) g) =
      AutomorphicForm.toTensorGL K L A (Matrix.GeneralLinearGroup.map (algebraMap K A) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (algebraMap K L ((g : Matrix (Fin 2) (Fin 2) K) i j)) ⊗ₜ[K] (1 : A) =
    (1 : L) ⊗ₜ[K] (algebraMap K A ((g : Matrix (Fin 2) (Fin 2) K) i j))
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

theorem isRegularSemisimple_of_mem_ellipticCell (γ : GL (Fin 2) K) (hγ : γ ∈ AutomorphicForm.ellipticCell K) :
    AutomorphicForm.IsRegularSemisimple γ := by
  rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero]
  intro h

  apply hγ ((γ : Matrix (Fin 2) (Fin 2) K).trace / 2)
  rw [Polynomial.IsRoot, Matrix.charpoly_fin_two]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  have h' : Matrix.det (γ : Matrix (Fin 2) (Fin 2) K) = Matrix.trace (γ : Matrix (Fin 2) (Fin 2) K) ^ 2 / 4 := by
    rw [eq_div_iff (by norm_num : (4 : K) ≠ 0)]
    linear_combination (-1 : K) * h
  rw [h']
  ring

end TorusBridge

end

namespace CltAux

open MeasureTheory

theorem exists_cme_of_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H₁ H₂ : Subgroup G} (h : H₁ = H₂) :
    ∃ C : H₁ ≃ₜ* H₂, ∀ x, ((C x : H₂) : G) = (x : G) := by
  subst h
  exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl⟩

theorem centralizer_mul_eq_of_central {G : Type*} [Group G] (g z : G) (hz : ∀ x : G, x * z = z * x) :
    Subgroup.centralizer ({g * z} : Set G) = Subgroup.centralizer ({g} : Set G) := by
  ext k
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : k * g * z = g * k * z := by
      rw [mul_assoc, h, mul_assoc, ← hz k, mul_assoc]
    exact mul_right_cancel h'
  · intro h
    rw [← mul_assoc, h, mul_assoc, hz k, mul_assoc]

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (h : ∀ a b : G, a * b = b * a) : μ.IsMulRightInvariant := by
  constructor
  intro g
  have : (fun x : G => x * g) = fun x : G => g * x := funext fun x => h x g
  rw [this]
  exact MeasureTheory.map_mul_left_eq_self μ g

theorem comm_of_injective {G H : Type*} [Mul G] [Mul H] (f : G → H) (hf : Function.Injective f)
    (hmul : ∀ a b, f (a * b) = f a * f b) (h : ∀ a b : H, a * b = b * a) : ∀ a b : G, a * b = b * a :=
  fun a b => hf (by rw [hmul, hmul, h])

end CltAux

namespace CltAux
theorem conj_central_rearrange {G : Type*} [Group G] (g x c1 c2 : G) (h1 : ∀ y : G, y * c1 = c1 * y)
    (h2 : ∀ y : G, y * c2 = c2 * y) : c2 * (x⁻¹ * (g * c1) * x) = x⁻¹ * g * x * (c1 * c2) := by
  calc c2 * (x⁻¹ * (g * c1) * x) = (x⁻¹ * (g * c1) * x) * c2 := (h2 _).symm
    _ = x⁻¹ * g * (c1 * x) * c2 := by simp only [mul_assoc]
    _ = x⁻¹ * g * (x * c1) * c2 := by rw [← h1 x]
    _ = x⁻¹ * g * x * (c1 * c2) := by simp only [mul_assoc]
end CltAux

namespace CltAux2

open MeasureTheory AutomorphicForm NumberField

theorem cov_of_eq (K : Type) [Field K] [NumberField K]
    (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ AutomorphicForm.ellipticCell K) (u : (AdeleRing (𝓞 K) K)ˣ)
    (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hH : H = Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K u} :
      Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))
    [inst : MeasurableSpace H] [hB : BorelSpace H]
    (τ : Measure H) [τ.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D : Set H,
        IsFundamentalDomain
          (((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map
            (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf H).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : (AutomorphicForm.AdelicGL2 (𝓞 K) K))) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by
  subst hH
  obtain ⟨hB'⟩ := hB
  subst hB'
  exact AutomorphicForm.exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell
    K γ₀ hγ₀ u τ

theorem sigmaCompactSpace_adelicGL2 (K : Type) [Field K] [NumberField K] : SigmaCompactSpace (AutomorphicForm.AdelicGL2 (𝓞 K) K) := by
  haveI : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

end CltAux2

namespace CltMain

open MeasureTheory AutomorphicForm NumberField TorusBridge

theorem exists_bridge (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) :
    ∃ B : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ≃ₜ* (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))), ∀ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), ((B t : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) = TorusBridge.φ K L (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  let iL : GL (Fin 2) L →* (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)
  have hδ' : (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = iL δ₀ := by rw [map_one, mul_one]
  have hmap : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)).map ((TorusBridge.φ K L : (AutomorphicForm.AdelicGL2 (𝓞 L) L) ≃* (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : (AutomorphicForm.AdelicGL2 (𝓞 L) L) →* (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) = (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) := by
    ext s
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [AutomorphicForm.mem_sigmaCentralizer_iff] at ht
      show _ ∈ AutomorphicForm.sigmaCentralizer _ _
      rw [AutomorphicForm.mem_sigmaCentralizer_iff, hδ', MonoidHom.coe_coe, ← φ_sigmaAdelicAct K L D,
        ← φ_globalPoints K L D, ← map_inv, ← map_mul, ← map_mul, ht]
    · intro hs
      refine ⟨(TorusBridge.φ K L).symm s, ?_, (TorusBridge.φ K L).apply_symm_apply s⟩
      change s ∈ AutomorphicForm.sigmaCentralizer _ _ at hs
      rw [AutomorphicForm.mem_sigmaCentralizer_iff] at hs ⊢
      apply (TorusBridge.φ K L).injective
      rw [map_mul, map_mul, map_inv, φ_sigmaAdelicAct K L D, φ_globalPoints K L D, MulEquiv.apply_symm_apply,
        ← hδ', hs]
  have hfwd : ∀ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), TorusBridge.φ K L (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) ∈ (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) := by
    intro t; rw [← hmap]; exact ⟨t, t.2, rfl⟩
  have hbwd : ∀ s : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))), (TorusBridge.φ K L).symm (s : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∈ (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) := by
    intro s
    have hs : (s : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∈ (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)).map ((TorusBridge.φ K L : (AutomorphicForm.AdelicGL2 (𝓞 L) L) ≃* (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : (AutomorphicForm.AdelicGL2 (𝓞 L) L) →* (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) := by
      rw [hmap]; exact s.2
    obtain ⟨t, ht, hts⟩ := hs
    rw [← hts, MonoidHom.coe_coe, MulEquiv.symm_apply_apply]
    exact ht
  let Bm : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ≃* (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) :=
    { toFun := fun t => ⟨TorusBridge.φ K L (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)), hfwd t⟩
      invFun := fun s => ⟨(TorusBridge.φ K L).symm (s : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))), hbwd s⟩
      left_inv := fun t => Subtype.ext ((TorusBridge.φ K L).symm_apply_apply _)
      right_inv := fun s => Subtype.ext ((TorusBridge.φ K L).apply_symm_apply _)
      map_mul' := fun t t' => Subtype.ext (map_mul (TorusBridge.φ K L) _ _) }
  have hc1' : Continuous fun t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) => (⟨TorusBridge.φ K L (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)), hfwd t⟩ : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) :=
    ((continuous_φ K L).comp continuous_subtype_val).subtype_mk _
  have hc2' : Continuous fun s : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) => (⟨(TorusBridge.φ K L).symm (s : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))), hbwd s⟩ : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀))) :=
    ((continuous_φ_symm K L).comp continuous_subtype_val).subtype_mk _
  exact ⟨⟨Bm, hc1', hc2'⟩, fun t => rfl⟩

theorem isNormRep_of_normClassMap_eq (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm) (γ₀ : GL (Fin 2) K) (a : Kˣ) (δ₀ : GL (Fin 2) L)
    (hNcl : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) :
    LT.TwistedNorm.IsNormRep σ.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) δ₀ := by
  rw [LT.TwistedNorm.normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hNcl
  obtain ⟨c, hc⟩ := hNcl
  obtain ⟨P, hP⟩ := LT.TwistedNorm.isNormRep_normRep hgen δ₀
  refine ⟨P * (Matrix.GeneralLinearGroup.map (algebraMap K L) c)⁻¹, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv, ← hP]
  group

theorem isNormConjugator_includeLeft (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (γ₀ : GL (Fin 2) K) (a : Kˣ) (δ₀ P : GL (Fin 2) L)
    (hP : P⁻¹ * LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) (Module.finrank K L) δ₀ * P =
      Matrix.GeneralLinearGroup.map (algebraMap K L) (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) :
    AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ.symm
      (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1))
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) P) := by
  let iL : GL (Fin 2) L →* (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)
  have hδ' : (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = iL δ₀ := by rw [map_one, mul_one]
  have hNS : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) =
      iL (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) (Module.finrank K L) δ₀) := by
    rw [hδ', normString_eq_sigmaNormPow K L,
      LT.TwistedNorm.hom_sigmaNormPow (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L))
        (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ.symm) iL (fun x => map_includeLeft_map_sigma K L (AdeleRing (𝓞 K) K) σ.symm x)]
  have hγu : AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1) =
      Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) := by
    rw [mul_one, map_mul, TorusBridgeAux.map_scalar]
    exact (TorusBridgeAux.scalar_commute _ _).symm
  unfold AutomorphicForm.IsNormConjugator
  rw [hNS, hγu, ← map_includeLeft_map_algebraMap K L, ← hP, map_mul, map_mul, map_inv]

theorem normString_scalar_one (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) :
    AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.scalar (Fin 2) 1) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K 1) := by
  rw [map_one, map_one, map_one, normString_eq_sigmaNormPow K L, LT.TwistedNorm.sigmaNormPow_one_left]

theorem ideleNorm_det_eq_pow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (s : (AutomorphicForm.AdelicGL2 (𝓞 K) K)) (x : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (y : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))
    (h : AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) s = y⁻¹ * TorusBridge.φ K L x * y) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) =
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det s) ^ Module.finrank K L := by
  have hd : Matrix.GeneralLinearGroup.det (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) s) =
      Matrix.GeneralLinearGroup.det (TorusBridge.φ K L x) := by
    rw [h, map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  rw [φ_apply] at hd
  unfold AutomorphicForm.toTensorGL at hd
  rw [Matrix.GeneralLinearGroup.map_det, Matrix.GeneralLinearGroup.map_det] at hd
  have hdet : Matrix.GeneralLinearGroup.det x =
      AutomorphicForm.TransversalMeasure.idelesBaseChange K L (Matrix.GeneralLinearGroup.det s) := by
    refine Units.ext ?_
    have hv := congrArg (fun u : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ =>
      AutomorphicForm.baseChangeEquiv K L (u : L ⊗[K] AdeleRing (𝓞 K) K)) hd
    simp only [Units.coe_map, MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at hv
    rw [← hv]
    change AutomorphicForm.baseChangeEquiv K L ((1 : L) ⊗ₜ[K]
      ((Matrix.GeneralLinearGroup.det s : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K))) = _
    rw [AutomorphicForm.baseChangeEquiv_one_tmul]
    rfl
  rw [hdet, NumberField.TateGlobal.ideleNorm_idelesBaseChange]

theorem cov_transfer {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]
    [MeasurableMul A] [MeasurableMul B]
    (e : A ≃ₜ* B) (H : Subgroup A) (H' : Subgroup B) (hH : ∀ a, e a ∈ H' ↔ a ∈ H)
    (NA : A → ℝ) (NB : B → ℝ) (ℓ : ℕ) (hℓ : ℓ ≠ 0) (hNB : ∀ b, 0 < NB b) (hN : ∀ a, NA a = NB (e a) ^ ℓ)
    (τ : Measure B) (C : ENNReal)
    (hcov : ∀ D : Set B, IsFundamentalDomain H'.op D τ → ∀ a b : ℝ, 0 < a → a ≤ b →
      τ (D ∩ {t | NB t ∈ Set.Icc a b}) = C * ENNReal.ofReal (Real.log (b / a))) :
    ∀ D' : Set A, IsFundamentalDomain H.op D' (τ.map e.symm) → ∀ a b : ℝ, 0 < a → a ≤ b →
      (τ.map e.symm) (D' ∩ {t | NA t ∈ Set.Icc a b}) = C * ENNReal.ofReal (Real.log (b / a) / ℓ) := by
  intro D' hD' a b ha hab
  let me : A ≃ᵐ B := e.toHomeomorph.toMeasurableEquiv
  have hme : (me : A → B) = (e : A → B) := rfl
  have hmes : (me.symm : B → A) = (e.symm : B → A) := rfl
  have hem : Measurable (e : A → B) := hme ▸ me.measurable
  have hesm : Measurable (e.symm : B → A) := hmes ▸ me.symm.measurable
  have hmapback : (τ.map e.symm).map e = τ := by
    rw [← hme, ← hmes]; exact MeasurableEquiv.map_map_symm me
  have hFD := MeasureTheory.IsFundamentalDomain.image_mulEquiv_op_subgroupOf e.toMulEquiv
    hem hesm H H' (fun t => hH t) (τ.map e.symm) D' hD'
  rw [show ((e.toMulEquiv : A ≃* B) : A → B) = (e : A → B) from rfl, hmapback] at hFD
  have hℓ' : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hℓ
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = a ^ ((ℓ : ℝ)⁻¹) := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b' = b ^ ((ℓ : ℝ)⁻¹) := ⟨_, rfl⟩
  have ha'pos : 0 < a' := by rw [ha']; exact Real.rpow_pos_of_pos ha _
  have ha'b' : a' ≤ b' := by rw [ha', hb']; exact Real.rpow_le_rpow ha.le hab (inv_nonneg.mpr hℓ'.le)
  have key := hcov _ hFD a' b' ha'pos ha'b'
  have hset : (e : A → B) '' (D' ∩ {t | NA t ∈ Set.Icc a b}) = (e : A → B) '' D' ∩ {s | NB s ∈ Set.Icc a' b'} := by
    rw [Set.image_inter e.injective]
    congr 1
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [Set.mem_setOf_eq, hN t] at ht
      have hx := hNB (e t)
      refine ⟨?_, ?_⟩
      · rw [ha', ← Real.pow_rpow_inv_natCast hx.le hℓ]
        exact Real.rpow_le_rpow ha.le ht.1 (inv_nonneg.mpr hℓ'.le)
      · rw [hb', ← Real.pow_rpow_inv_natCast hx.le hℓ]
        exact Real.rpow_le_rpow (pow_nonneg hx.le _) ht.2 (inv_nonneg.mpr hℓ'.le)
    · intro hs
      refine ⟨e.symm s, ?_, e.apply_symm_apply s⟩
      rw [Set.mem_setOf_eq, hN, e.apply_symm_apply]
      have hx := hNB s
      refine ⟨?_, ?_⟩
      · rw [← Real.rpow_inv_natCast_pow ha.le hℓ, ← ha']
        exact pow_le_pow_left₀ ha'pos.le hs.1 _
      · rw [← Real.rpow_inv_natCast_pow (ha.le.trans hab) hℓ, ← hb']
        exact pow_le_pow_left₀ hx.le hs.2 _
  have hmeas : (τ.map e.symm) (D' ∩ {t | NA t ∈ Set.Icc a b}) = τ ((e : A → B) '' (D' ∩ {t | NA t ∈ Set.Icc a b})) := by
    rw [← hmes, MeasurableEquiv.map_apply]
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h; exact ⟨me.symm s, h, by rw [← hme]; exact me.apply_symm_apply s⟩
    · rintro ⟨t, ht, rfl⟩
      rw [← hme, me.symm_apply_apply]; exact ht
  rw [hmeas, hset, key, ha', hb', ← Real.div_rpow (ha.le.trans hab) ha.le, Real.log_rpow (div_pos (ha.trans_le hab) ha)]
  congr 2
  ring

end CltMain

namespace CltMain

open MeasureTheory AutomorphicForm NumberField TorusBridge

theorem exists_isTwistedOrbitalIntegralOn (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (δ : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ')
    (ψ : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) → ℂ) (hψ : HasCompactSupport ψ) :
    ∃ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ' ψ I := by
  obtain ⟨w, hw⟩ := AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
    K L σ δ hδ τ' hτ' ψ hψ
  exact ⟨_, w, hw, rfl⟩

theorem sigmaAdelicAct_centralScalar (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D τ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct τ z) := by
  change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) _
  rw [TorusBridgeAux.map_scalar]
  congr 1

theorem integrand_bridge (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L)
    (φt : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (x : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) :
    φt (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) =
      ((fun g : (AutomorphicForm.AdelicGL2 (𝓞 L) L) => φt (AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ.symm z) * g)) ∘
          AutomorphicForm.baseChangeGL K L)
        ((TorusBridge.φ K L x)⁻¹ * (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) *
          AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ.symm (TorusBridge.φ K L x)) := by
  have hδ' : (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = TorusBridge.φ K L (AutomorphicForm.globalPoints (𝓞 L) L δ₀) := by
    rw [map_one, mul_one, φ_globalPoints K L D]
  have hbc : ∀ g : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), AutomorphicForm.baseChangeGL K L g = (TorusBridge.φ K L).symm g := fun g => rfl
  simp only [Function.comp_apply]
  rw [hbc, hδ', ← φ_sigmaAdelicAct K L D, ← map_inv, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply,
    map_mul, sigmaAdelicAct_centralScalar K L D]
  congr 1
  simp only [← mul_assoc]
  rw [AutomorphicForm.SiegelCovering.mul_centralScalar_comm (D.unitsAct σ.symm z)
    (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀)]
  simp only [mul_assoc]

end CltMain

namespace CltMain

open MeasureTheory AutomorphicForm NumberField TorusBridge

noncomputable def φh (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : (AutomorphicForm.AdelicGL2 (𝓞 L) L) ≃ₜ (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  { toEquiv := (TorusBridge.φ K L).toEquiv
    continuous_toFun := continuous_φ K L
    continuous_invFun := continuous_φ_symm K L }

theorem φh_coe (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ((φh K L : (AutomorphicForm.AdelicGL2 (𝓞 L) L) ≃ₜ (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) = (TorusBridge.φ K L : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) := rfl

theorem section_bridge (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (δ₀ : GL (Fin 2) L)
    (B : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ≃ₜ* (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) (hB : ∀ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), ((B t : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) = TorusBridge.φ K L (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (τ' : Measure (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)))
    (φt : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (wt : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) → ℝ)
    (hwt : AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))
      (@Measure.map _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) B τ')
      ((fun g : (AutomorphicForm.AdelicGL2 (𝓞 L) L) => φt (AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ.symm z) * g)) ∘
          AutomorphicForm.baseChangeGL K L) wt) :
    ((∀ x, 0 ≤ wt (TorusBridge.φ K L x)) ∧ Measurable (fun x => wt (TorusBridge.φ K L x)) ∧
      HasCompactSupport (fun x => wt (TorusBridge.φ K L x)) ∧
      (∀ x : (AutomorphicForm.AdelicGL2 (𝓞 L) L), φt (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0 →
        ∫ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), wt (TorusBridge.φ K L ((t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * x)) ∂τ' = 1)) ∧
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ.symm
        (@Measure.map _ _ _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) (TorusBridge.φ K L)
          (adelicGLHaar (Fin 2) (𝓞 L) L))
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) (@Measure.map _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) B τ')
        ((fun g : (AutomorphicForm.AdelicGL2 (𝓞 L) L) => φt (AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ.symm z) * g)) ∘
          AutomorphicForm.baseChangeGL K L)
        (∫ x, φt (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) *
          (wt (TorusBridge.φ K L x) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) := (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) := ⟨rfl⟩
  have hφm : Measurable (TorusBridge.φ K L : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) := (continuous_φ K L).measurable
  obtain ⟨hw0, hwm, hwc, hw1⟩ := hwt
  have hident := integrand_bridge K L D σ δ₀ φt z

  let Φm : (AutomorphicForm.AdelicGL2 (𝓞 L) L) ≃ᵐ (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := (φh K L).toMeasurableEquiv
  have hΦm : (Φm : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) = (TorusBridge.φ K L : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) := rfl
  let Bm : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ≃ᵐ (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) := B.toHomeomorph.toMeasurableEquiv
  have hBm : (Bm : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) → (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) = (B : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) → (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) := rfl
  have hsec : ∀ x : (AutomorphicForm.AdelicGL2 (𝓞 L) L), φt (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0 →
      ∫ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), wt (TorusBridge.φ K L ((t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * x)) ∂τ' = 1 := by
    intro x hx
    rw [hident] at hx
    have h := hw1 (TorusBridge.φ K L x) hx
    rw [← hBm, MeasureTheory.integral_map_equiv] at h
    simpa only [hBm, hB, map_mul] using h
  refine ⟨⟨fun x => hw0 _, hwm.comp hφm, ?_, hsec⟩, ?_⟩
  · have := hwc.comp_homeomorph (φh K L)
    rwa [φh_coe] at this
  · refine ⟨wt, ⟨hw0, hwm, hwc, hw1⟩, ?_⟩
    rw [← hΦm, MeasureTheory.integral_map_equiv]
    simp only [hΦm]
    congr 1
    funext x
    rw [hident]

end CltMain

namespace CltB

theorem isRegularSemisimple_toTensorGL
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.toTensorGL K L A γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  have hmat : ((AutomorphicForm.toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (γ : Matrix (Fin 2) (Fin 2) A).map
        ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom) := rfl
  rw [hmat, Matrix.trace, Matrix.det_fin_two]
  rw [Matrix.trace, Matrix.det_fin_two] at hγ
  simp only [Matrix.diag_apply, Matrix.map_apply, Fin.sum_univ_two] at hγ ⊢
  have := hγ.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
  simpa [map_sub, map_mul, map_pow, map_add, map_ofNat] using this

theorem isRegularSemisimple_normString_of_isNormConjugator
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (δ y : GL (Fin 2) (L ⊗[K] A)) (hy : AutomorphicForm.IsNormConjugator K L A σ γ δ y) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ) := by
  have h : AutomorphicForm.normString K L A σ δ = (y⁻¹)⁻¹ * AutomorphicForm.toTensorGL K L A γ * y⁻¹ := by
    unfold AutomorphicForm.IsNormConjugator at hy
    rw [hy, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one]
  rw [h]
  exact (isRegularSemisimple_toTensorGL K L A γ hγ).conj y⁻¹

theorem idelicNorm_unitsAct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (D.unitsAct τ z) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z := by
  obtain ⟨hinj, -, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
  have hinjU : Function.Injective (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom) :=
    fun a b hab => Units.ext (hinj (congrArg Units.val hab))
  apply hinjU
  rw [← hprod, ← hprod]

  rw [← Fintype.prod_equiv (Equiv.mulRight τ) (fun τ' => D.unitsAct τ' (D.unitsAct τ z)) (fun τ'' => D.unitsAct τ'' z)]
  intro τ'
  simp only [Equiv.coe_mulRight, map_mul, MulAut.mul_apply]

theorem isOrbitalIntegralOn_transfer
    (K : Type) [Field K] [NumberField K]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (γ₁ γ₂ : AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (C : Subgroup.centralizer ({γ₁} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) ≃ₜ*
      Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))
    (hC : ∀ x, ((C x : Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) :
      AutomorphicForm.AdelicGL2 (𝓞 K) K) = (x : AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (τ₂ : Measure (Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (f₁ f₂ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K, f₁ (x⁻¹ * γ₁ * x) = f₂ (x⁻¹ * γ₂ * x)) (I : ℂ)
    (h : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ₂ τ₂ f₂ I) :
    AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ₁ (τ₂.map C.symm) f₁ I := by
  haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  obtain ⟨w, ⟨hw0, hwm, hws, hw1⟩, hI⟩ := h
  have hCsymm : ∀ t : Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
      ((C.symm t : Subgroup.centralizer ({γ₁} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) :
        AutomorphicForm.AdelicGL2 (𝓞 K) K) = (t : AutomorphicForm.AdelicGL2 (𝓞 K) K) := by
    intro t
    have := hC (C.symm t)
    rw [ContinuousMulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨w, ⟨hw0, hwm, hws, fun x hx => ?_⟩, ?_⟩
  · rw [hf] at hx
    let e : Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) ≃ᵐ
        Subgroup.centralizer ({γ₁} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) :=
      C.symm.toHomeomorph.toMeasurableEquiv
    have he : (Measure.map (⇑C.symm) τ₂) = Measure.map (⇑e) τ₂ := rfl
    rw [he, MeasureTheory.integral_map_equiv e]
    have : (fun t : Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) =>
        w (((e t : Subgroup.centralizer ({γ₁} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) :
          AutomorphicForm.AdelicGL2 (𝓞 K) K) * x)) =
        fun t : Subgroup.centralizer ({γ₂} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) =>
          w ((t : AutomorphicForm.AdelicGL2 (𝓞 K) K) * x) := by
      funext t
      show w (((C.symm t : Subgroup.centralizer ({γ₁} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) :
        AutomorphicForm.AdelicGL2 (𝓞 K) K) * x) = _
      rw [hCsymm t]
    rw [this]
    exact hw1 x hx
  · rw [hI]
    congr 1
    funext x
    rw [hf x]

end CltB

namespace CltAux

theorem isRegularSemisimple_mul_scalar {A : Type*} [CommRing A] (u : Aˣ) {g : GL (Fin 2) A}
    (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (g * Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  unfold AutomorphicForm.IsRegularSemisimple at hg ⊢
  have hmat : ((g * Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      (u : A) • (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [← TorusBridgeAux.scalar_commute, Units.val_mul]
    change Matrix.scalar (Fin 2) (u : A) * (g : Matrix (Fin 2) (Fin 2) A) = (u : A) • (g : Matrix (Fin 2) (Fin 2) A)
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  rw [hmat, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]
  have : ((u : A) * Matrix.trace (g : Matrix (Fin 2) (Fin 2) A)) ^ 2 -
      4 * ((u : A) ^ 2 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)) =
      (u : A) ^ 2 * (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)) := by
    ring
  rw [this]
  exact (Units.isUnit (u ^ 2)).mul hg

end CltAux

namespace CltMain

open MeasureTheory AutomorphicForm NumberField TorusBridge

theorem clause_b (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (γ₀ : GL (Fin 2) K) (a : Kˣ) (δ₀ : GL (Fin 2) L) (c₀ : NNReal)
    (φ : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → ℂ) (hφc : HasCompactSupport φ)
    (f : (AutomorphicForm.AdelicGL2 (𝓞 K) K) → ℂ) (hfc : HasCompactSupport f)
    (hOn : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm
      (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
        (Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
        (adelicGLHaar (Fin 2) (𝓞 L) L))
      (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
      f)
    (hregA : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.globalPoints (𝓞 K) K γ₀))
    (P : GL (Fin 2) L)
    (hy : AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ.symm (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) P))
    (e₀ : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) ≃ₜ* (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (he₃ : ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ.symm (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) P) τ
      (@Measure.map _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) e₀.symm τ))
    (B : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ≃ₜ* (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) (hB : ∀ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), ((B t : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) : (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) = TorusBridge.φ K L (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (C₁ : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) ≃ₜ* (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) (hC₁ : ∀ x, ((C₁ x : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) : (AutomorphicForm.AdelicGL2 (𝓞 K) K)) = (x : (AutomorphicForm.AdelicGL2 (𝓞 K) K)))
    (e' : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ≃ₜ* (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) (he'def : e' = B.trans (e₀.trans C₁))
    (τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) [hτi : τ.IsHaarMeasure] (τ' : Measure (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀))) (hτ'def : τ' = τ.map e'.symm)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∃ w : (AutomorphicForm.AdelicGL2 (𝓞 L) L) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0 →
        ∫ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), w ((t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * x) ∂τ' = 1) ∧
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
          (fun g => f (g * AutomorphicForm.centralScalar (𝓞 K) K
            ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z))) I →
        ∫ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) * (w x : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = I := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI hBS : BorelSpace (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  have hcentral : ∀ (u : (AdeleRing (𝓞 K) K)ˣ) (x : (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
      x * AutomorphicForm.centralScalar (𝓞 K) K u = AutomorphicForm.centralScalar (𝓞 K) K u * x :=
    fun u x => AutomorphicForm.SiegelCovering.mul_centralScalar_comm u x
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI hBS₁ : BorelSpace (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) := (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))) := ⟨rfl⟩

  obtain ⟨z', hz'⟩ : ∃ z' : (AdeleRing (𝓞 L) L)ˣ, z' = D.unitsAct σ.symm z := ⟨_, rfl⟩
  have hNz : (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z' =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z := by
    rw [hz']; exact CltB.idelicNorm_unitsAct K L D σ.symm z

  have hγ₁reg : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) :=
    CltAux.isRegularSemisimple_mul_scalar _ hregA
  have hδ'reg := CltB.isRegularSemisimple_normString_of_isNormConjugator K L (AdeleRing (𝓞 K) K) σ.symm _ hγ₁reg _ _ hy

  obtain ⟨τ₁, hτ₁def⟩ : ∃ τ₁ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), τ₁ = τ.map C₁.symm := ⟨_, rfl⟩
  haveI hτ₁ : τ₁.IsHaarMeasure := by rw [hτ₁def]; exact ContinuousMulEquiv.isHaarMeasure_map τ C₁.symm
  obtain ⟨τ'', hτ''def⟩ : ∃ τ'' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ))), τ'' = τ₁.map e₀.symm := ⟨_, rfl⟩
  haveI hτ''h : τ''.IsHaarMeasure := by rw [hτ''def]; exact ContinuousMulEquiv.isHaarMeasure_map τ₁ e₀.symm
  have hcoup : AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ.symm (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) P) τ₁ τ'' := by
    rw [hτ''def]; exact he₃ τ₁

  have hBτ : τ'.map B = τ'' := by
    have m1 : Measurable (e'.symm : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) → (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀))) := (map_continuous e'.symm).measurable
    have m2 : Measurable (B : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) → (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) := (map_continuous B).measurable
    have m3 : Measurable (C₁.symm : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) → (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) := (map_continuous C₁.symm).measurable
    have m4 : Measurable (e₀.symm : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) → (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)))) := (map_continuous e₀.symm).measurable
    rw [hτ''def, hτ₁def, hτ'def, Measure.map_map m2 m1, Measure.map_map m4 m3]
    congr 1
    funext s
    show B (e'.symm s) = e₀.symm (C₁.symm s)
    apply e₀.injective
    apply C₁.injective
    rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
    have : e' (e'.symm s) = s := e'.apply_symm_apply s
    rw [he'def, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply] at this
    rw [← he'def] at this
    exact this

  have hψc : HasCompactSupport ((fun g : (AutomorphicForm.AdelicGL2 (𝓞 L) L) => φ (AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ.symm z) * g)) ∘
      AutomorphicForm.baseChangeGL K L) := by
    have h1 : HasCompactSupport (fun g : (AutomorphicForm.AdelicGL2 (𝓞 L) L) => φ (AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ.symm z) * g)) :=
      hφc.comp_homeomorph (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 L) L (D.unitsAct σ.symm z)))
    have h2 := h1.comp_homeomorph (CltMain.φh K L).symm
    exact h2
  obtain ⟨wt, hwt⟩ := AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
    K L σ.symm (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) hδ'reg τ'' hτ''h _ hψc
  rw [← hBτ] at hwt
  obtain ⟨⟨hw0, hwm, hwc, hsec⟩, hTOI⟩ := CltMain.section_bridge K L D σ δ₀ B hB τ' φ z wt hwt
  rw [hBτ] at hTOI
  refine ⟨fun x => wt (TorusBridge.φ K L x), hw0, hwm, hwc, hsec, ?_⟩
  intro I hI

  have hI₁ : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) τ₁
      (fun g : (AutomorphicForm.AdelicGL2 (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K
        ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z') * g)) I := by
    rw [hτ₁def]
    refine CltB.isOrbitalIntegralOn_transfer K _ _ _ C₁ hC₁ τ _ _ (fun x => ?_) I hI
    beta_reduce
    rw [CltAux.conj_central_rearrange _ _ _ _ (hcentral _) (hcentral _), mul_one, ← map_mul, hNz]

  classical
  let IL : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun w =>
    if w = z' then ∫ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) *
        (wt (TorusBridge.φ K L x) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
    else Classical.choose (CltMain.exists_isTwistedOrbitalIntegralOn K L σ.symm
      (@Measure.map _ _ _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) (TorusBridge.φ K L)
        (adelicGLHaar (Fin 2) (𝓞 L) L)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) hδ'reg τ'' hτ''h
      ((fun g : (AutomorphicForm.AdelicGL2 (𝓞 L) L) => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘ AutomorphicForm.baseChangeGL K L)
      ((hφc.comp_homeomorph (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 L) L w))).comp_homeomorph
        (CltMain.φh K L).symm))
  let IK : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun u =>
    if u = (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z' then I
    else Classical.choose (AutomorphicForm.IsOrbitalIntegralOn.exists_adeleRing_of_isRegularSemisimple K
      (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) hγ₁reg τ₁
      (fun g : (AutomorphicForm.AdelicGL2 (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K u * g))
      (hfc.comp_homeomorph (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 K) K u))))
  have hIL : ∀ w, AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ.symm
      (@Measure.map _ _ _ (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) (TorusBridge.φ K L)
        (adelicGLHaar (Fin 2) (𝓞 L) L)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) τ''
      ((fun g : (AutomorphicForm.AdelicGL2 (𝓞 L) L) => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘ AutomorphicForm.baseChangeGL K L)
      (IL w) := by
    intro w
    by_cases hw : w = z'
    · simp only [IL, if_pos hw]; rw [hw, hz']; exact hTOI
    · simp only [IL, if_neg hw]; exact Classical.choose_spec _
  have hIK : ∀ u, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) τ₁
      (fun g : (AutomorphicForm.AdelicGL2 (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K u * g)) (IK u) := by
    intro u
    by_cases hu : u = (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z'
    · simp only [IK, if_pos hu]; rw [hu]; exact hI₁
    · simp only [IK, if_neg hu]; exact Classical.choose_spec _
  have key := AutomorphicForm.eq_comp_idelicNorm_of_isTwistedOrbitalIntegralOn_centralScalar_mul_of_isOrbitalIntegralOn_centralScalar_mul_of_areMatchingOn
    K L σ.symm hgen _ c₀ φ f hOn (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (1 : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)) hδ'reg (AutomorphicForm.globalPoints (𝓞 K) K γ₀ * AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)) hγ₁reg (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) P) hy τ₁ τ'' hcoup IL hIL IK hIK z'
  simp only [IL, IK, if_pos rfl, if_true] at key
  exact key

end CltMain

open TorusBridge AutomorphicForm NumberField.AdelicLevel in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (RL : Set (GL (Fin 2) L))
    (hRLsub : RL ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ})
    (hRL : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ RL ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h))
    (ΨL : GL (Fin 2) L → Set (AdelicGL2 (𝓞 L) L))
    (hΨLs : ∀ δ₀ ∈ RL, ΨL δ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨL : ∀ δ₀ ∈ RL, IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) (ΨL δ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ.symm : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (RK : Set (GL (Fin 2) K))
    (hRKsub : RK ⊆ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K)
    (hRK : ∀ γ ∈ AutomorphicForm.centralCell K ∪ AutomorphicForm.ellipticCell K, ∃! γ₀ : GL (Fin 2) K,
      γ₀ ∈ RK ∧ ∃ (h : GL (Fin 2) K) (a : Kˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (ΨK : GL (Fin 2) K → Set (AdelicGL2 (𝓞 K) K))
    (hΨKs : ∀ γ₀ ∈ RK, ΨK γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨK : ∀ γ₀ ∈ RK, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K))
      (ΨK γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (c₀ : NNReal) (κ : ℝ) (hκ : 0 < κ)
    (hκl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        ENNReal.ofReal κ *
          ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hκi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
        IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
      ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        κ * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hOn : AutomorphicForm.AreMatchingOn K L (AdeleRing (𝓞 K) K) σ.symm
      (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
        (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
        (Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
        (adelicGLHaar (Fin 2) (𝓞 L) L))
      (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
      f)
    (hvan : ∀ γ₀ ∈ RK, γ₀ ∈ AutomorphicForm.ellipticCell K → ∀ (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      ¬ LT.TwistedNorm.IsNormClass hgen
          (ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) →
      (∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u)) →
      ∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure →
      ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
          (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          τ f I → I = 0)
    (δ₀ : GL (Fin 2) L) (hδ₀ : δ₀ ∈ RL) (γ₀ : GL (Fin 2) K) (hγ₀ : γ₀ ∈ RK)
    (hγ₀e : γ₀ ∈ AutomorphicForm.ellipticCell K) (a : Kˣ)
    (hNcl : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) :
    ∃ (τ' : Measure (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm)
          (AutomorphicForm.globalPoints (𝓞 L) L δ₀)))
      (τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AdelicGL2 (𝓞 K) K)))) (C : ENNReal),
      τ'.IsHaarMeasure ∧ SFinite τ' ∧ τ'.IsMulRightInvariant ∧
      τ.IsHaarMeasure ∧ SFinite τ ∧ τ.IsMulRightInvariant ∧ C ≠ 0 ∧ C ≠ ⊤ ∧

      (∀ Dm : Set (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map
            (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf
            (Subgroup.centralizer {AutomorphicForm.globalPoints (𝓞 K) K γ₀})).op Dm τ →
        ∀ A B : ℝ, 0 < A → A ≤ B →
          τ (Dm ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc A B}) =
            C * ENNReal.ofReal (Real.log (B / A))) ∧

      (∀ Dm' : Set (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm)
          (AutomorphicForm.globalPoints (𝓞 L) L δ₀)),
        IsFundamentalDomain
          (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
            (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf
            (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm)
              (AutomorphicForm.globalPoints (𝓞 L) L δ₀))).op Dm' τ' →
        ∀ A B : ℝ, 0 < A → A ≤ B →
          τ' (Dm' ∩ {t | NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 L) L)) ∈ Set.Icc A B}) =
            C * ENNReal.ofReal (Real.log (B / A) / (Module.finrank K L : ℝ))) ∧

      (∀ z : (AdeleRing (𝓞 L) L)ˣ, ∃ w : AdelicGL2 (𝓞 L) L → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧
        HasCompactSupport w ∧
        (∀ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0 →
          ∫ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm)
          (AutomorphicForm.globalPoints (𝓞 L) L δ₀)),
            w ((t : AdelicGL2 (𝓞 L) L) * x) ∂τ' = 1) ∧
        ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
            (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
            (fun g => f (g * AutomorphicForm.centralScalar (𝓞 K) K
              ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z))) I →
          ∫ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x)) * (w x : ℂ)
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = I) ∧

      (∃ G : (AdeleRing (𝓞 K) K)ˣ → ℂ, Continuous G ∧ HasCompactSupport G ∧
        ∀ u : (AdeleRing (𝓞 K) K)ˣ,
          AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
            (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
            (fun g => f (g * AutomorphicForm.centralScalar (𝓞 K) K u)) (G u)) := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := CltAux2.sigmaCompactSpace_adelicGL2 K
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K

  have hcentral : ∀ (u : (AdeleRing (𝓞 K) K)ˣ) (x : (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
      x * AutomorphicForm.centralScalar (𝓞 K) K u = AutomorphicForm.centralScalar (𝓞 K) K u * x :=
    fun u x => AutomorphicForm.SiegelCovering.mul_centralScalar_comm u x
  have hS₁S : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) = (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := CltAux.centralizer_mul_eq_of_central _ _ (hcentral _)
  obtain ⟨C₁, hC₁⟩ := CltAux.exists_cme_of_eq (G := (AutomorphicForm.AdelicGL2 (𝓞 K) K)) hS₁S
  have hreg : AutomorphicForm.IsRegularSemisimple γ₀ := isRegularSemisimple_of_mem_ellipticCell K γ₀ hγ₀e
  have hregA : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.globalPoints (𝓞 K) K γ₀) := by
    unfold AutomorphicForm.IsRegularSemisimple at hreg ⊢
    have h := hreg.map (algebraMap K (AdeleRing (𝓞 K) K))
    have e : Matrix.trace ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : (AutomorphicForm.AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ^ 2 -
        4 * Matrix.det ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : (AutomorphicForm.AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        algebraMap K (AdeleRing (𝓞 K) K) (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) K) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) K)) := by
      change Matrix.trace ((γ₀ : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (AdeleRing (𝓞 K) K))) ^ 2 -
        4 * Matrix.det ((γ₀ : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (AdeleRing (𝓞 K) K))) = _
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.det_fin_two]
      simp only [Matrix.map_apply, map_sub, map_mul, map_pow, map_add, map_ofNat]
    rw [e]; exact h
  have hScomm : ∀ a b : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), a * b = b * a := fun a b =>
    Subtype.ext (AutomorphicForm.IsRegularSemisimple.mul_comm_of_mem_centralizer _ _ hregA _ _ a.2 b.2)

  haveI : LocallyCompactSpace (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := (Set.isClosed_centralizer _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := (Set.isClosed_centralizer _).sigmaCompactSpace
  haveI hBS : BorelSpace (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), τ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have hτr : τ.IsMulRightInvariant := CltAux.isMulRightInvariant_of_comm τ hScomm
  haveI : SigmaFinite τ := Measure.IsHaarMeasure.sigmaFinite τ
  have hτsf : SFinite τ := inferInstance
  obtain ⟨Cc, hCc0, hCctop, hcov⟩ := CltAux2.cov_of_eq K γ₀ hγ₀e 1 (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) (by rw [map_one, mul_one]) τ

  obtain ⟨P, hP⟩ := CltMain.isNormRep_of_normClassMap_eq K L σ hgen γ₀ a δ₀ hNcl
  have hy := CltMain.isNormConjugator_includeLeft K L σ γ₀ a δ₀ P hP
  obtain ⟨e₀, he₁, he₂, he₃⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep K L σ.symm hgen γ₀
      hreg a 1 δ₀ 1 ⟨P, hP⟩ (CltMain.normString_scalar_one K L σ) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) P) hy
  obtain ⟨B, hB⟩ := CltMain.exists_bridge K L D σ δ₀
  obtain ⟨e', he'def⟩ : ∃ e' : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ≃ₜ* (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), e' = B.trans (e₀.trans C₁) := ⟨_, rfl⟩
  have he' : ∀ t, ((e' t : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) : (AutomorphicForm.AdelicGL2 (𝓞 K) K)) = ((e₀ (B t) : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) * 1)} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) : (AutomorphicForm.AdelicGL2 (𝓞 K) K)) := fun t => by
    rw [he'def, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply, hC₁]
  have hrat : ∀ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), (e' t : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) ∈ ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) ↔ t ∈ ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) := by
    intro t
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, he', he₂ (B t), hB, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      apply (TorusBridge.φ K L).injective
      rw [φ_globalPoints K L D]; exact hxe
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hxe, φ_globalPoints K L D]
  have hnorm : ∀ t : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L))) =
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det ((e' t : (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) : (AutomorphicForm.AdelicGL2 (𝓞 K) K))) ^ Module.finrank K L := by
    intro t
    refine CltMain.ideleNorm_det_eq_pow K L D _ (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) P) ?_
    rw [he', he₁ (B t), hB]

  obtain ⟨τ', hτ'def⟩ : ∃ τ' : Measure (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), τ' = τ.map e'.symm := ⟨_, rfl⟩
  have hτ' : τ'.IsHaarMeasure := by rw [hτ'def]; exact ContinuousMulEquiv.isHaarMeasure_map τ e'.symm
  have hT'comm : ∀ a b : (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀)), a * b = b * a :=
    CltAux.comm_of_injective (fun t => e' t) e'.injective (fun a b => map_mul e' a b) hScomm
  haveI := hτ'
  have hτ'r : τ'.IsMulRightInvariant := CltAux.isMulRightInvariant_of_comm τ' hT'comm
  have hτ'sf : SFinite τ' := by rw [hτ'def]; infer_instance

  have hcov' := CltMain.cov_transfer e' (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf (AutomorphicForm.sigmaCentralizer (AutomorphicForm.sigmaAdelicAct K L D σ.symm) (AutomorphicForm.globalPoints (𝓞 L) L δ₀))) (((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) hrat
    (fun t => NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (t : (AutomorphicForm.AdelicGL2 (𝓞 L) L))))
    (fun s => NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (s : (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (Module.finrank K L) Module.finrank_pos.ne' (fun s => NumberField.TateGlobal.ideleNorm_pos _) hnorm τ Cc hcov
  rw [← hτ'def] at hcov'
  refine ⟨τ', τ, Cc, hτ', hτ'sf, hτ'r, hτ, hτsf, hτr, hCc0, hCctop, hcov, ?_, ?_, ?_⟩
  · intro Dm' hDm' A B hA hAB
    exact hcov' Dm' hDm' A B hA hAB
  ·
    intro z
    haveI := hτ
    exact CltMain.clause_b K L D σ hgen γ₀ a δ₀ c₀ φ hφc f hfc hOn hregA P hy e₀ he₃ B hB C₁ hC₁ e' he'def τ τ' hτ'def z
  · haveI := hτ
    obtain ⟨G, hG, hGc, hGI⟩ :=
      AutomorphicForm.exists_continuous_hasCompactSupport_forall_isOrbitalIntegralOn_mul_centralScalar_of_mem_ellipticCell
        K γ₀ hγ₀e τ c₀ f hf hfc
    exact ⟨G, hG, hGc, hGI⟩

end S_AutomorphicForm_exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn
end P2MW
export P2MW.S_AutomorphicForm_exists_haar_sigmaCentralizer_centralizer_covolume_and_twistedOrbital_eq_of_normClassMap_eq_of_areMatchingOn (solution)
