-- Prove2me | solution 1 for ArtinL.codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f978bafc-c497-5c17-9832-e366f078a0bb

import Mathlib
import Definitions.Def_ArtinL_Conductor
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
import Theorems.Thm_ValuationSubring_exists_heightOneSpectrum_asIdeal_eq_and_eq_valuationSubring_of_forall_mem_iff_valuation_lt_one
import Theorems.Thm_ValuationSubring_map_restrictNormalHom_decompositionSubgroup_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring
import Theorems.Thm_Ideal_inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
import Definitions.Def_Deformations_MatrixRepresentation
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom
p2m_attr_erase "instance" "FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

open scoped MatrixGroups Pointwise
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open IsDedekindDomain

namespace DictBody

section P
variable {K : Type*} [Field K] (val : Valuation K (WithZero (Multiplicative ℤ)))

theorem le_exp_neg_one_of_lt_one {t : WithZero (Multiplicative ℤ)} (ht : t < 1) :
    t ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨z, rfl⟩ : ∃ z : ℤ, t = WithZero.exp z := ⟨WithZero.log t, (WithZero.exp_log h0).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
    rw [WithZero.exp_le_exp]
    omega

theorem integers_valuationSubring : val.Integers val.valuationSubring where
  hom_inj := Subtype.val_injective
  map_le_one x := x.2
  exists_of_le_one r hr := ⟨⟨r, hr⟩, rfl⟩

theorem mem_maximalIdeal_iff' (x : val.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal val.valuationSubring ↔ val (x : K) < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring val).lt_one_iff_lt_one).symm

theorem mem_maximalIdeal_pow_iff_of_uniformizer {π : K} (hπ : val π = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (x : val.valuationSubring) :
    x ∈ IsLocalRing.maximalIdeal val.valuationSubring ^ n ↔ val (x : K) ≤ WithZero.exp (-(n : ℤ)) := by
  have hπA : π ∈ val.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  set ϖ : val.valuationSubring := ⟨π, hπA⟩ with hϖ
  have hint := integers_valuationSubring val
  have hmax : IsLocalRing.maximalIdeal val.valuationSubring = Ideal.span {ϖ} := by
    apply le_antisymm
    · intro x hx
      rw [mem_maximalIdeal_iff'] at hx
      rw [Ideal.mem_span_singleton, ← hint.le_iff_dvd]
      change val (x : K) ≤ val π
      rw [hπ]
      exact le_exp_neg_one_of_lt_one hx
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_iff']
      change val π < 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hint.le_iff_dvd]
  change val (x : K) ≤ val ((ϖ ^ n : val.valuationSubring) : K) ↔ _
  have : val ((ϖ ^ n : val.valuationSubring) : K) = WithZero.exp (-(n : ℤ)) := by
    rw [SubmonoidClass.coe_pow]
    change val (π ^ n) = _
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  rw [this]

end P

theorem mem_pow_valuationSubring_iff {F : Type*} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (n : ℕ) (x : ↥((w.valuation F).valuationSubring)) :
    x ∈ IsLocalRing.maximalIdeal ↥((w.valuation F).valuationSubring) ^ n ↔
      w.valuation F (x : F) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  exact mem_maximalIdeal_pow_iff_of_uniformizer (w.valuation F) hπ n x

end DictBody
namespace LevelBody

section L3
variable {n : ℕ} {G : Type} [Group G]

theorem finrank_invariants_eq_inv_card_mul_sum_trace (θ : G →* GL (Fin n) ℂ) (S : Subgroup G) [Fintype ↥S] :
    (Module.finrank ℂ (Representation.invariants ((Deformation.matrixRepresentation θ).comp S.subtype)) : ℂ) =
      (Fintype.card ↥S : ℂ)⁻¹ * ∑ s : ↥S, ((θ (s : G) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := by
  classical
  set π := Deformation.matrixRepresentation θ with hπ
  have h1 : ∀ v ∈ Representation.invariants (π.comp S.subtype), π 1 v ∈ Representation.invariants (π.comp S.subtype) := by
    intro v hv; rw [map_one]; exact hv
  have key := ArtinL.trace_restrict_invariants_eq_inv_card_mul_sum_trace π S 1 h1
  have hid : (π 1).restrict h1 = LinearMap.id := by
    ext v
    simp only [LinearMap.restrict_coe_apply, map_one, LinearMap.id_coe, id_eq]
    rfl
  rw [hid, LinearMap.trace_id] at key
  rw [key]
  refine congrArg _ (Finset.sum_congr rfl (fun s _ => ?_))
  rw [one_mul, hπ, Deformation.matrixRepresentation_apply]
  change LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLin' ((θ (s : G) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) = _
  exact Matrix.trace_toLin'_eq _

end L3

end LevelBody

namespace LevelBody

section KA
variable {n : ℕ}
local notation "ℚbar" => AlgebraicClosure ℚ
local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable (ρ : Γℚ →* GL (Fin n) ℂ)

theorem halg : (DivisionRing.toRatAlgebra : Algebra ℚ (ArtinL.splittingField ρ)) = (ArtinL.splittingField ρ).algebra :=
  Subsingleton.elim _ _

theorem normal_splittingField' : @Normal ℚ (ArtinL.splittingField ρ) _ _ (ArtinL.splittingField ρ).algebra :=
  IntermediateField.normal_iff_forall_map_le'.2 (fun σ x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ArtinL.apply_mem_splittingField ρ σ hy)

scoped instance normal_splittingField : Normal ℚ (ArtinL.splittingField ρ) := by
  have h := normal_splittingField' ρ
  rwa [← halg] at h

theorem galoisFactors_of_comp (F : IntermediateField ℚ ℚbar) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F)) :
    GaloisFactorsThroughFiniteLevel ρ := by
  refine ⟨F, inferInstance, fun σ hσ => ?_⟩
  rw [hρ, MonoidHom.comp_apply]
  have : AlgEquiv.restrictNormalHom F σ = 1 := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change algebraMap F ℚbar (σ.restrictNormal F x) = algebraMap F ℚbar x
    rw [AlgEquiv.restrictNormal_commutes]
    exact hσ x x.2
  rw [this, map_one]

theorem smul_eq_of_mem_ker {σ : Γℚ} (hσ : σ ∈ ρ.ker) (x : ArtinL.splittingField ρ) : σ • x = x := by
  apply Subtype.ext
  rw [ArtinL.coe_smul_splittingField]
  exact (IntermediateField.mem_fixedField_iff ρ.ker (x : ℚbar)).1 x.2 σ hσ

theorem isOpen_ker (hρ : GaloisFactorsThroughFiniteLevel ρ) : IsOpen (ρ.ker : Set Γℚ) := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen L)
  intro σ hσ
  rw [MonoidHom.mem_ker]
  exact hker σ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx)

theorem isClosed_ker (hρ : GaloisFactorsThroughFiniteLevel ρ) : IsClosed (ρ.ker : Set Γℚ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_ker ρ hρ)

theorem mem_ker_of_forall_smul_eq (hρ : GaloisFactorsThroughFiniteLevel ρ) {σ : Γℚ}
    (h : ∀ x : ArtinL.splittingField ρ, σ • x = x) : σ ∈ ρ.ker := by
  have hfix : σ ∈ (IntermediateField.fixedField (F := ℚ) (E := ℚbar) ρ.ker).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have := congrArg (fun y : ArtinL.splittingField ρ => (y : ℚbar)) (h ⟨x, hx⟩)
    simpa using this
  have key := InfiniteGalois.fixingSubgroup_fixedField (⟨ρ.ker, isClosed_ker ρ hρ⟩ : ClosedSubgroup Γℚ)
  change (IntermediateField.fixedField ρ.ker).fixingSubgroup = ρ.ker at key
  rwa [key] at hfix

theorem finiteDimensional_splittingField (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    FiniteDimensional ℚ (ArtinL.splittingField ρ) := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  have hle : ArtinL.splittingField ρ ≤ L := by
    have h1 : L.fixingSubgroup ≤ ρ.ker := fun σ hσ =>
      (MonoidHom.mem_ker).2 (hker σ fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx)
    have h2 := IntermediateField.fixedField_antitone (F := ℚ) (E := ℚbar) h1
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at h2
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

theorem numberField_splittingField (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    NumberField (ArtinL.splittingField ρ) := by
  have hfd := finiteDimensional_splittingField ρ hρ
  haveI hFD : @FiniteDimensional ℚ (ArtinL.splittingField ρ) _ _ DivisionRing.toRatAlgebra.toModule := by
    rw [halg]; exact hfd
  exact @NumberField.mk _ _ inferInstance hFD

theorem restrictNormalHom_eq_one_iff (hρ : GaloisFactorsThroughFiniteLevel ρ) (σ : Γℚ) :
    AlgEquiv.restrictNormalHom (ArtinL.splittingField ρ) σ = 1 ↔ ρ σ = 1 := by
  constructor
  · intro h
    apply (MonoidHom.mem_ker).1 (mem_ker_of_forall_smul_eq ρ hρ (fun x => ?_))
    apply Subtype.ext
    rw [ArtinL.coe_smul_splittingField]
    have h1 := AlgEquiv.restrictNormal_commutes σ (ArtinL.splittingField ρ) x
    have h2 : σ.restrictNormal (ArtinL.splittingField ρ) = 1 := h
    rw [h2, AlgEquiv.one_apply] at h1
    exact h1.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change algebraMap _ ℚbar (σ.restrictNormal (ArtinL.splittingField ρ) x) = algebraMap _ ℚbar x
    rw [AlgEquiv.restrictNormal_commutes]
    exact congrArg Subtype.val (smul_eq_of_mem_ker ρ ((MonoidHom.mem_ker).2 h) x)

theorem restrictNormalHom_surjective' :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚbar) (ArtinL.splittingField ρ)) :=
  AlgEquiv.restrictNormalHom_surjective ℚbar

noncomputable def rhoK (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    (ArtinL.splittingField ρ ≃ₐ[ℚ] ArtinL.splittingField ρ) →* GL (Fin n) ℂ where
  toFun τ := ρ (Function.surjInv (restrictNormalHom_surjective' ρ) τ)
  map_one' := by
    rw [← restrictNormalHom_eq_one_iff ρ hρ]
    exact Function.surjInv_eq (restrictNormalHom_surjective' ρ) 1
  map_mul' τ₁ τ₂ := by
    set s := Function.surjInv (restrictNormalHom_surjective' ρ) with hs
    have hsτ : ∀ τ, AlgEquiv.restrictNormalHom (ArtinL.splittingField ρ) (s τ) = τ :=
      Function.surjInv_eq (restrictNormalHom_surjective' ρ)
    have hker : ρ ((s τ₁ * s τ₂)⁻¹ * s (τ₁ * τ₂)) = 1 := by
      rw [← restrictNormalHom_eq_one_iff ρ hρ, map_mul, map_inv, map_mul, hsτ, hsτ, hsτ, inv_mul_cancel]
    rw [map_mul, map_inv, inv_mul_eq_one] at hker
    show ρ (s (τ₁ * τ₂)) = ρ (s τ₁) * ρ (s τ₂)
    rw [← hker, map_mul]

theorem rhoK_restrictNormalHom (hρ : GaloisFactorsThroughFiniteLevel ρ) (σ : Γℚ) :
    rhoK ρ hρ (AlgEquiv.restrictNormalHom (ArtinL.splittingField ρ) σ) = ρ σ := by
  show ρ (Function.surjInv (restrictNormalHom_surjective' ρ) _) = ρ σ
  set s := Function.surjInv (restrictNormalHom_surjective' ρ) with hs
  have hsτ : ∀ τ, AlgEquiv.restrictNormalHom (ArtinL.splittingField ρ) (s τ) = τ :=
    Function.surjInv_eq (restrictNormalHom_surjective' ρ)
  have : ρ ((s (AlgEquiv.restrictNormalHom (ArtinL.splittingField ρ) σ))⁻¹ * σ) = 1 := by
    rw [← restrictNormalHom_eq_one_iff ρ hρ, map_mul, map_inv, hsτ, inv_mul_cancel]
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem rhoK_comp (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    (rhoK ρ hρ).comp (AlgEquiv.restrictNormalHom (ArtinL.splittingField ρ)) = ρ :=
  MonoidHom.ext (rhoK_restrictNormalHom ρ hρ)

theorem rhoK_injective (hρ : GaloisFactorsThroughFiniteLevel ρ) : Function.Injective (rhoK ρ hρ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro τ hτ
  rw [MonoidHom.mem_ker] at hτ
  obtain ⟨σ, rfl⟩ := restrictNormalHom_surjective' ρ τ
  rw [rhoK_restrictNormalHom] at hτ
  rw [Subgroup.mem_bot, restrictNormalHom_eq_one_iff ρ hρ]
  exact hτ

end KA

end LevelBody
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

namespace LevelBody

section KB
variable {n : ℕ}
local notation "ℚbar" => AlgebraicClosure ℚ
local instance isAlgebraicQbar' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar' : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar' : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)

local notation "K" => ArtinL.splittingField ρ
local notation "res" => AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (ArtinL.splittingField ρ)

include hρ in
theorem map_rho_eq (X : Subgroup Γℚ) : X.map ρ = (X.map res).map (rhoK ρ hρ) := by
  rw [Subgroup.map_map, rhoK_comp]

include hρ in
theorem natCard_map_rho_eq (X : Subgroup Γℚ) : Nat.card (X.map ρ) = Nat.card (X.map res) := by
  rw [map_rho_eq ρ hρ X]
  exact (Nat.card_congr ((X.map res).equivMapOfInjective _ (rhoK_injective ρ hρ)).toEquiv).symm

include hρ in
theorem invariantsUnder_eq (X : Subgroup Γℚ) :
    ArtinL.invariantsUnder ρ X =
      Representation.invariants ((Deformation.matrixRepresentation (rhoK ρ hρ)).comp (X.map res).subtype) := by
  ext v
  rw [ArtinL.invariantsUnder, Representation.mem_invariants, Representation.mem_invariants]
  constructor
  · rintro h ⟨τ, hτ⟩
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
    have := h ⟨σ, hσ⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, Deformation.matrixRepresentation_apply] at this ⊢
    rw [rhoK_restrictNormalHom]
    exact this
  · rintro h ⟨σ, hσ⟩
    have := h ⟨res σ, Subgroup.mem_map_of_mem _ hσ⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, Deformation.matrixRepresentation_apply] at this ⊢
    rw [rhoK_restrictNormalHom] at this
    exact this

include hρ in

theorem codimInvariants_eq (X : Subgroup Γℚ) [Fintype ↥(X.map res)] :
    ((ArtinL.codimInvariants ρ X : ℕ) : ℂ) =
      (n : ℂ) - (Fintype.card ↥(X.map res) : ℂ)⁻¹ *
        ∑ τ : ↥(X.map res), (((rhoK ρ hρ) (τ : K ≃ₐ[ℚ] K) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := by
  rw [← finrank_invariants_eq_inv_card_mul_sum_trace (rhoK ρ hρ) (X.map res), ← invariantsUnder_eq ρ hρ X,
    ArtinL.codimInvariants]
  have hle : Module.finrank ℂ (ArtinL.invariantsUnder ρ X) ≤ n := by
    have := Submodule.finrank_le (ArtinL.invariantsUnder ρ X)
    rwa [Module.finrank_fin_fun] at this
  rw [Nat.cast_sub hle]

end KB
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

end LevelBody
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

namespace LevelBody

section KC
variable {n : ℕ}
local notation "ℚbar" => AlgebraicClosure ℚ
local instance isAlgebraicQbar'' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar'' : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar'' : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable (ρ : Γℚ →* GL (Fin n) ℂ)

local notation "K" => ArtinL.splittingField ρ
local notation "res" => AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (ArtinL.splittingField ρ)

theorem mem_nonunits_placeUnder_iff (A : ValuationSubring ℚbar) (x : K) :
    x ∈ (ArtinL.placeUnder ρ A).nonunits ↔ (x : ℚbar) ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ArtinL.mem_placeUnder_iff]
  simp

theorem mem_maximalIdeal_pow_iff_of_eq {L : Type*} [Field L] {S₁ S₂ : ValuationSubring L} (h : S₁ = S₂)
    (m : ℕ) (x : L) (hx : x ∈ S₁) :
    (⟨x, hx⟩ : S₁) ∈ IsLocalRing.maximalIdeal S₁ ^ m ↔ (⟨x, h ▸ hx⟩ : S₂) ∈ IsLocalRing.maximalIdeal S₂ ^ m := by
  subst h; rfl

theorem coe_smul_placeUnder (A : ValuationSubring ℚbar) (σ : ↥(A.decompositionSubgroup ℚ)) (x : ArtinL.placeUnder ρ A) :
    ((σ • x : ArtinL.placeUnder ρ A) : K) = res (σ : Γℚ) (x : K) := by
  apply Subtype.ext
  rw [ArtinL.coe_coe_smul_placeUnder]
  exact (AlgEquiv.restrictNormal_commutes (σ : Γℚ) K (x : K)).symm

theorem exists_place_data (hρ : GaloisFactorsThroughFiniteLevel ρ) {p : ℕ} (hp : p.Prime)
    (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p) :
    haveI := numberField_splittingField ρ hρ
    ∃ (Q : Ideal (𝓞 K)) (_ : Q.IsMaximal), (p : 𝓞 K) ∈ Q ∧
      (A.inertiaSubgroupIn ℚ).map res = Q.inertia (K ≃ₐ[ℚ] K) ∧
      ∀ i : ℕ, (ArtinL.ramificationGroup ρ A i).map res = (Q ^ (i + 1)).inertia (K ≃ₐ[ℚ] K) := by
  haveI := numberField_splittingField ρ hρ
  haveI := normal_splittingField ρ
  haveI : IsGalois ℚ K := ⟨⟩
  classical
  obtain ⟨Q, hQmax, -, hpQ, hval, hQv, hIQ, -, -⟩ :=
    ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom K A hp hA
  haveI := hQmax
  refine ⟨Q, hQmax, hpQ, hIQ, ?_⟩

  have hA1 : ∀ x : 𝓞 K, (ArtinL.placeUnder ρ A).valuation (algebraMap (𝓞 K) K x) ≤ 1 := by
    intro x
    rw [ValuationSubring.valuation_le_one_iff, ArtinL.mem_placeUnder_iff, ← ValuationSubring.valuation_le_one_iff]
    exact hval x
  have hA2 : ∀ x : 𝓞 K, x ∈ Q ↔ (ArtinL.placeUnder ρ A).valuation (algebraMap (𝓞 K) K x) < 1 := by
    intro x
    rw [hQv x, ← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff, mem_nonunits_placeUnder_iff]
    rfl
  obtain ⟨w, hwQ, hAK⟩ :=
    ValuationSubring.exists_heightOneSpectrum_asIdeal_eq_and_eq_valuationSubring_of_forall_mem_iff_valuation_lt_one
      K (ArtinL.placeUnder ρ A) Q hA1 hA2

  have hmem : ∀ x : 𝓞 K, (algebraMap (𝓞 K) K x) ∈ ArtinL.placeUnder ρ A := fun x =>
    (ValuationSubring.valuation_le_one_iff _ _).1 (hA1 x)
  let f : 𝓞 K →+* ↥(ArtinL.placeUnder ρ A) :=
    { toFun := fun x => ⟨algebraMap (𝓞 K) K x, hmem x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hfval : ∀ x : 𝓞 K, ((f x : ↥(ArtinL.placeUnder ρ A)) : K) = algebraMap (𝓞 K) K x := fun x => rfl
  let j : ↥(A.decompositionSubgroup ℚ) →* (K ≃ₐ[ℚ] K) := (res).comp (A.decompositionSubgroup ℚ).subtype
  have h543 := @ValuationSubring.map_restrictNormalHom_decompositionSubgroup_eq ℚ ℚbar _ _ _ _ K (normal_splittingField' ρ) A
  have hjrange : j.range = (ArtinL.placeUnder ρ A).decompositionSubgroup ℚ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h543

  have hj : ∀ σ : K ≃ₐ[ℚ] K, (∀ x ∈ Q, σ • x ∈ Q) → σ ∈ j.range := by
    intro σ hσ
    rw [hjrange, hAK, ← IsDedekindDomain.HeightOneSpectrum.stabilizer_asIdeal_eq_decompositionSubgroup_valuationSubring ℚ K w,
      MulAction.mem_stabilizer_iff, hwQ]
    have hle : σ • Q ≤ Q := by
      rw [Ideal.pointwise_smul_def, Ideal.map_le_iff_le_comap]
      intro x hx
      exact hσ x hx
    have hprime : (σ • Q).IsPrime := hQmax.isPrime.smul σ
    have hQ0 : Q ≠ ⊥ := by rw [← hwQ]; exact w.ne_bot
    have hne : σ • Q ≠ ⊥ := by
      intro h
      apply hQ0
      have h2 : σ⁻¹ • (σ • Q) = Q := inv_smul_smul σ Q
      rw [h] at h2
      rw [← h2, Ideal.pointwise_smul_def, Ideal.map_bot]
    exact (hprime.isMaximal hne).eq_of_le hQmax.ne_top hle

  have hf : ∀ (γ : ↥(A.decompositionSubgroup ℚ)) (x : 𝓞 K), f (j γ • x) = γ • f x := by
    intro γ x
    apply Subtype.ext
    rw [coe_smul_placeUnder, hfval, hfval]
    rfl

  have hcomap : ∀ m : ℕ, (IsLocalRing.maximalIdeal ↥(ArtinL.placeUnder ρ A) ^ m).comap f = Q ^ m := by
    intro m
    ext x
    rw [Ideal.mem_comap, show f x = ⟨algebraMap (𝓞 K) K x, hmem x⟩ from rfl,
      mem_maximalIdeal_pow_iff_of_eq hAK m, DictBody.mem_pow_valuationSubring_iff, ← hwQ,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]

  have hdense : ∀ (m : ℕ) (y : ↥(ArtinL.placeUnder ρ A)), ∃ x : 𝓞 K, y - f x ∈ IsLocalRing.maximalIdeal ↥(ArtinL.placeUnder ρ A) ^ m := by
    intro m y
    have hy : (y : K) ∈ (w.valuation K).valuationSubring := hAK ▸ y.2
    obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer (R := 𝓞 K) (v := w)
      ((Valuation.mem_valuationSubring_iff _ _).1 hy) (Units.mk0 (WithZero.exp (-(m : ℤ))) WithZero.coe_ne_zero)
    refine ⟨a, ?_⟩
    have hsub : ((y - f a : ↥(ArtinL.placeUnder ρ A)) : K) ∈ ArtinL.placeUnder ρ A := (y - f a).2
    rw [show y - f a = ⟨((y : K) - algebraMap (𝓞 K) K a), hsub⟩ from Subtype.ext rfl,
      mem_maximalIdeal_pow_iff_of_eq hAK m, DictBody.mem_pow_valuationSubring_iff]
    rw [Units.val_mk0] at ha
    change w.valuation K ((y : K) - algebraMap (𝓞 K) K a) ≤ _
    rw [Valuation.map_sub_swap]
    exact ha.le

  have hdict : ∀ i : ℕ, (Q ^ (i + 1)).inertia (K ≃ₐ[ℚ] K) =
      (IsLocalRing.lowerRamificationGroup ↥(ArtinL.placeUnder ρ A) ↥(A.decompositionSubgroup ℚ) i).map j := fun i =>
    Ideal.inertia_pow_succ_eq_map_lowerRamificationGroup_of_dense (G := K ≃ₐ[ℚ] K) Q j hj f hf hcomap hdense i

  intro i
  apply le_antisymm
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [hdict]
    obtain ⟨-, hσ2⟩ := hσ
    obtain ⟨δ, hδ, hδσ⟩ := Subgroup.mem_map.mp hσ2
    exact ⟨δ, hδ, by rw [← hδσ]; rfl⟩
  · intro τ hτ

    have hτ0 : τ ∈ Q.inertia (K ≃ₐ[ℚ] K) := by
      have hanti : (Q ^ (i + 1)).inertia (K ≃ₐ[ℚ] K) ≤ (Q ^ 1).inertia (K ≃ₐ[ℚ] K) := fun σ hσ x =>
        Ideal.pow_le_pow_right (by omega) (hσ x)
      rw [pow_one] at hanti
      exact hanti hτ
    rw [← hIQ] at hτ0
    obtain ⟨σ₁, hσ₁I, hσ₁τ⟩ := Subgroup.mem_map.mp hτ0

    rw [hdict] at hτ
    obtain ⟨δ, hδ, hδτ⟩ := Subgroup.mem_map.mp hτ
    have hσ₁D : σ₁ ∈ A.decompositionSubgroup ℚ := by
      obtain ⟨ι, -, rfl⟩ := Subgroup.mem_map.mp hσ₁I
      exact ι.2
    refine ⟨σ₁, ⟨hσ₁I, ?_⟩, hσ₁τ⟩
    refine Subgroup.mem_map.mpr ⟨⟨σ₁, hσ₁D⟩, ?_, rfl⟩

    have hres : res σ₁ = res (δ : Γℚ) := by rw [hσ₁τ, ← hδτ]; rfl
    intro x
    have hact : (⟨σ₁, hσ₁D⟩ : ↥(A.decompositionSubgroup ℚ)) • x = δ • x := by
      apply Subtype.ext
      rw [coe_smul_placeUnder, coe_smul_placeUnder]
      exact congrArg (fun e : K ≃ₐ[ℚ] K => e (x : K)) hres
    rw [hact]
    exact hδ x

end KC
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

end LevelBody
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

namespace LevelBody

theorem exists_eq_bot_of_antitone_of_iInf_eq_bot {G : Type*} [Group G] [Finite G] (f : ℕ → Subgroup G) (hf : Antitone f)
    (h : ⨅ i, f i = ⊥) : ∃ N, f N = ⊥ := by
  classical
  haveI : Finite (Subgroup G) := inferInstance
  obtain ⟨s, hs⟩ := (Set.toFinite (Set.range f)).exists_finset_coe
  have hidx : ∀ K ∈ s, ∃ n, f n = K := fun K hK => by
    have : K ∈ Set.range f := by rw [← hs]; exact hK
    exact this
  choose! idx hidx' using hidx
  refine ⟨s.sup idx, le_bot_iff.mp ?_⟩
  rw [← h]
  refine le_iInf fun m => ?_
  have hm : f m ∈ s := by rw [← Finset.mem_coe, hs]; exact ⟨m, rfl⟩
  rw [← hidx' (f m) hm]
  exact hf (Finset.le_sup hm)

section Fin
variable (F : Type*) [Field F] [NumberField F]

theorem eq_one_of_forall_smul_ringOfIntegers_eq (σ : F ≃ₐ[ℚ] F) (h : ∀ x : 𝓞 F, σ • x = x) : σ = 1 := by
  apply AlgEquiv.ext
  intro m
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) m
  have ha : σ (a : F) = a := congrArg (fun y : 𝓞 F => (y : F)) (h a)
  have hb' : σ (b : F) = b := congrArg (fun y : 𝓞 F => (y : F)) (h b)
  rw [map_div₀, ha, hb']
  rfl

theorem exists_inertia_pow_eq_bot (𝔓 : Ideal (𝓞 F)) [h𝔓 : 𝔓.IsMaximal] :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → (𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  classical
  set c : ℕ → Subgroup (F ≃ₐ[ℚ] F) := fun j => (𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F) with hc
  have hanti : Antitone c := by
    intro a b hab σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have hinf : ⨅ j, c j = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_iInf] at hσ
    rw [Subgroup.mem_bot]
    apply eq_one_of_forall_smul_ringOfIntegers_eq F σ
    intro x
    have hx : σ • x - x ∈ ⨅ j : ℕ, 𝔓 ^ j := by
      rw [Ideal.mem_iInf]
      intro j
      rcases j with _ | j
      · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
      · exact hσ j x
    rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔓 h𝔓.ne_top] at hx
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hx)
  obtain ⟨J, hJ⟩ := exists_eq_bot_of_antitone_of_iInf_eq_bot c hanti hinf
  exact ⟨J, fun j hj => le_bot_iff.mp (hJ ▸ hanti hj)⟩

end Fin
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

section KD
variable {n : ℕ}
local notation "ℚbar" => AlgebraicClosure ℚ
local instance isAlgebraicQbar3 : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar3 : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar3 : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable (ρ : Γℚ →* GL (Fin n) ℂ)

local notation "K" => ArtinL.splittingField ρ
local notation "res" => AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) (ArtinL.splittingField ρ)

open scoped Classical in

theorem kbridge (hρ : GaloisFactorsThroughFiniteLevel ρ) {p : ℕ} (hp : p.Prime)
    (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p) :
    haveI := numberField_splittingField ρ hρ
    ∃ (Q : Ideal (𝓞 K)) (_ : Q.IsMaximal), (p : 𝓞 K) ∈ Q ∧
      (((ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) : ℚ) + ArtinL.swanConductor ρ A : ℚ) : ℂ) =
        ∑ᶠ j : ℕ, ((Nat.card ((Q ^ (j + 1)).inertia (K ≃ₐ[ℚ] K)) : ℂ) /
            (Nat.card ((Q ^ 1).inertia (K ≃ₐ[ℚ] K)) : ℂ)) *
          ((n : ℂ) - ((Nat.card ((Q ^ (j + 1)).inertia (K ≃ₐ[ℚ] K)) : ℂ))⁻¹ *
            ∑ g : ↥((Q ^ (j + 1)).inertia (K ≃ₐ[ℚ] K)),
              (((rhoK ρ hρ) (g : K ≃ₐ[ℚ] K) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) := by
  haveI := numberField_splittingField ρ hρ
  obtain ⟨Q, hQmax, hpQ, hI, hR⟩ := exists_place_data ρ hρ hp A hA
  haveI := hQmax
  refine ⟨Q, hQmax, hpQ, ?_⟩

  set E : Subgroup (K ≃ₐ[ℚ] K) → ℂ := fun S => (n : ℂ) - ((Nat.card S : ℕ) : ℂ)⁻¹ *
      ∑ g : ↥S, (((rhoK ρ hρ) (g : K ≃ₐ[ℚ] K) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace with hE
  set G : ℕ → Subgroup (K ≃ₐ[ℚ] K) := fun j => (Q ^ (j + 1)).inertia (K ≃ₐ[ℚ] K) with hG
  have hEcongr : ∀ S T : Subgroup (K ≃ₐ[ℚ] K), S = T → E S = E T := by rintro S T rfl; rfl

  have hcod : ∀ X : Subgroup Γℚ, ((ArtinL.codimInvariants ρ X : ℕ) : ℂ) = E (X.map res) := by
    intro X
    rw [codimInvariants_eq ρ hρ X]
    simp only [hE]
    rw [Nat.card_eq_fintype_card]
  have hEbot : E ⊥ = 0 := by
    have h0 : ArtinL.codimInvariants ρ ⊥ = 0 := by
      unfold ArtinL.codimInvariants
      have htop : ArtinL.invariantsUnder ρ ⊥ = ⊤ := by
        rw [eq_top_iff]
        intro v _
        rw [ArtinL.invariantsUnder, Representation.mem_invariants]
        intro g
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, (Subgroup.mem_bot).mp g.2, map_one]
        rfl
      rw [htop, finrank_top, Module.finrank_fin_fun, Nat.sub_self]
    have h := hcod ⊥
    rw [Subgroup.map_bot, h0, Nat.cast_zero] at h
    exact h.symm
  have hcard : ∀ X : Subgroup Γℚ, (Nat.card (X.map ρ) : ℂ) = Nat.card (X.map res) := fun X => by
    rw [natCard_map_rho_eq ρ hρ X]
  have hI' : (A.inertiaSubgroupIn ℚ).map res = G 0 := by
    simp only [hG]; rw [zero_add, pow_one]; exact hI
  have hR' : ∀ i, (ArtinL.ramificationGroup ρ A i).map res = G i := hR

  obtain ⟨J, hJ⟩ := exists_inertia_pow_eq_bot K Q
  have hGJ : ∀ j, J ≤ j → G j = ⊥ := hJ
  have hcod0 : ∀ j, J ≤ j → ArtinL.codimInvariants ρ (ArtinL.ramificationGroup ρ A j) = 0 := by
    intro j hj
    have h := hcod (ArtinL.ramificationGroup ρ A j)
    rw [hR' j, hGJ j hj, hEbot, Nat.cast_eq_zero] at h
    exact h
  have hG0 : (Nat.card (G 0) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'

  have hswan : ((ArtinL.swanConductor ρ A : ℚ) : ℂ) =
      ∑ i ∈ Finset.range J, ((Nat.card (G (i + 1)) : ℂ) / (Nat.card (G 0) : ℂ)) * E (G (i + 1)) := by
    unfold ArtinL.swanConductor
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range J) (by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra h
      exact hi (by rw [hcod0 (i + 1) (by omega), Nat.cast_zero, mul_zero]))]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcard, hcard, hR', hI', hcod, hR']

  have hrhs : (∑ᶠ j : ℕ, ((Nat.card (G j) : ℂ) / (Nat.card (G 0) : ℂ)) * E (G j)) =
      ∑ j ∈ Finset.range (J + 1), ((Nat.card (G j) : ℂ) / (Nat.card (G 0) : ℂ)) * E (G j) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra h
    exact hj (by rw [hGJ j (by omega), hEbot, mul_zero])

  change (((ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) : ℚ) + ArtinL.swanConductor ρ A : ℚ) : ℂ) =
    ∑ᶠ j : ℕ, ((Nat.card (G j) : ℂ) / (Nat.card ((Q ^ 1).inertia (K ≃ₐ[ℚ] K)) : ℂ)) * E (G j)
  have hG0' : (Q ^ 1).inertia (K ≃ₐ[ℚ] K) = G 0 := by simp only [hG]
  rw [hG0', hrhs, Finset.sum_range_succ', Rat.cast_add, Rat.cast_natCast, hswan, hcod, hI', div_self hG0, one_mul,
    add_comm]

end KD
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

end LevelBody
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

open scoped MatrixGroups
open NumberField IsDedekindDomain

namespace LVF

open scoped Classical in

noncomputable def artinFun (L : Type) [Field L] [NumberField L] {n : ℕ} (θ : (L ≃ₐ[ℚ] L) →* GL (Fin n) ℂ)
    (Q : Ideal (𝓞 L)) : ℂ :=
  ∑ᶠ j : ℕ, ((Nat.card ((Q ^ (j + 1)).inertia (L ≃ₐ[ℚ] L)) : ℂ) /
      (Nat.card ((Q ^ 1).inertia (L ≃ₐ[ℚ] L)) : ℂ)) *
    ((n : ℂ) - ((Nat.card ((Q ^ (j + 1)).inertia (L ≃ₐ[ℚ] L)) : ℂ))⁻¹ *
      ∑ g : ↥((Q ^ (j + 1)).inertia (L ≃ₐ[ℚ] L)),
        ((θ (g : L ≃ₐ[ℚ] L) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace)

section Helpers

variable {G G' : Type*} [Group G] [Group G'] [Fintype G] [Fintype G']

open scoped Classical in

lemma sum_map_eq_of_injective (ι : G →* G') (hι : Function.Injective ι) (S : Subgroup G) (φ : G' → ℂ) :
    ∑ t : ↥(S.map ι), φ t = ∑ s : ↥S, φ (ι s) := by
  rw [← (Subgroup.equivMapOfInjective S ι hι).sum_comp]
  rfl

lemma card_map_of_injective' (ι : G →* G') (hι : Function.Injective ι) (S : Subgroup G) :
    Nat.card ↥(S.map ι) = Nat.card ↥S :=
  Nat.card_congr (Subgroup.equivMapOfInjective S ι hι).toEquiv.symm

open scoped Classical in
lemma card_filter_apply_eq (r : G →* G') (S : Subgroup G) (s₀ : ↥S) :
    (Finset.univ.filter fun s : ↥S => r s = r s₀).card = Nat.card ↥(S ⊓ r.ker) := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine Finset.card_bij' (fun s _ => ⟨(s₀ : G)⁻¹ * s, Subgroup.mem_inf.mpr ⟨S.mul_mem (S.inv_mem s₀.2) s.2, ?_⟩⟩)
    (fun k _ => ⟨(s₀ : G) * k, S.mul_mem s₀.2 (Subgroup.mem_inf.mp k.2).1⟩) ?_ ?_ ?_ ?_
  · rename_i s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
  · intro s hs; exact Finset.mem_univ _
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hk := (Subgroup.mem_inf.mp k.2).2
    rw [MonoidHom.mem_ker] at hk
    show r ((s₀ : G) * k) = r s₀
    rw [map_mul, hk, mul_one]
  · intro s _; ext; simp
  · intro k _; ext; simp

open scoped Classical in

lemma sum_comp_eq_card_mul_sum_map (r : G →* G') (S : Subgroup G) (φ : G' → ℂ) :
    ∑ s : ↥S, φ (r s) = Nat.card ↥(S ⊓ r.ker) * ∑ t : ↥(S.map r), φ t := by
  have hmaps : ∀ s ∈ (Finset.univ : Finset ↥S),
      (⟨r s, Subgroup.mem_map_of_mem r s.2⟩ : ↥(S.map r)) ∈ (Finset.univ : Finset ↥(S.map r)) :=
    fun s _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨t, ht⟩ := t
  obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp ht
  have hfil : ∀ s : ↥S, ((⟨r s, Subgroup.mem_map_of_mem r s.2⟩ : ↥(S.map r)) = ⟨r s₀, ht⟩) ↔ r s = r (⟨s₀, hs₀⟩ : ↥S) :=
    fun s => Subtype.ext_iff
  rw [Finset.sum_congr rfl fun s hs => by rw [show φ (r s) = φ (r s₀) from congrArg φ ((hfil s).mp (Finset.mem_filter.mp hs).2)],
    Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Finset.filter_congr fun s _ => hfil s]
  exact card_filter_apply_eq r S ⟨s₀, hs₀⟩

lemma card_eq_card_map_mul (r : G →* G') (S : Subgroup G) :
    Nat.card ↥S = Nat.card ↥(S.map r) * Nat.card ↥(S ⊓ r.ker) := by
  classical
  have h := sum_comp_eq_card_mul_sum_map r S (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  exact_mod_cast h.trans (mul_comm _ _)

lemma finsum_nat_eq_zero_add {M : Type*} [AddCommMonoid M] (a : ℕ → M) (h : (Function.support a).Finite) :
    ∑ᶠ j : ℕ, a j = a 0 + ∑ᶠ i : ℕ, a (i + 1) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ j, J ≤ j → a j = 0 := by
    obtain ⟨J, hJ⟩ := h.bddAbove
    exact ⟨J + 1, fun j hj => by_contra fun hne => absurd (hJ hne) (by omega)⟩
  rw [finsum_eq_sum_of_support_subset a (s := Finset.range (J + 1)) fun j hj => by
      by_contra h'; simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h'; exact hj (hJ j (by omega)),
    finsum_eq_sum_of_support_subset (fun i => a (i + 1)) (s := Finset.range J) fun i hi => by
      by_contra h'; simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h'; exact hi (hJ (i + 1) (by omega)),
    Finset.sum_range_succ']
  ac_rfl

end Helpers
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

section L3
variable {n : ℕ} {G : Type} [Group G]

theorem finrank_invariants_eq_inv_card_mul_sum_trace (θ : G →* GL (Fin n) ℂ) (S : Subgroup G) [Fintype ↥S] :
    (Module.finrank ℂ (Representation.invariants ((Deformation.matrixRepresentation θ).comp S.subtype)) : ℂ) =
      (Fintype.card ↥S : ℂ)⁻¹ * ∑ s : ↥S, ((θ (s : G) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := by
  classical
  set π := Deformation.matrixRepresentation θ with hπ
  have h1 : ∀ v ∈ Representation.invariants (π.comp S.subtype), π 1 v ∈ Representation.invariants (π.comp S.subtype) := by
    intro v hv; rw [map_one]; exact hv
  have key := ArtinL.trace_restrict_invariants_eq_inv_card_mul_sum_trace π S 1 h1
  have hid : (π 1).restrict h1 = LinearMap.id := by
    ext v
    simp only [LinearMap.restrict_coe_apply, map_one, LinearMap.id_coe, id_eq]
    rfl
  rw [hid, LinearMap.trace_id] at key
  rw [key]
  refine congrArg _ (Finset.sum_congr rfl (fun s _ => ?_))
  rw [one_mul, hπ, Deformation.matrixRepresentation_apply]
  change LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLin' ((θ (s : G) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) = _
  exact Matrix.trace_toLin'_eq _

end L3
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

section Transport

variable {n : ℕ}

lemma finrank_invariants_congr {G : Type} [Group G] (π : Representation ℂ G (Fin n → ℂ)) {S S' : Subgroup G} (h : S = S') :
    Module.finrank ℂ (Representation.invariants (π.comp S.subtype)) =
      Module.finrank ℂ (Representation.invariants (π.comp S'.subtype)) := by
  subst h; rfl

lemma finrank_invariants_bot {G : Type} [Group G] (π : Representation ℂ G (Fin n → ℂ)) :
    Module.finrank ℂ (Representation.invariants (π.comp (⊥ : Subgroup G).subtype)) = n := by
  have : Representation.invariants (π.comp (⊥ : Subgroup G).subtype) = ⊤ := by
    rw [eq_top_iff]
    rintro v - ⟨g, hg⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  rw [this, finrank_top, Module.finrank_fin_fun]

lemma exists_forall_inertia_pow_eq_bot (L : Type) [Field L] [NumberField L] (Q : Ideal (𝓞 L)) [Q.IsMaximal] :
    ∃ J : ℕ, ∀ j, J ≤ j → (Q ^ (j + 1)).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  classical
  have hanti : Antitone fun j : ℕ => (Q ^ (j + 1)).inertia (L ≃ₐ[ℚ] L) := fun i j hij g hg y =>
    Ideal.pow_le_pow_right (by omega) (hg y)
  have hkr : ⨅ i : ℕ, Q ^ i = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain Q Ideal.IsPrime.ne_top'
  have hg : ∀ g : L ≃ₐ[ℚ] L, g ≠ 1 → ∃ m : ℕ, g ∉ (Q ^ (m + 1)).inertia (L ≃ₐ[ℚ] L) := by
    intro g hg1
    by_contra hall
    push Not at hall
    apply hg1
    ext x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    have hfix : ∀ y : 𝓞 L, g • y = y := fun y => by
      have hmem : g • y - y ∈ ⨅ i : ℕ, Q ^ i := by
        refine Ideal.mem_iInf.mpr fun i => ?_
        rcases i with _ | i
        · simp
        · exact hall i y
      rw [hkr, Ideal.mem_bot, sub_eq_zero] at hmem
      exact hmem
    have ha : g (a : L) = a := congrArg ((↑) : 𝓞 L → L) (hfix a)
    have hb' : g (b : L) = b := congrArg ((↑) : 𝓞 L → L) (hfix b)
    simp [map_div₀, ha, hb']
  choose! m hm using hg
  refine ⟨Finset.univ.sup m, fun j hj => le_bot_iff.mp fun g hgm => ?_⟩
  by_contra hg1
  exact hm g hg1 (hanti ((Finset.le_sup (Finset.mem_univ g)).trans hj) hgm)

open scoped Classical in

theorem artinFun_comp_restrictNormalHom_eq
    (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    [IsGalois ℚ F] [Normal ℚ K]
    (ρK : (K ≃ₐ[ℚ] K) →* GL (Fin n) ℂ) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal] :
    artinFun F (ρK.comp (AlgEquiv.restrictNormalHom K)) 𝔓 = artinFun K ρK (𝔓.under (𝓞 K)) := by
  classical

  have h𝔓ne : 𝔓 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField F)
  let w : HeightOneSpectrum (𝓞 F) := ⟨𝔓, inferInstance, h𝔓ne⟩
  let wK : HeightOneSpectrum (𝓞 K) := HeightOneSpectrum.under (𝓞 K) w
  have hwK : wK.asIdeal = 𝔓.under (𝓞 K) := rfl
  haveI : wK.asIdeal.IsMaximal := by rw [hwK]; infer_instance

  obtain ⟨r, hsurj, hr, -, -, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower ℚ K F w
  have hIF : ∀ j : ℕ, (𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F) = (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j).map (NumberField.PlaceDecomp.decomp ℚ F w).subtype := fun j =>
    IsDedekindDomain.HeightOneSpectrum.inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup ℚ F w j
  have hIK : ∀ j : ℕ, ((𝔓.under (𝓞 K)) ^ (j + 1)).inertia (K ≃ₐ[ℚ] K) = (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) j).map (NumberField.PlaceDecomp.decomp ℚ K wK).subtype := fun j =>
    IsDedekindDomain.HeightOneSpectrum.inertia_asIdeal_pow_succ_eq_map_subtype_lowerRamificationGroup ℚ K wK j

  obtain ⟨f, hfdef⟩ : ∃ f : Subgroup ↥(NumberField.PlaceDecomp.decomp ℚ K wK) → ℚ, f = fun S =>
      (n : ℚ) - Module.finrank ℂ (Representation.invariants ((Deformation.matrixRepresentation ρK).comp
        (S.map (NumberField.PlaceDecomp.decomp ℚ K wK).subtype).subtype)) := ⟨_, rfl⟩
  have hf : f ⊥ = 0 := by
    rw [hfdef]
    simp only
    rw [finrank_invariants_congr _ (Subgroup.map_bot _), finrank_invariants_bot, sub_self]
  obtain ⟨h0, hsum⟩ := NumberField.PlaceDecomp.finsum_card_lowerRamificationGroup_mul_apply_map_eq_of_restrict
    ℚ K F w r hsurj hr f hf

  have htr : ∀ u : K ≃ₐ[ℚ] K, ((ρK u : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ((ρK u : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := fun u => rfl
  have hL3 : ∀ S : Subgroup (K ≃ₐ[ℚ] K),
      (Module.finrank ℂ (Representation.invariants ((Deformation.matrixRepresentation ρK).comp S.subtype)) : ℂ) =
        (Nat.card ↥S : ℂ)⁻¹ * ∑ s : ↥S, ((ρK (s : K ≃ₐ[ℚ] K) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := fun S => by
    rw [finrank_invariants_eq_inv_card_mul_sum_trace ρK S, Nat.card_eq_fintype_card]

  have hK : ∀ j : ℕ, ((Nat.card (((𝔓.under (𝓞 K)) ^ (j + 1)).inertia (K ≃ₐ[ℚ] K)) : ℂ) /
        (Nat.card (((𝔓.under (𝓞 K)) ^ 1).inertia (K ≃ₐ[ℚ] K)) : ℂ)) *
      ((n : ℂ) - ((Nat.card (((𝔓.under (𝓞 K)) ^ (j + 1)).inertia (K ≃ₐ[ℚ] K)) : ℂ))⁻¹ *
        ∑ g : ↥(((𝔓.under (𝓞 K)) ^ (j + 1)).inertia (K ≃ₐ[ℚ] K)),
          ((ρK (g : K ≃ₐ[ℚ] K) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) =
      ((((Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) j) : ℚ) / (Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) 0) : ℚ)) * f (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) j) : ℚ) : ℂ) := by
    intro j
    have h1 : ((𝔓.under (𝓞 K)) ^ 1).inertia (K ≃ₐ[ℚ] K) = (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) 0).map (NumberField.PlaceDecomp.decomp ℚ K wK).subtype := by
      rw [show (1 : ℕ) = 0 + 1 from rfl]; exact hIK 0
    rw [hIK j, h1, ← hL3, card_map_of_injective' _ (NumberField.PlaceDecomp.decomp ℚ K wK).subtype_injective, card_map_of_injective' _ (NumberField.PlaceDecomp.decomp ℚ K wK).subtype_injective]
    simp only [hfdef]
    push_cast
    try ring

  have hF : ∀ j : ℕ, ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ) /
        (Nat.card ((𝔓 ^ 1).inertia (F ≃ₐ[ℚ] F)) : ℂ)) *
      ((n : ℂ) - ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ))⁻¹ *
        ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)),
          (((ρK.comp (AlgEquiv.restrictNormalHom K)) (g : F ≃ₐ[ℚ] F) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) =
      ((((Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j) : ℚ) / (Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) 0) : ℚ)) * f ((ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j).map r) : ℚ) : ℂ) := by
    intro j
    have h1 : (𝔓 ^ 1).inertia (F ≃ₐ[ℚ] F) = (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) 0).map (NumberField.PlaceDecomp.decomp ℚ F w).subtype := by
      rw [show (1 : ℕ) = 0 + 1 from rfl]; exact hIF 0
    rw [hIF j, h1, card_map_of_injective' _ (NumberField.PlaceDecomp.decomp ℚ F w).subtype_injective, card_map_of_injective' _ (NumberField.PlaceDecomp.decomp ℚ F w).subtype_injective]
    rw [sum_map_eq_of_injective (NumberField.PlaceDecomp.decomp ℚ F w).subtype (NumberField.PlaceDecomp.decomp ℚ F w).subtype_injective (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j)
      (fun g => (((ρK.comp (AlgEquiv.restrictNormalHom K)) g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace)]
    have hres : ∀ s : ↥(ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j), (((ρK.comp (AlgEquiv.restrictNormalHom K)) ((NumberField.PlaceDecomp.decomp ℚ F w).subtype s) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        (fun u : ↥(NumberField.PlaceDecomp.decomp ℚ K wK) => ((ρK ((NumberField.PlaceDecomp.decomp ℚ K wK).subtype u) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) (r s) := fun s => by
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [← hr s]
    simp_rw [hres]
    rw [sum_comp_eq_card_mul_sum_map r (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j) (fun u : ↥(NumberField.PlaceDecomp.decomp ℚ K wK) => ((ρK ((NumberField.PlaceDecomp.decomp ℚ K wK).subtype u) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace)]
    rw [← sum_map_eq_of_injective (NumberField.PlaceDecomp.decomp ℚ K wK).subtype (NumberField.PlaceDecomp.decomp ℚ K wK).subtype_injective ((ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j).map r)
      (fun u => ((ρK u : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace)]
    have hcard := card_eq_card_map_mul r (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j)
    have hfin := hL3 (((ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j).map r).map (NumberField.PlaceDecomp.decomp ℚ K wK).subtype)
    rw [card_map_of_injective' _ (NumberField.PlaceDecomp.decomp ℚ K wK).subtype_injective] at hfin
    simp only [hfdef]
    push_cast [hcard]
    have hm : (Nat.card ↥((ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j).map r) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hk : (Nat.card ↥((ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j) ⊓ r.ker) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    try simp only [Subgroup.coe_subtype, MonoidHom.comp_apply] at hfin
    try simp only [Subgroup.coe_subtype, MonoidHom.comp_apply]
    rw [hfin]
    generalize (∑ s : ↥(((ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j).map r).map
        (NumberField.PlaceDecomp.decomp ℚ K wK).subtype),
      ((ρK (s : K ≃ₐ[ℚ] K) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) = S at *
    have hmS : ∀ (m G0 : ℂ), m ≠ 0 → m * S * G0⁻¹ * m⁻¹ = S * G0⁻¹ := fun m G0 hm' => by field_simp
    field_simp
    ring_nf
    rw [hmS _ _ hm]

  simp only [artinFun]
  rw [finsum_congr hF, finsum_congr hK]
  have hsuppF : (Function.support fun j : ℕ => (((Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j) : ℚ) / (Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) 0) : ℚ)) * f ((ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j).map r) : ℚ)).Finite := by
    obtain ⟨J, hJ⟩ := exists_forall_inertia_pow_eq_bot F 𝔓
    refine (Finset.range J).finite_toSet.subset fun j hj => ?_
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
    apply hj
    have hbot : (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j) = ⊥ := by
      have := hJ j h
      rw [hIF j, Subgroup.map_eq_bot_iff_of_injective (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) j) (NumberField.PlaceDecomp.decomp ℚ F w).subtype_injective] at this
      exact this
    simp [hbot, hf]
  have hsuppK : (Function.support fun j : ℕ => (((Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) j) : ℚ) / (Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) 0) : ℚ)) * f (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) j) : ℚ)).Finite := by
    obtain ⟨J, hJ⟩ := exists_forall_inertia_pow_eq_bot K (𝔓.under (𝓞 K))
    refine (Finset.range J).finite_toSet.subset fun j hj => ?_
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
    apply hj
    have hbot : (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) j) = ⊥ := by
      have := hJ j h
      rw [hIK j, Subgroup.map_eq_bot_iff_of_injective (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) j) (NumberField.PlaceDecomp.decomp ℚ K wK).subtype_injective] at this
      exact this
    simp [hbot, hf]
  have hcastF := (AddMonoidHom.map_finsum (Rat.castHom ℂ).toAddMonoidHom hsuppF).symm
  have hcastK := (AddMonoidHom.map_finsum (Rat.castHom ℂ).toAddMonoidHom hsuppK).symm
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Rat.coe_castHom] at hcastF hcastK
  rw [hcastF, hcastK]
  congr 1
  rw [finsum_nat_eq_zero_add _ hsuppF, finsum_nat_eq_zero_add _ hsuppK, hsum, h0]
  congr 1
  have hF0 : (Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((w.valuation F).valuationSubring) 0) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hK0 : (Nat.card (ValuationSubring.lowerRamificationGroup ℚ ((wK.valuation K).valuationSubring) 0) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [div_self hF0, div_self hK0]

end Transport
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

end LVF
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

namespace LVF

section PlaceIndep

variable {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]

theorem smul_ideal_pow' (x : G) (I : Ideal B) (k : ℕ) : (x • I) ^ k = x • I ^ k := by
  simp only [Ideal.pointwise_smul_def, Ideal.map_pow]

theorem mem_inertia_smul_pow_iff' (x g : G) (I : Ideal B) (k : ℕ) :
    g ∈ ((x • I) ^ k).inertia G ↔ x⁻¹ * g * x ∈ (I ^ k).inertia G := by
  rw [smul_ideal_pow']
  constructor
  · intro hg z
    have := hg (x • z)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, ← mul_smul, ← mul_smul,
      inv_smul_smul] at this
    rw [Submodule.mem_toAddSubgroup]
    simpa [mul_assoc] using this
  · intro hg y
    have := hg (x⁻¹ • y)
    rw [Submodule.mem_toAddSubgroup] at this ⊢
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, ← mul_smul]
    rw [← mul_smul, show x⁻¹ * g * x * x⁻¹ = x⁻¹ * g by group] at this
    exact this

def inertiaSmulEquiv (x : G) (I : Ideal B) (k : ℕ) : ↥(((x • I) ^ k).inertia G) ≃ ↥((I ^ k).inertia G) where
  toFun g := ⟨x⁻¹ * g * x, (mem_inertia_smul_pow_iff' x g I k).mp g.2⟩
  invFun g := ⟨x * g * x⁻¹, (mem_inertia_smul_pow_iff' x _ I k).mpr (by simpa [mul_assoc] using g.2)⟩
  left_inv g := by ext; simp [mul_assoc]
  right_inv g := by ext; simp [mul_assoc]

theorem card_inertia_smul_pow (x : G) (I : Ideal B) (k : ℕ) :
    Nat.card ↥(((x • I) ^ k).inertia G) = Nat.card ↥((I ^ k).inertia G) :=
  Nat.card_congr (inertiaSmulEquiv x I k)

theorem trace_conj {n : ℕ} (θ : G →* GL (Fin n) ℂ) (x g : G) :
    ((θ (x⁻¹ * g * x) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace = ((θ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, ← map_mul,
    mul_inv_cancel, map_one, Units.val_one, one_mul]

theorem sum_trace_inertia_smul_pow {n : ℕ} (θ : G →* GL (Fin n) ℂ) (x : G) (I : Ideal B) (k : ℕ)
    [Fintype ↥(((x • I) ^ k).inertia G)] [Fintype ↥((I ^ k).inertia G)] :
    ∑ g : ↥(((x • I) ^ k).inertia G), ((θ (g : G) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
      ∑ g : ↥((I ^ k).inertia G), ((θ (g : G) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace :=
  Fintype.sum_equiv (inertiaSmulEquiv x I k) _ _ fun g => by
    show _ = ((θ (x⁻¹ * (g : G) * x) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace
    rw [trace_conj]

end PlaceIndep
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

section NumberFieldLevel

variable (L : Type) [Field L] [NumberField L] {n : ℕ}

theorem artinFun_smul (θ : (L ≃ₐ[ℚ] L) →* GL (Fin n) ℂ) (x : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) :
    artinFun L θ (x • Q) = artinFun L θ Q := by
  classical
  unfold artinFun
  refine finsum_congr fun j => ?_
  rw [card_inertia_smul_pow, card_inertia_smul_pow, sum_trace_inertia_smul_pow]

theorem artinFun_eq_of_under_eq [IsGalois ℚ L] (θ : (L ≃ₐ[ℚ] L) →* GL (Fin n) ℂ) (Q Q' : Ideal (𝓞 L))
    [Q.IsMaximal] [Q'.IsMaximal] (h : Q.under ℤ = Q'.under ℤ) :
    artinFun L θ Q = artinFun L θ Q' := by
  obtain ⟨x, hx⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := ℤ) (B := 𝓞 L) (G := L ≃ₐ[ℚ] L) (P := Q) (Q := Q') h
  rw [hx, artinFun_smul]

theorem under_int_eq_span (Q : Ideal (𝓞 L)) [Q.IsMaximal] {p : ℕ} (hp : p.Prime) (hpQ : (p : 𝓞 L) ∈ Q) :
    Q.under ℤ = Ideal.span {(p : ℤ)} := by
  have hle : Ideal.span {(p : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ Q
    rw [map_natCast]; exact hpQ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)
  exact (hmax.eq_of_le (Ideal.IsMaximal.under ℤ Q).ne_top hle).symm

end NumberFieldLevel
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

section Identify

variable {n : ℕ}

theorem restrictNormal_restrictNormal
    (K F M : Type) [Field K] [Field F] [Field M] [Algebra ℚ K] [Algebra ℚ F] [Algebra ℚ M]
    [Algebra K F] [Algebra F M] [Algebra K M] [IsScalarTower ℚ K F] [IsScalarTower ℚ F M] [IsScalarTower ℚ K M]
    [IsScalarTower K F M] [Normal ℚ K] [Normal ℚ F] (χ : M ≃ₐ[ℚ] M) :
    (χ.restrictNormal F).restrictNormal K = χ.restrictNormal K := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap K M).injective
  rw [AlgEquiv.restrictNormal_commutes, IsScalarTower.algebraMap_apply K F M, AlgEquiv.restrictNormal_commutes,
    AlgEquiv.restrictNormal_commutes, ← IsScalarTower.algebraMap_apply]

theorem eq_comp_restrictNormalHom_of_comp_eq
    (K F M : Type) [Field K] [Field F] [Field M] [Algebra ℚ K] [Algebra ℚ F] [Algebra ℚ M]
    [Algebra K F] [Algebra F M] [Algebra K M] [IsScalarTower ℚ K F] [IsScalarTower ℚ F M] [IsScalarTower ℚ K M]
    [IsScalarTower K F M] [Normal ℚ K] [Normal ℚ F] [Normal ℚ M]
    (ρM : (M ≃ₐ[ℚ] M) →* GL (Fin n) ℂ) (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (ρK : (K ≃ₐ[ℚ] K) →* GL (Fin n) ℂ)
    (hF : ρM = ρF.comp (AlgEquiv.restrictNormalHom F)) (hK : ρM = ρK.comp (AlgEquiv.restrictNormalHom K)) :
    ρF = ρK.comp (AlgEquiv.restrictNormalHom K) := by
  apply MonoidHom.ext
  intro τ
  obtain ⟨χ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := F) (E := M) τ
  have h := DFunLike.congr_fun (hF.symm.trans hK) χ
  simp only [MonoidHom.comp_apply] at h
  rw [MonoidHom.comp_apply]
  show ρF (AlgEquiv.restrictNormalHom F χ) = ρK (AlgEquiv.restrictNormalHom K (AlgEquiv.restrictNormalHom F χ))
  rw [h]
  congr 1
  exact (restrictNormal_restrictNormal K F M χ).symm
end Identify
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

end LVF
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

namespace LevelAsm

local notation "ℚbar" => AlgebraicClosure ℚ

local instance isAlgebraicQbar' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar' : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance isGaloisQbar' : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)

theorem splittingField_le (F : IntermediateField ℚ ℚbar) [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F)) :
    ArtinL.splittingField ρ ≤ F := by
  have h1 : F.fixingSubgroup ≤ ρ.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply]
    have : AlgEquiv.restrictNormalHom F σ = 1 := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      change algebraMap F ℚbar (σ.restrictNormal F x) = algebraMap F ℚbar x
      rw [AlgEquiv.restrictNormal_commutes]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x x.2
    rw [this, map_one]
  have h2 := IntermediateField.fixedField_antitone (F := ℚ) (E := ℚbar) h1
  rwa [InfiniteGalois.fixedField_fixingSubgroup] at h2

end LevelAsm
p2m_reactivate "P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom.LevelBody"

open LevelAsm in
open scoped Classical in
theorem solution {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    (p : ℕ) (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal] (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) :
    (((ArtinL.codimInvariants ρ (A.inertiaSubgroupIn ℚ) : ℚ) + ArtinL.swanConductor ρ A : ℚ) : ℂ) =
      ∑ᶠ j : ℕ, ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ) /
          (Nat.card ((𝔓 ^ 1).inertia (F ≃ₐ[ℚ] F)) : ℂ)) *
        ((n : ℂ) - ((Nat.card ((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) : ℂ))⁻¹ *
          ∑ g : ↥((𝔓 ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)),
            ((ρF (g : F ≃ₐ[ℚ] F) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace) := by

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

  have hfin : GaloisFactorsThroughFiniteLevel ρ := LevelBody.galoisFactors_of_comp ρ F ρF hρ
  haveI hKnf : NumberField ↥(ArtinL.splittingField ρ) := LevelBody.numberField_splittingField ρ hfin
  have hle : ArtinL.splittingField ρ ≤ F := splittingField_le ρ F ρF hρ
  letI : Algebra ↥(ArtinL.splittingField ρ) ↥F := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ ↥(ArtinL.splittingField ρ) ↥F :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hle).commutes x).symm
  haveI : IsScalarTower ↥(ArtinL.splittingField ρ) ↥F (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsGalois ℚ ↥(ArtinL.splittingField ρ) := ⟨⟩

  obtain ⟨Q, hQmax, hpQ, hK⟩ := LevelBody.kbridge ρ hfin hp A hA
  rw [hK]
  change LVF.artinFun ↥(ArtinL.splittingField ρ) (LevelBody.rhoK ρ hfin) Q = LVF.artinFun ↥F ρF 𝔓

  have hunder : Q.under ℤ = (𝔓.under (𝓞 ↥(ArtinL.splittingField ρ))).under ℤ := by
    rw [LVF.under_int_eq_span _ Q hp hpQ, Ideal.under_under, h𝔓]
  rw [LVF.artinFun_eq_of_under_eq ↥(ArtinL.splittingField ρ) (LevelBody.rhoK ρ hfin) Q
    (𝔓.under (𝓞 ↥(ArtinL.splittingField ρ))) hunder]

  rw [← LVF.artinFun_comp_restrictNormalHom_eq ↥(ArtinL.splittingField ρ) ↥F (LevelBody.rhoK ρ hfin) 𝔓]

  congr 1
  exact (LVF.eq_comp_restrictNormalHom_of_comp_eq ↥(ArtinL.splittingField ρ) ↥F (AlgebraicClosure ℚ) ρ ρF (LevelBody.rhoK ρ hfin)
    hρ (LevelBody.rhoK_comp ρ hfin).symm).symm

end S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom
end P2MW
export P2MW.S_ArtinL_codimInvariants_add_swanConductor_eq_finsum_card_mul_sub_sum_trace_of_comp_restrictNormalHom (solution)
