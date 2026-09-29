-- Prove2me | solution 1 for AlgebraicCurve.tateChainRule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/94afbce2-9eee-5e62-a161-cc19cce611fe

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import Definitions.Def_AlgebraicCurve_TateResidueCurrency
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AlgebraicCurve_tateChainRule

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
p2m_open "AlgebraicCurve"
end AlgebraicCurve
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"
end AlgebraicCurve.Place
namespace Filter
p2m_export "Filter" "ker mk mem_comap mem_ker mem_top comap unique map_mono map"
p2m_open "Filter"
end Filter
namespace IntermediateField
p2m_export "IntermediateField" "toAlgebra mk val isIntegral_iff inclusion ext algebraMap_apply smul_def finiteDimensional_sup comap mem_top restrictScalars restrictScalars_top coe_smul map_mono smul_mem restrict map"
p2m_open "IntermediateField"
end IntermediateField
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.ext mk HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.ext mk HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "valuation_of_algebraMap intValuation_le_pow_iff_mem isMaximal mk comap valuedAdicCompletion_eq_valuation' adicCompletion valuation adicCompletionIntegers valuedAdicCompletion_surjective mem_integers_of_valuation_le_one denseRange_algebraMap intValuation completionIdeal adicCompletion.mem_completionIdeal_pow"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"
end IsDedekindDomain.HeightOneSpectrum
namespace IsLocalRing
p2m_export "IsLocalRing" "ResidueField maximalIdeal maximalIdeal.isMaximal of_injective"
p2m_open "IsLocalRing"
end IsLocalRing
namespace KaehlerDifferential
p2m_export "KaehlerDifferential" "finite D map_D map"
p2m_open "KaehlerDifferential"
end KaehlerDifferential
namespace LinearMap
p2m_export "LinearMap" "mulLeft_apply coe_smul mem_range range sub_apply coe_mk add_apply ker_eq_bot range_zero id range_comp codRestrict smul_apply mulLeft ker_comp trace_comp_comm' mk id_apply ext comp isIntegral trace quotKerEquivRange finiteDimensional range_comp_le_range restrictScalars ker mem_ker comp_apply mem_range_self restrict"
p2m_open "LinearMap"
end LinearMap
namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4R1V410a
p2m_open "ModularCurve"
end ModularCurve.KwF4R1V410a
namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4R1V473a
p2m_open "ModularCurve"
end ModularCurve.KwF4R1V473a
namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"
end ModularCurve.KwF4gRRTate
namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace Lg37
p2m_open "ModularCurve"
end ModularCurve.Lg37
namespace Module
p2m_export "Module" "Injective equiv Finite.equiv mk restrictScalars Finite.of_submodule_quotient"
p2m_open "Module"
end Module
namespace MonoidWithZeroHom
p2m_export "MonoidWithZeroHom" "id_apply id ext mk coe_mk coe_one comp_apply comp"
p2m_open "MonoidWithZeroHom"
end MonoidWithZeroHom
namespace Multiplicative
p2m_export "Multiplicative" "ext smul"
p2m_open "Multiplicative"
end Multiplicative
namespace NumberField
p2m_export "NumberField" "mk"
p2m_open "NumberField"
end NumberField
namespace Pointwise
p2m_open "Pointwise"
end Pointwise
namespace Polynomial
p2m_export "Polynomial" "coe_one algebraMap_eq unique ext_iff toSubring map comp coe_mul coe_sub coe_smul algebraMap_apply ext ring"
p2m_open "Polynomial"
end Polynomial
namespace Submodule
p2m_export "Submodule" "quotEquivOfEq inclusion mem_sup_right coe_smul smul_mem' mk smul_mem coe_mem Quotient.mk span restrictScalars projectionOnto_apply_left restrictScalars_top mem_closure_iff Quotient.restrictScalarsEquiv mem_comap mem_top Quotient.equiv mem_span_singleton mkQ map_mono map_smul' equivMapOfInjective zero quotientQuotientEquivQuotient coe_eq_zero range_subtype Quotient.mk_surjective restrictScalars_mono map coe_mk exists_isCompl projectionOnto finiteDimensional_of_le smul_def restrictScalarsEquiv ext ker_mkQ comap finiteDimensional_sup liftQ mem_sup_left smul restrictScalars_mem"
p2m_open "Submodule"
end Submodule
namespace Topology
p2m_open "Topology"
end Topology
namespace WithZero
p2m_export "WithZero" "coe_one map coe_mul exp_eq_coe_ofAdd coe exp_ne_zero exp exp_zero exp_le_exp"
p2m_open "WithZero"
end WithZero

section
namespace IsLocalRing p2m_export "IsLocalRing" "ResidueField maximalIdeal maximalIdeal.isMaximal of_injective" end IsLocalRing
p2m_open_scoped "IsLocalRing" in
theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R

scoped instance instAlgebraSubtypeMemValuationSubring_fLT {K L : Type*} [Field K] [Semiring L]
    (O : ValuationSubring K) [Algebra K L] : Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' _ _ := by simp [← Algebra.smul_def]; rfl
end

section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

p2m_open "LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateFactoring

end ModularCurve.KwF4gRRTate

end

end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_tateChainRule.WithZero IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place"

variable {K F}

variable (v : Place K F)

end Place

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "smul_def smul_apply"
p2m_open "AlgebraicCurve.Divisor"

variable {K F}

end Divisor

namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "mk mk_surjective"
p2m_open "AlgebraicCurve.Pic0"

variable {K F}

end Pic0

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place"

p2m_open_scoped "Pointwise P2MW.S_AlgebraicCurve_tateChainRule.Pointwise"

variable {K F}
variable (σ : F ≃ₐ[K] F)

variable (v : Place K F)

end Place

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "smul_def smul_apply"
p2m_open "AlgebraicCurve.Divisor"

p2m_open_scoped "Pointwise P2MW.S_AlgebraicCurve_tateChainRule.Pointwise"

variable {K F}

end Divisor

namespace Pic0
p2m_export "AlgebraicCurve.Pic0" "mk mk_surjective"
p2m_open "AlgebraicCurve.Pic0"

p2m_open_scoped "Pointwise P2MW.S_AlgebraicCurve_tateChainRule.Pointwise"

variable {K F}

end Pic0

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place"

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

end Place

end AlgebraicCurve

end
end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_tateChainRule.WithZero IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place"

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
private theorem _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩

p2m_export "AlgebraicCurve.Place" "mem_iff_ord_nonneg"
theorem exists_ord_pos : ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  refine ⟨(π : F), ?_, ?_⟩
  · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  · rw [v.ord_coe_irreducible hπ]
    exact one_pos

end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

private theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')

private theorem _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'

  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)

  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  letI : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  letI : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : _root_.IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2

p2m_export "AlgebraicCurve.Place" "comap_algebraMap_ne_top"
variable {w} in

theorem mem_comap_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  rw [ValuationSubring.mem_comap]
  exact w.mem_iff_ord_nonneg (algebraMap_ne_zero hf)

variable {w} in

theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0)
    (hmem : f ∈ w.toValuationSubring.comap (algebraMap F F')) :
    IsUnit (⟨f, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) ↔
      w.ord (algebraMap F F' f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F) = 1 := by
      simpa [Subtype.ext_iff] using hb
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : w.ord (algebraMap F F' f) + w.ord (algebraMap F F' (b : F)) = 0 := by
      rw [← w.ord_mul (algebraMap_ne_zero hf) (algebraMap_ne_zero hbne), ← map_mul, hb',
        map_one, w.ord_one]
    have h1 : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ w.ord (algebraMap F F' (b : F)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ w.toValuationSubring.comap (algebraMap F F') :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, w.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

private theorem _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
    ∃ f : F, f ≠ 0 ∧ 0 < w.ord (algebraMap F F' f) := by
  have h := w.comap_algebraMap_ne_top (F := F)
  rw [ne_eq, SetLike.ext_iff, not_forall] at h
  obtain ⟨g, hg⟩ := h
  simp only [ValuationSubring.mem_top, iff_true] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg (zero_mem _)
  refine ⟨g⁻¹, inv_ne_zero hg0, ?_⟩
  rw [map_inv₀, w.ord_inv]
  have := (mem_comap_iff_ord_nonneg hg0).not.mp hg
  omega

p2m_export "AlgebraicCurve.Place" "exists_ord_algebraMap_pos"
variable [Algebra.IsIntegral F F']

private theorem ramificationIndex_set_nonempty :
    {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n}.Nonempty := by
  obtain ⟨f, hf0, hf⟩ := w.exists_ord_algebraMap_pos (F := F)
  exact ⟨(w.ord (algebraMap F F' f)).toNat, by omega, f, hf0, by omega⟩

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (w.toValuationSubring.comap (algebraMap F F')) := by
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  have hgmem : g ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap w hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx

  obtain ⟨c, hc⟩ := w.ramificationIndex_dvd_ord (F := F) hf
  have hnonneg : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (ramificationIndex (F := F) w : ℤ) * c ≤ (ramificationIndex (F := F) w : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩

  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : w.ord (algebraMap F F' (f / g ^ n)) = 0 := by
    have hkey : algebraMap F F' (f / g ^ n)
        = algebraMap F F' f * (algebraMap F F' g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F F' g) n,
        ← _root_.zpow_neg]
    rw [hkey, w.ord_mul (algebraMap_ne_zero hf) (zpow_ne_zero _ (algebraMap_ne_zero hg0)),
      w.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : w.toValuationSubring.comap (algebraMap F F')) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : w.toValuationSubring.comap (algebraMap F F')) : F) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

section RestrictDef

variable [Algebra K F] [IsScalarTower K F F']

end RestrictDef

end Restrict

end Place

end AlgebraicCurve

end
end

end

section
section

section

variable {F : Type*} [Field F]

namespace ValuationSubring p2m_export "ValuationSubring" "comap subtype mem_comap toSubring algebraMap_apply ext zero_mem mk mem_top mul_mem add_mem valuation inclusion" end ValuationSubring
p2m_open_scoped "ValuationSubring" in
theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _

p2m_open_scoped "ValuationSubring" in
theorem ValuationSubring.isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  have : IsUnit x.val := by rw [isUnit_iff_ne_zero, ne_eq, ← map_eq_zero hv.v, hx]; aesop
  obtain ⟨u, hu⟩ := this
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  rw [isUnit_iff_exists]
  exact ⟨⟨u⁻¹.val, hu_inv_le⟩,  ⟨by aesop, by aesop⟩⟩

p2m_open_scoped "ValuationSubring" in
theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩

end

end

end

section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing WithZero P2MW.S_AlgebraicCurve_tateChainRule.WithZero MonoidWithZeroHom P2MW.S_AlgebraicCurve_tateChainRule.MonoidWithZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section AdicCompletion

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end AdicCompletion

section Henselian

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

end Henselian

section WithValLevel

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end WithValLevel

section CompletionComap

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end CompletionComap

section Bridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

end Bridge

end AlgebraicCurve.Place

end
end

end

section
section

noncomputable section

p2m_open "KaehlerDifferential P2MW.S_AlgebraicCurve_tateChainRule.KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
p2m_export "AlgebraicCurve.IsCurveOver" "mk"
p2m_open "AlgebraicCurve.IsCurveOver"

variable {K F}

end IsCurveOver

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue heightOneSpectrum heightOneSpectrum_asIdeal ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring mk dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord uniformizer ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place"

variable {K F}
variable (v : Place K F)

end Place

variable {K F}

variable (K F)

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end ModularCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
p2m_open "ModularCurve"

end ModularCurve

end
end

end

section
section

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_tateChainRule.WithZero Module P2MW.S_AlgebraicCurve_tateChainRule.Module IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver HasCanonicalDivisor HasCanonicalLocalResidueKStar kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kaehlerPullback"
p2m_open "AlgebraicCurve"

section Helpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end Helpers

section NoGoEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

namespace FiberKaehlerLocalDatum

end FiberKaehlerLocalDatum

end NoGoEngine

section FKRINoGo

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

end FKRINoGo

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

variable {K F E}

@[scoped simp] theorem kaehlerPullback_D (e : E) :
    kaehlerPullback K F E (KaehlerDifferential.D K E e)
      = KaehlerDifferential.D K F (algebraMap E F e) :=
  KaehlerDifferential.map_D K K E F e

variable (K F E)
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

end CorrectedCarrier

section CorrectedEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable {E : Type*} [Field E] [Algebra K E]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalDivisor (K := K) (F := E)]
variable [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

end CorrectedEngine

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve Polynomial P2MW.S_AlgebraicCurve_tateChainRule.Polynomial IntermediateField P2MW.S_AlgebraicCurve_tateChainRule.IntermediateField"

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

section ProductionNondegeneracy

end ProductionNondegeneracy
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section ProductionNoGo

end ProductionNoGo
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section CorrectedProductionJoin

variable (N : ℕ) [NeZero N]

end CorrectedProductionJoin
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section AxiomAudit

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem mem_adicIntegersKSubmod_iff (x : u.adicCompletion) :
    x ∈ adicIntegersKSubmod u ↔ x ∈ u.adicCompletionIntegers := Iff.rfl

theorem tateProj_mem_integers (x : u.adicCompletion) :
    tateProj u x ∈ u.adicCompletionIntegers :=
  (mem_adicIntegersKSubmod_iff u _).mp
    (Submodule.coe_mem
      (Submodule.projectionOnto (adicIntegersKSubmod u) _
        (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u))) x))

theorem tateProj_of_mem {x : u.adicCompletion} (hx : x ∈ u.adicCompletionIntegers) :
    tateProj u x = x := by
  have h := Submodule.projectionOnto_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))
    (⟨x, (mem_adicIntegersKSubmod_iff u x).mpr hx⟩ : adicIntegersKSubmod u)
  have hcoe := congrArg (Subtype.val (p := fun y => y ∈ adicIntegersKSubmod u)) h
  exact hcoe

theorem tateProj_idem : tateProj u ∘ₗ tateProj u = tateProj u := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact tateProj_of_mem u (tateProj_mem_integers u x)

theorem range_tateProj : LinearMap.range (tateProj u) = adicIntegersKSubmod u := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact tateProj_mem_integers u y
  · intro x hx
    exact ⟨x, tateProj_of_mem u hx⟩

end TateProj
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateResDef
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable [HasCanonicalLocalResidueKStar K L]

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

end TateAtoms
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section PoleWindow

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletion where
  carrier := {x | (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, mul_add] at ha hb ⊢; exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero]; exact zero_mem _
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K L u.adicCompletion, mul_left_comm]
    exact mul_mem ((kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
      (u.algebraMap_mem' c)) hx

theorem mem_poleWindowKSubmod_iff (πh : u.adicCompletionIntegers) (M : ℕ)
    (x : u.adicCompletion) :
    x ∈ poleWindowKSubmod u πh M ↔ (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers :=
  Iff.rfl

theorem adicIntegersKSubmod_le_poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    adicIntegersKSubmod u ≤ poleWindowKSubmod u πh M :=
  fun _ hx => mul_mem (pow_mem πh.2 M) hx

theorem kwF4gRRTate_clearPole (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (fh : u.adicCompletion) :
    ∃ M : ℕ, (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers := by
  obtain ⟨a, b, hb, hfh⟩ := IsFractionRing.div_surjective
    (A := u.adicCompletionIntegers) (K := u.adicCompletion) fh
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨M, ub, hbeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπh
  refine ⟨M, ?_⟩

  have hcoe : ∀ x : u.adicCompletionIntegers,
      (x : u.adicCompletion) = algebraMap _ u.adicCompletion x := fun _ => rfl
  have hbK0 : (b : u.adicCompletion) ≠ 0 := by
    rw [hcoe]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have hbfh : (b : u.adicCompletion) * fh = (a : u.adicCompletion) := by
    rw [← hfh, hcoe b, hcoe a, mul_div_cancel₀ _ (hcoe b ▸ hbK0)]

  have hπheq : ((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers) * b = πh ^ M := by
    rw [hbeq, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

  have hπheqK : ((((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers)
        : u.adicCompletion)) * (b : u.adicCompletion)
      = (πh : u.adicCompletion)^M := by
    have := congrArg (algebraMap u.adicCompletionIntegers u.adicCompletion) hπheq
    simp only [map_mul, map_pow] at this
    exact this

  rw [← hπheqK, mul_assoc, hbfh]
  exact mul_mem (Subtype.coe_prop _) a.2

variable (K L) in

def KwF4gRRTatePoleWindowFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K
      (poleWindowKSubmod u πh M ⧸
        (adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)

end PoleWindow
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section
section

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open_scoped "WithZero P2MW.S_AlgebraicCurve_tateChainRule.WithZero Multiplicative P2MW.S_AlgebraicCurve_tateChainRule.Multiplicative Topology P2MW.S_AlgebraicCurve_tateChainRule.Topology"
p2m_open "Filter P2MW.S_AlgebraicCurve_tateChainRule.Filter"

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.ext mk HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "valuation_of_algebraMap intValuation_le_pow_iff_mem isMaximal mk comap valuedAdicCompletion_eq_valuation' adicCompletion valuation adicCompletionIntegers valuedAdicCompletion_surjective mem_integers_of_valuation_le_one denseRange_algebraMap intValuation completionIdeal adicCompletion.mem_completionIdeal_pow"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

namespace adicCompletion
p2m_export "IsDedekindDomain.HeightOneSpectrum.adicCompletion" "mem_completionIdeal_pow"
p2m_open "IsDedekindDomain.HeightOneSpectrum.adicCompletion"

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

theorem isOpen_setOf_valued_le {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ γ} := by

  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective K v γ
  have hz0 : vK z ≠ 0 := by rw [hz]; exact hγ
  have hr0 : (vK).restrict z ≠ 0 := fun h =>
    hz0 ((Valuation.restrict_eq_zero_iff vK).mp h)
  have hset : {y : v.adicCompletion K | Valued.v y ≤ γ}
      = {y : v.adicCompletion K | (vK).restrict y ≤ (vK).restrict z} := by
    ext y
    simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, hz]
  rw [hset]
  exact Valued.isOpen_closedBall _ hr0

end adicCompletion
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section NumberField

p2m_open "NumberField P2MW.S_AlgebraicCurve_tateChainRule.NumberField"

variable (F : Type*) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

end NumberField
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end IsDedekindDomain.HeightOneSpectrum
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section AxiomAudit

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain.HeightOneSpectrum"

end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing WithZero P2MW.S_AlgebraicCurve_tateChainRule.WithZero"
p2m_open "P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.Lg37 AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place"

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4R1V410a
p2m_open "ModularCurve"

scoped instance kwF4R1V410a_subsingletonHeightOneSpectrumDVR
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Subsingleton (HeightOneSpectrum O) :=
  ⟨fun a b => IsDedekindDomain.HeightOneSpectrum.ext
    (((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp
      inferInstance).2.unique ⟨a.3, a.2⟩ ⟨b.3, b.2⟩)⟩

section Bridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

local notation "O_w" => w.toValuationSubring
local notation "𝔪_w" => IsLocalRing.maximalIdeal w.toValuationSubring
local notation "O_W" => w.adicCompletionIntegers
local notation "𝔪_W" => w.heightOneSpectrum.completionIdeal F

theorem kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff (n : ℕ) (x : O_w) :
    algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n ↔ x ∈ (𝔪_w) ^ n := by
  have hval : Valued.v (algebraMap (O_w) (O_W) x).val
      = w.heightOneSpectrum.intValuation x := by
    have h1 : (algebraMap (O_w) (O_W) x).val
        = ((algebraMap (O_w) F x : F) : w.adicCompletion) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation' (K := F) w.heightOneSpectrum,
      valuation_of_algebraMap]
  rw [adicCompletion.mem_completionIdeal_pow, hval, ← WithZero.exp_eq_coe_ofAdd,
    intValuation_le_pow_iff_mem, w.heightOneSpectrum_asIdeal]

theorem kwF4R1V410a_exists_sub_mem_completionIdeal_pow (n : ℕ) (y : O_W) :
    ∃ x : O_w, y - algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n := by

  have hball_open : IsOpen {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} :=
    (adicCompletion.isOpen_setOf_valued_le F w.heightOneSpectrum
      WithZero.exp_ne_zero).preimage (continuous_sub_right y.val)
  have hy_mem : y.val ∈ {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} := by
    simp only [Set.mem_setOf_eq, sub_self, _root_.map_zero]; exact WithZero.zero_le _
  have hmeet := mem_closure_iff.mp
    ((denseRange_algebraMap F w.heightOneSpectrum) y.val) _ hball_open hy_mem

  have hexists : ∃ z : F, Valued.v (algebraMap F w.adicCompletion z - y.val)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rcases hmeet with ⟨z₀, hz₀_ball, z, hz_eq⟩
    exact ⟨z, hz_eq ▸ hz₀_ball⟩
  obtain ⟨z, hz⟩ := hexists
  rw [show algebraMap F w.adicCompletion z = ((z : F) : w.adicCompletion) from rfl] at hz

  have hz_val_le : w.heightOneSpectrum.valuation F z ≤ 1 := by
    have hzhat : Valued.v ((z : w.adicCompletion)) ≤ (1 : ℤᵐ⁰) := by
      calc Valued.v ((z : w.adicCompletion))
          = Valued.v (((z : w.adicCompletion) - y.val) + y.val) := by ring_nf
        _ ≤ max (Valued.v ((z : w.adicCompletion) - y.val)) (Valued.v y.val) :=
            Valuation.map_add _ _ _
        _ ≤ (1 : ℤᵐ⁰) := max_le
            (hz.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)))
            y.2
    rwa [valuedAdicCompletion_eq_valuation'] at hzhat
  have hz_mem : z ∈ (O_w : ValuationSubring F) := by
    obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one F z
      (fun v' => by
        obtain rfl : v' = w.heightOneSpectrum := Subsingleton.elim _ _
        exact hz_val_le)
    exact hr ▸ r.2
  refine ⟨⟨z, hz_mem⟩, ?_⟩
  rw [adicCompletion.mem_completionIdeal_pow, ← WithZero.exp_eq_coe_ofAdd]
  have hsub : (y - algebraMap (O_w) (O_W) ⟨z, hz_mem⟩ : O_W).val
      = y.val - ((z : F) : w.adicCompletion) := rfl
  rw [hsub, Valuation.map_sub_swap]
  exact hz

def kwF4R1V410a_quotientEquiv (n : ℕ) :
    (O_w) ⧸ (𝔪_w) ^ n ≃+* (O_W) ⧸ (𝔪_W) ^ n :=
  RingEquiv.ofBijective
    (Ideal.quotientMap _ (algebraMap (O_w) (O_W))
      (fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mpr hx))
    ⟨Ideal.quotientMap_injective'
      (fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mp
        (Ideal.mem_comap.mp hx)),
    fun y => by
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hx⟩ := kwF4R1V410a_exists_sub_mem_completionIdeal_pow w n y'
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [Ideal.quotientMap_mk]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by
        rw [← neg_sub, neg_mem_iff]; exact hx)⟩

theorem kwF4R1V410a_quotientEquiv_mk (n : ℕ) (x : O_w) :
    kwF4R1V410a_quotientEquiv w n (Ideal.Quotient.mk _ x)
      = Ideal.Quotient.mk _ (algebraMap (O_w) (O_W) x) := rfl

end Bridge
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve"

end ModularCurve.KwF4R1V410a
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem coe_smul_K (c : K) (x : u.adicCompletionIntegers) :
    ((c • x : u.adicCompletionIntegers) : u.adicCompletion) = c • (x : u.adicCompletion) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

def poleWindowShift (πh : u.adicCompletionIntegers) (M : ℕ) :
    poleWindowKSubmod u πh M →ₗ[K] u.adicCompletionIntegers where
  toFun x := ⟨(πh : u.adicCompletion)^M * (x : u.adicCompletion), x.2⟩
  map_add' x y := by apply Subtype.ext; push_cast; ring
  map_smul' c x := by
    apply Subtype.ext
    rw [coe_smul_K]
    show (πh : u.adicCompletion)^M * (c • (x : u.adicCompletion))
        = c • ((πh : u.adicCompletion)^M * (x : u.adicCompletion))
    rw [mul_smul_comm]

theorem poleWindowShift_injective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Injective (poleWindowShift u πh M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz
    exact hπh.ne_zero (Subtype.ext hz)
  have hx0 : (x : u.adicCompletion) = 0 := by
    have := congrArg Subtype.val hx
    push_cast at this
    exact (mul_eq_zero.mp this).resolve_left hπhM0
  exact Subtype.ext hx0

theorem poleWindowShift_surjective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Surjective (poleWindowShift u πh M) := by
  intro y
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz; exact hπh.ne_zero (Subtype.ext hz)
  refine ⟨⟨(y : u.adicCompletion) / (πh : u.adicCompletion)^M, ?_⟩, ?_⟩
  · rw [mem_poleWindowKSubmod_iff, mul_div_cancel₀ _ hπhM0]; exact y.2
  · apply Subtype.ext
    show (πh : u.adicCompletion)^M * ((y : u.adicCompletion) / (πh : u.adicCompletion)^M)
        = (y : u.adicCompletion)
    rw [mul_div_cancel₀ _ hπhM0]

def poleWindowShiftEquiv (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    poleWindowKSubmod u πh M ≃ₗ[K] u.adicCompletionIntegers :=
  LinearEquiv.ofBijective (poleWindowShift u πh M)
    ⟨poleWindowShift_injective u πh hπh M, poleWindowShift_surjective u πh hπh M⟩

def piPowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletionIntegers where
  carrier := {y | ∃ x : u.adicCompletionIntegers, y = πh^M * x}
  add_mem' := by rintro a b ⟨xa, rfl⟩ ⟨xb, rfl⟩; exact ⟨xa + xb, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  smul_mem' c y := by
    rintro ⟨x, rfl⟩
    exact ⟨c • x, by rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩

theorem poleWindowShift_image_integers (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule.map (poleWindowShift u πh M)
        ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
      = piPowKSubmod u πh M := by
  ext y
  constructor
  · rintro ⟨⟨x, hxP⟩, hxA, rfl⟩
    refine ⟨⟨(x : u.adicCompletion), hxA⟩, ?_⟩
    apply Subtype.ext; push_cast; rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : u.adicCompletion),
      adicIntegersKSubmod_le_poleWindowKSubmod u πh M x.2⟩, x.2, ?_⟩
    apply Subtype.ext; push_cast; rfl

variable (K L) in

def KwF4gRRTateDVRQuotPowKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)

theorem kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (hDVR : KwF4gRRTateDVRQuotPowKFinite K L) :
    KwF4gRRTatePoleWindowFinite K L := by
  intro u _ πh hπh M
  haveI := hDVR u πh hπh M

  have e := (poleWindowShiftEquiv u πh hπh M).toLinearMap
  let e' := Submodule.Quotient.equiv
    ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
    (piPowKSubmod u πh M)
    (poleWindowShiftEquiv u πh hπh M)
    (poleWindowShift_image_integers u πh M)
  exact FiniteDimensional.of_injective e'.toLinearMap e'.injective

end PoleWindowShift
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section FinrankTraceCyclicity

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem range_comp_map_left (f : M →ₗ[K] N) (g : N →ₗ[K] M) :
    ∀ x ∈ LinearMap.range (g ∘ₗ f), f x ∈ LinearMap.range (f ∘ₗ g) := by
  rintro x ⟨y, rfl⟩
  exact ⟨f y, rfl⟩

theorem finrankTrace_comp_comm (f : M →ₗ[K] N) (g : N →ₗ[K] M)
    [FiniteDimensional K (LinearMap.range (g ∘ₗ f))]
    [FiniteDimensional K (LinearMap.range (f ∘ₗ g))] :
    finrankTrace (g ∘ₗ f) = finrankTrace (f ∘ₗ g) := by
  set W := LinearMap.range (g ∘ₗ f)
  set W' := LinearMap.range (f ∘ₗ g)

  let fR : W →ₗ[K] W' := f.restrict (range_comp_map_left f g)
  let gR : W' →ₗ[K] W := g.restrict (range_comp_map_left g f)

  have hgf : (g ∘ₗ f).restrict (fun x _ => LinearMap.mem_range_self _ x) = gR ∘ₗ fR := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  have hfg : (f ∘ₗ g).restrict (fun x _ => LinearMap.mem_range_self _ x) = fR ∘ₗ gR := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  unfold finrankTrace
  rw [hgf, hfg, LinearMap.trace_comp_comm']

end FinrankTraceCyclicity
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section TraceOnSuperspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrankTrace_eq_trace_on_superspace
    (φ : V →ₗ[K] V) (W : Submodule K V) [FiniteDimensional K W]
    (hrange : LinearMap.range φ ≤ W) (hW : ∀ x ∈ W, φ x ∈ W) :
    haveI : FiniteDimensional K (LinearMap.range φ) :=
      Submodule.finiteDimensional_of_le hrange
    finrankTrace φ = LinearMap.trace K W (φ.restrict hW) := by
  haveI : FiniteDimensional K (LinearMap.range φ) := Submodule.finiteDimensional_of_le hrange

  let i : LinearMap.range φ →ₗ[K] W := Submodule.inclusion hrange

  let π : W →ₗ[K] LinearMap.range φ :=
    { toFun := fun w => ⟨φ (w : V), LinearMap.mem_range_self φ (w : V)⟩
      map_add' := fun w₁ w₂ => by simp [Subtype.ext_iff]
      map_smul' := fun c w => by simp [Subtype.ext_iff] }

  have hip : i ∘ₗ π = φ.restrict hW := by
    apply LinearMap.ext; intro w; apply Subtype.ext; rfl

  have hpi : π ∘ₗ i = φ.restrict (fun x _ => LinearMap.mem_range_self φ x) := by
    apply LinearMap.ext; intro x; apply Subtype.ext; rfl
  unfold finrankTrace
  rw [← hpi, ← hip, LinearMap.trace_comp_comm']

end TraceOnSuperspace
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrankTrace_sub_eq
    (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    haveI : FiniteDimensional K
        ((LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V) : Type _) :=
      Submodule.finiteDimensional_sup _ _
    finrankTrace φ - finrankTrace ψ
      = LinearMap.trace K (LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V)
          ((φ - ψ).restrict
            (p := (LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V))
            (fun x _ => sub_mem
              (Submodule.mem_sup_left (LinearMap.mem_range_self φ x))
              (Submodule.mem_sup_right (LinearMap.mem_range_self ψ x)))) := by
  set W' : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ with hW'
  haveI : FiniteDimensional K W' := Submodule.finiteDimensional_sup _ _
  have hφW : ∀ x ∈ W', φ x ∈ W' := fun x _ =>
    Submodule.mem_sup_left (LinearMap.mem_range_self φ x)
  have hψW : ∀ x ∈ W', ψ x ∈ W' := fun x _ =>
    Submodule.mem_sup_right (LinearMap.mem_range_self ψ x)
  rw [finrankTrace_eq_trace_on_superspace φ W' le_sup_left hφW,
    finrankTrace_eq_trace_on_superspace ψ W' le_sup_right hψW,
    ← map_sub]

  refine congrArg (LinearMap.trace K W') (LinearMap.ext fun x => Subtype.ext ?_)
  rfl

end Additivity
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section DVRQuotDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem piPowKSubmod_eq_restrictScalars (πh : u.adicCompletionIntegers) (M : ℕ) :
    piPowKSubmod u πh M
      = (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, h⟩⟩

def quotPiPowEquivIdealQuot (πh : u.adicCompletionIntegers) (M : ℕ) :
    (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)
      ≃ₗ[K] (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) :=
  (Submodule.quotEquivOfEq _ _ (piPowKSubmod_eq_restrictScalars u πh M)).trans
    (Submodule.Quotient.restrictScalarsEquiv K _)

variable (K L) in

def KwF4gRRTateDVRCotangentKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh),
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))

theorem range_mulLeft_eq_restrictScalars_span (a : u.adicCompletionIntegers) :
    LinearMap.range (LinearMap.mulLeft K a)
      = (Ideal.span {a} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩

set_option maxHeartbeats 25600000 in

theorem finiteDimensional_restrictScalarsQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K (u.adicCompletionIntegers ⧸
      (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
  induction M with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Submodule.restrictScalars_top]
    infer_instance
  | succ M ih =>
    have hle : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)
        ≤ Ideal.span {πh^M} := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]; exact ⟨πh, rfl⟩
    have hle' : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K
        ≤ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K :=
      Submodule.restrictScalars_mono K hle

    set N : Submodule K (u.adicCompletionIntegers ⧸
        (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
      (Submodule.restrictScalars K (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)).map
        (Submodule.restrictScalars K (Ideal.span {πh^(M+1)} : Ideal _)).mkQ with hN_def

    haveI hquot : FiniteDimensional K
        ((u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal _).restrictScalars K) ⧸ N) := by
      haveI := ih
      exact Module.Finite.equiv
        (Submodule.quotientQuotientEquivQuotient _ _ hle').symm

    haveI hN : FiniteDimensional K N := by
      set φ : u.adicCompletionIntegers →ₗ[K] (u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
        (Submodule.restrictScalars K
            (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)).mkQ ∘ₗ
          LinearMap.mulLeft K (πh^M) with hφ_def
      have hrange : LinearMap.range φ = N := by
        rw [hφ_def, LinearMap.range_comp, range_mulLeft_eq_restrictScalars_span, hN_def]
      have hker : LinearMap.ker φ
          = (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K := by
        simp only [hφ_def, LinearMap.ker_comp, Submodule.ker_mkQ]
        ext x
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
          Ideal.mem_span_singleton]
        have hπM : (πh : u.adicCompletionIntegers)^M ≠ 0 := pow_ne_zero M hπh.ne_zero
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, mul_left_cancel₀ hπM (by rw [hc, pow_succ, mul_assoc])⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, by rw [hc, pow_succ, mul_assoc]⟩

      let e₁ : (u.adicCompletionIntegers ⧸
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K)
          ≃ₗ[K] (u.adicCompletionIntegers ⧸ LinearMap.ker φ) :=
        Submodule.quotEquivOfEq _ _ hker.symm
      let e₂ : (u.adicCompletionIntegers ⧸ LinearMap.ker φ) ≃ₗ[K] LinearMap.range φ :=
        φ.quotKerEquivRange
      let e₃ : (LinearMap.range φ : Submodule K _) ≃ₗ[K] N := LinearEquiv.ofEq _ _ hrange
      haveI hCK : FiniteDimensional K (u.adicCompletionIntegers ⧸
          (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
        haveI := hCot u πh hπh
        exact Module.Finite.equiv
          (Submodule.Quotient.restrictScalarsEquiv K
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers)).symm
      exact Module.Finite.equiv ((e₁.trans e₂).trans e₃)
    exact Module.Finite.of_submodule_quotient N

theorem finiteDimensional_idealQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) := by
  haveI := finiteDimensional_restrictScalarsQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K _)

theorem kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
    (hCot : KwF4gRRTateDVRCotangentKFinite K L) :
    KwF4gRRTateDVRQuotPowKFinite K L := by
  intro u _ πh hπh M
  haveI := finiteDimensional_idealQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (quotPiPowEquivIdealQuot u πh M).symm

end DVRQuotDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"
p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_tateChainRule.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_tateChainRule.IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section DVRCotangentDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

scoped instance instIsScalarTower_K_toValuationSubring_adicCompletionIntegers :
    IsScalarTower K u.toValuationSubring u.adicCompletionIntegers := by
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  apply Subtype.ext
  show algebraMap K u.adicCompletion k
    = (algebraMap u.toValuationSubring u.adicCompletionIntegers (algebraMap K _ k)).val
  rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
  rfl

theorem span_irreducible_eq_completionIdeal_pow_one
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (Ideal.span {πh} : Ideal u.adicCompletionIntegers)
      = (u.heightOneSpectrum.completionIdeal L) ^ 1 := by
  rw [pow_one, ← hπh.maximalIdeal_eq]

def quotientEquivKAlg (n : ℕ) :
    (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n)
      ≃ₐ[K] (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n) :=
  { kwF4R1V410a_quotientEquiv u n with
    commutes' := fun k => by
      show kwF4R1V410a_quotientEquiv u n (algebraMap K _ k) = algebraMap K _ k
      rw [IsScalarTower.algebraMap_apply K u.toValuationSubring
          (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n),
        Ideal.Quotient.algebraMap_eq, kwF4R1V410a_quotientEquiv_mk,
        IsScalarTower.algebraMap_apply K u.adicCompletionIntegers
          (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n),
        Ideal.Quotient.algebraMap_eq,
        IsScalarTower.algebraMap_apply K u.toValuationSubring u.adicCompletionIntegers] }

def quotSpanIrreducibleEquivResidueField (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))
      ≃ₗ[K] u.ResidueField :=
  (Ideal.quotientEquivAlgOfEq K
      (span_irreducible_eq_completionIdeal_pow_one u πh hπh)).toLinearEquiv.trans
    ((quotientEquivKAlg u 1).symm.toLinearEquiv.trans
      (Ideal.quotientEquivAlgOfEq K
        (pow_one (IsLocalRing.maximalIdeal u.toValuationSubring))).toLinearEquiv)

theorem kwF4gRRTate_DVRCotangentKFinite : KwF4gRRTateDVRCotangentKFinite K L := by
  intro u _ πh hπh
  haveI : Module.Finite K u.ResidueField := FiniteResidue.finite
  exact Module.Finite.equiv (quotSpanIrreducibleEquivResidueField u πh hπh).symm

end DVRCotangentDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section DeltaQuotFactor

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {pA pA' : V →ₗ[K] V}

end DeltaQuotFactor
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section TermRangeFinite

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

def KwF4gRRTatePoleWindowImageFinite : Prop :=
  ∀ (fh : u.adicCompletion),
    FiniteDimensional K (Submodule.map (adicIntegersKSubmod u).mkQ
      (Submodule.map (lmulK u fh) (adicIntegersKSubmod u)))

end TermRangeFinite
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section DiffTraceZero

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

end DiffTraceZero
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section Composite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem kwF4gRRTate_poleWindowFinite : KwF4gRRTatePoleWindowFinite K L :=
  kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
      kwF4gRRTate_DVRCotangentKFinite)

end Composite
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section Subset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem lmul_adicIntegers_subset_poleWindow (fh : u.adicCompletion)
    (πh : u.adicCompletionIntegers) (M : ℕ)
    (hfhM : (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers) :
    Submodule.map (lmulK u fh) (adicIntegersKSubmod u) ≤ poleWindowKSubmod u πh M := by
  rintro x ⟨a, ha, rfl⟩

  rw [mem_poleWindowKSubmod_iff]
  show (πh : u.adicCompletion)^M * (lmulK u fh) a ∈ u.adicCompletionIntegers
  have : (lmulK u fh) a = fh * a := rfl
  rw [this, ← mul_assoc]
  exact mul_mem hfhM (show a ∈ u.adicCompletionIntegers from ha)

end Subset
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section Discharge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

theorem kwF4gRRTate_poleWindowImageFinite :
    KwF4gRRTatePoleWindowImageFinite u := by
  intro fh
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hfhM⟩ := kwF4gRRTate_clearPole u πh hπh fh

  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  have hsub : Submodule.map A.mkQ (Submodule.map (lmulK u fh) A)
      ≤ Submodule.map A.mkQ P :=
    Submodule.map_mono (lmul_adicIntegers_subset_poleWindow u fh πh M hfhM)

  suffices hPim : FiniteDimensional K (Submodule.map A.mkQ P : Submodule K _) by
    exact Submodule.finiteDimensional_of_le hsub

  haveI : FiniteDimensional K (P ⧸ (A.comap P.subtype)) :=
    kwF4gRRTate_poleWindowFinite (K := K) (L := L) u πh hπh M
  let r : P →ₗ[K] (u.adicCompletion ⧸ A) := A.mkQ ∘ₗ P.subtype
  have hrange : LinearMap.range r = Submodule.map A.mkQ P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker r = A.comap P.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : (P ⧸ (A.comap P.subtype)) ≃ₗ[K] LinearMap.range r := hker ▸ r.quotKerEquivRange
  rw [← hrange]
  exact e.finiteDimensional

end Discharge
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrankTrace_congr {φ ψ : V →ₗ[K] V}
    [hφ : FiniteDimensional K (LinearMap.range φ)]
    [hψ : FiniteDimensional K (LinearMap.range ψ)]
    (h : φ = ψ) : finrankTrace φ = finrankTrace ψ := by
  subst h; rfl

theorem range_sub_le (φ ψ : V →ₗ[K] V) :
    LinearMap.range (φ - ψ) ≤ LinearMap.range φ ⊔ LinearMap.range ψ := by
  rintro x ⟨y, rfl⟩
  exact sub_mem (Submodule.mem_sup_left (mem_range_self φ y))
    (Submodule.mem_sup_right (mem_range_self ψ y))

scoped instance instFinDimRangeSub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ - ψ)) :=
  haveI : FiniteDimensional K
      ((LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V) : Type _) :=
    Submodule.finiteDimensional_sup _ _
  Submodule.finiteDimensional_of_le (range_sub_le φ ψ)

theorem finrankTrace_sub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace φ - finrankTrace ψ = finrankTrace (φ - ψ) := by
  set W' : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ
  haveI : FiniteDimensional K W' := Submodule.finiteDimensional_sup _ _
  have hφψW : ∀ x ∈ W', (φ - ψ) x ∈ W' := fun x _ =>
    sub_mem (Submodule.mem_sup_left (mem_range_self φ x))
      (Submodule.mem_sup_right (mem_range_self ψ x))
  rw [finrankTrace_sub_eq φ ψ,
    finrankTrace_eq_trace_on_superspace (φ - ψ) W' (range_sub_le φ ψ) hφψW]

end Additivity
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section ConjInvariance

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
variable [AddCommGroup N] [Module K N]

end ConjInvariance
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section TermMaps

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def alphaMap (c : u.adicCompletion) :
    LinearMap.range (tateProj u) →ₗ[K] (u.adicCompletion ⧸ LinearMap.range (tateProj u)) :=
  (LinearMap.range (tateProj u)).mkQ ∘ₗ lmulK u c ∘ₗ (LinearMap.range (tateProj u)).subtype

variable [u.FiniteResidue]

theorem finiteDimensional_range_alphaMap (c : u.adicCompletion) :
    FiniteDimensional K (LinearMap.range (alphaMap u c)) := by

  haveI hF21 := kwF4gRRTate_poleWindowImageFinite u c
  set Q1 := u.adicCompletion ⧸ LinearMap.range (tateProj u)
  set Q2 := u.adicCompletion ⧸ adicIntegersKSubmod u
  let eQ : Q1 ≃ₗ[K] Q2 := Submodule.quotEquivOfEq _ _ (range_tateProj u)

  have hmap : (LinearMap.range (alphaMap u c)).map (eQ : Q1 →ₗ[K] Q2)
      = Submodule.map (adicIntegersKSubmod u).mkQ
          (Submodule.map (lmulK u c) (adicIntegersKSubmod u)) := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := hy
      refine ⟨c * (a : u.adicCompletion), ⟨(a : u.adicCompletion), ?_, rfl⟩, ?_⟩
      · exact (range_tateProj u) ▸ a.2
      · rfl
    · rintro x ⟨y, ⟨av, hav, rfl⟩, rfl⟩
      refine ⟨alphaMap u c ⟨av, (range_tateProj u).symm ▸ hav⟩, ⟨_, rfl⟩, ?_⟩
      rfl
  have : FiniteDimensional K
      ((LinearMap.range (alphaMap u c)).map (eQ : Q1 →ₗ[K] Q2)) := by
    rw [hmap]; exact hF21
  exact (Submodule.equivMapOfInjective (eQ : Q1 →ₗ[K] Q2) eQ.injective
    (LinearMap.range (alphaMap u c))).symm.finiteDimensional

end TermMaps
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section Cyclicity

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]
variable {pA' : u.adicCompletion →ₗ[K] u.adicCompletion}

end Cyclicity
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [∀ u : Place K L, u.FiniteResidue]

end Headline
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

scoped instance instFinDimRangeNeg (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    FiniteDimensional K (LinearMap.range (-φ)) := by
  have h : LinearMap.range (-φ) = LinearMap.range φ := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩; exact ⟨-y, by simp⟩
    · rintro x ⟨y, rfl⟩; exact ⟨-y, by simp⟩
  rw [h]; infer_instance

scoped instance instFinDimRangeZero : FiniteDimensional K (LinearMap.range (0 : V →ₗ[K] V)) := by
  rw [LinearMap.range_zero]; infer_instance

theorem finrankTrace_zero : finrankTrace (0 : V →ₗ[K] V) = 0 := by
  unfold finrankTrace
  have hrest : (0 : V →ₗ[K] V).restrict
      (p := LinearMap.range (0 : V →ₗ[K] V))
      (fun x _ => LinearMap.mem_range_self _ x) = 0 := by
    apply LinearMap.ext; intro; apply Subtype.ext; rfl
  rw [hrest, _root_.map_zero]

theorem finrankTrace_neg (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    finrankTrace (-φ) = -finrankTrace φ := by
  have hsub := finrankTrace_sub (0 : V →ₗ[K] V) φ
  rw [finrankTrace_zero, zero_sub] at hsub
  calc finrankTrace (-φ) = finrankTrace ((0 : V →ₗ[K] V) - φ) :=
        finrankTrace_congr (zero_sub φ).symm
    _ = -finrankTrace φ := hsub.symm

scoped instance instFinDimRangeAdd (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ + ψ)) := by
  rw [show φ + ψ = φ - (-ψ) from (sub_neg_eq_add φ ψ).symm]
  exact instFinDimRangeSub φ (-ψ)

theorem finrankTrace_add (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace (φ + ψ) = finrankTrace φ + finrankTrace ψ := by
  have h := finrankTrace_sub φ (-ψ)
  rw [finrankTrace_neg, sub_neg_eq_add] at h
  calc finrankTrace (φ + ψ) = finrankTrace (φ - (-ψ)) :=
        finrankTrace_congr (sub_neg_eq_add φ ψ).symm
    _ = finrankTrace φ + finrankTrace ψ := h.symm

end Additivity
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section TateCommAddFst

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V) :
    tateComm pA (φ₁ + φ₂) ψ = tateComm pA φ₁ ψ + tateComm pA φ₂ ψ := by
  unfold tateComm
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
  abel

theorem tateCommRestrict_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V) :
    tateCommRestrict pA (φ₁ + φ₂) ψ
      = tateCommRestrict pA φ₁ ψ + tateCommRestrict pA φ₂ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA (φ₁ + φ₂) ψ a : V)
    = (tateCommRestrict pA φ₁ ψ a : V) + (tateCommRestrict pA φ₂ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply, tateCommRestrict_apply]
  exact congrFun (congrArg DFunLike.coe (tateComm_add_fst pA φ₁ φ₂ ψ)) (a : V)

theorem tateCommTrace_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ₁ ψ))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ₂ ψ))] :
    haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA (φ₁ + φ₂) ψ)) := by
      rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
    tateCommTrace pA (φ₁ + φ₂) ψ = tateCommTrace pA φ₁ ψ + tateCommTrace pA φ₂ ψ := by
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA (φ₁ + φ₂) ψ)) := by
    rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  unfold tateCommTrace
  rw [← finrankTrace_add]
  exact finrankTrace_congr (tateCommRestrict_add_fst pA φ₁ φ₂ ψ)

end TateCommAddFst
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section TateResAddFst

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem tateRes_add_fst (fh₁ fh₂ gh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁) (lmulK u gh)))]
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₂) (lmulK u gh)))] :
    haveI : FiniteDimensional K (LinearMap.range
        (tateCommRestrict (tateProj u) (lmulK u (fh₁ + fh₂)) (lmulK u gh))) := by
      have heq : lmulK u (fh₁ + fh₂) = lmulK u fh₁ + lmulK u fh₂ := map_add _ _ _
      rw [heq, tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
    tateRes u (fh₁ + fh₂) gh = tateRes u fh₁ gh + tateRes u fh₂ gh := by
  have heq : lmulK u (fh₁ + fh₂) = lmulK u fh₁ + lmulK u fh₂ := map_add _ _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u (fh₁ + fh₂)) (lmulK u gh))) := by
    rw [heq, tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁ + lmulK u fh₂) (lmulK u gh))) := by
    rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  unfold tateRes
  have hct := tateCommTrace_add_fst (tateProj u) (lmulK u fh₁) (lmulK u fh₂) (lmulK u gh)
  unfold tateCommTrace at hct ⊢
  rw [← hct]
  exact finrankTrace_congr (by rw [heq])

end TateResAddFst
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section CohenMint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

end CohenMint
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section Reprice

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable [∀ u : Place K L, u.FiniteResidue]

end Reprice
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section AddSnd

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_add_snd (pA φ ψ₁ ψ₂ : V →ₗ[K] V) :
    tateComm pA φ (ψ₁ + ψ₂) = tateComm pA φ ψ₁ + tateComm pA φ ψ₂ := by
  unfold tateComm
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
  abel

theorem tateCommRestrict_add_snd (pA φ ψ₁ ψ₂ : V →ₗ[K] V) :
    tateCommRestrict pA φ (ψ₁ + ψ₂)
      = tateCommRestrict pA φ ψ₁ + tateCommRestrict pA φ ψ₂ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA φ (ψ₁ + ψ₂) a : V)
    = (tateCommRestrict pA φ ψ₁ a : V) + (tateCommRestrict pA φ ψ₂ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply, tateCommRestrict_apply]
  exact congrFun (congrArg DFunLike.coe (tateComm_add_snd pA φ ψ₁ ψ₂)) (a : V)

theorem tateCommTrace_add_snd (pA φ ψ₁ ψ₂ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ₁))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ₂))] :
    haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ (ψ₁ + ψ₂))) := by
      rw [tateCommRestrict_add_snd]; exact instFinDimRangeAdd _ _
    tateCommTrace pA φ (ψ₁ + ψ₂) = tateCommTrace pA φ ψ₁ + tateCommTrace pA φ ψ₂ := by
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ (ψ₁ + ψ₂))) := by
    rw [tateCommRestrict_add_snd]; exact instFinDimRangeAdd _ _
  unfold tateCommTrace
  rw [← finrankTrace_add]
  exact finrankTrace_congr (tateCommRestrict_add_snd pA φ ψ₁ ψ₂)

end AddSnd
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section CommutatorVanish

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

scoped instance instFinDimRangeCompRight (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ ∘ₗ ψ)) := by
  rw [LinearMap.range_comp]; infer_instance

scoped instance instFinDimRangeCompLeft (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (ψ ∘ₗ φ)) :=
  Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)

theorem finrankTrace_commutator_eq_zero (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace (φ ∘ₗ ψ - ψ ∘ₗ φ) = 0 := by
  rw [← finrankTrace_sub, finrankTrace_comp_comm ψ φ, sub_self]

end CommutatorVanish
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section LeibnizAbstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def piRestrict (pA φ : V →ₗ[K] V) : LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (pA ∘ₗ φ).restrict (fun x _ => LinearMap.mem_range_self pA (φ x))

theorem piRestrict_apply (pA φ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (piRestrict pA φ a : V) = pA (φ (a : V)) := rfl

def epsRestrict (pA φ ψ : V →ₗ[K] V) : LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (pA ∘ₗ φ ∘ₗ (LinearMap.id - pA) ∘ₗ ψ).restrict
    (fun x _ => LinearMap.mem_range_self pA _)

theorem epsRestrict_apply (pA φ ψ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (epsRestrict pA φ ψ a : V) = pA (φ (ψ (a : V) - pA (ψ (a : V)))) := by
  show pA (φ ((LinearMap.id (R := K) (M := V) - pA) (ψ (a : V)))) = _
  rw [LinearMap.sub_apply, LinearMap.id_apply]

theorem piRestrict_comp_eq (pA φ ψ : V →ₗ[K] V) :
    piRestrict pA (φ ∘ₗ ψ) = piRestrict pA φ ∘ₗ piRestrict pA ψ + epsRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext

  show pA (φ (ψ (a : V))) = pA (φ (pA (ψ (a : V)))) + (epsRestrict pA φ ψ a : V)
  rw [epsRestrict_apply, ← map_add, ← map_add]
  congr 2
  abel

theorem tateCommRestrict_eq_bracket (pA f g : V →ₗ[K] V) :
    tateCommRestrict pA f g
      = piRestrict pA f ∘ₗ piRestrict pA g - piRestrict pA g ∘ₗ piRestrict pA f := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  simp only [LinearMap.sub_apply, AddSubgroupClass.coe_sub, LinearMap.comp_apply]
  rw [tateCommRestrict_apply, tateComm_apply, piRestrict_apply, piRestrict_apply,
    piRestrict_apply, piRestrict_apply]

theorem bracket_leibniz_defect {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (F G H : W →ₗ[R] W) :
    (F ∘ₗ (G ∘ₗ H) - (G ∘ₗ H) ∘ₗ F)
      - ((F ∘ₗ G) ∘ₗ H - H ∘ₗ (F ∘ₗ G))
      - ((F ∘ₗ H) ∘ₗ G - G ∘ₗ (F ∘ₗ H))
      = G ∘ₗ (F ∘ₗ H - H ∘ₗ F) - (F ∘ₗ H - H ∘ₗ F) ∘ₗ G := by
  apply LinearMap.ext; intro x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

theorem tateCommTrace_leibniz_snd (pA f g h : V →ₗ[K] V)
    (hfin_fh : FiniteDimensional K (LinearMap.range (tateCommRestrict pA f h)))
    (hfin_gh : FiniteDimensional K (LinearMap.range (epsRestrict pA g h)))
    (hfin_fg : FiniteDimensional K (LinearMap.range (epsRestrict pA f g)))
    (hfin_fh' : FiniteDimensional K (LinearMap.range (epsRestrict pA f h)))
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA f (g ∘ₗ h)))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA (f ∘ₗ g) h))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA (f ∘ₗ h) g))] :
    tateCommTrace pA f (g ∘ₗ h)
      = tateCommTrace pA (f ∘ₗ g) h + tateCommTrace pA (f ∘ₗ h) g := by
  set A := LinearMap.range pA
  set F := piRestrict pA f
  set G := piRestrict pA g
  set H := piRestrict pA h
  set εgh := epsRestrict pA g h
  set εfg := epsRestrict pA f g
  set εfh := epsRestrict pA f h
  set CFH := F ∘ₗ H - H ∘ₗ F
  haveI : FiniteDimensional K (LinearMap.range εgh) := hfin_gh
  haveI : FiniteDimensional K (LinearMap.range εfg) := hfin_fg
  haveI : FiniteDimensional K (LinearMap.range εfh) := hfin_fh'
  haveI hCFH : FiniteDimensional K (LinearMap.range CFH) := by
    have : CFH = tateCommRestrict pA f h := (tateCommRestrict_eq_bracket pA f h).symm
    rw [this]; exact hfin_fh

  have hLHS : tateCommRestrict pA f (g ∘ₗ h)
      = (F ∘ₗ (G ∘ₗ H) - (G ∘ₗ H) ∘ₗ F)
        + (F ∘ₗ εgh - εgh ∘ₗ F) := by
    rw [tateCommRestrict_eq_bracket, piRestrict_comp_eq]
    show piRestrict pA f ∘ₗ (piRestrict pA g ∘ₗ piRestrict pA h + epsRestrict pA g h)
        - (piRestrict pA g ∘ₗ piRestrict pA h + epsRestrict pA g h) ∘ₗ piRestrict pA f = _
    apply LinearMap.ext; intro a
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
    abel
  have hRHS₁ : tateCommRestrict pA (f ∘ₗ g) h
      = ((F ∘ₗ G) ∘ₗ H - H ∘ₗ (F ∘ₗ G))
        + (εfg ∘ₗ H - H ∘ₗ εfg) := by
    rw [tateCommRestrict_eq_bracket, piRestrict_comp_eq]
    show (piRestrict pA f ∘ₗ piRestrict pA g + epsRestrict pA f g) ∘ₗ piRestrict pA h
        - piRestrict pA h ∘ₗ (piRestrict pA f ∘ₗ piRestrict pA g + epsRestrict pA f g) = _
    apply LinearMap.ext; intro a
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
    abel
  have hRHS₂ : tateCommRestrict pA (f ∘ₗ h) g
      = ((F ∘ₗ H) ∘ₗ G - G ∘ₗ (F ∘ₗ H))
        + (εfh ∘ₗ G - G ∘ₗ εfh) := by
    rw [tateCommRestrict_eq_bracket, piRestrict_comp_eq]
    show (piRestrict pA f ∘ₗ piRestrict pA h + epsRestrict pA f h) ∘ₗ piRestrict pA g
        - piRestrict pA g ∘ₗ (piRestrict pA f ∘ₗ piRestrict pA h + epsRestrict pA f h) = _
    apply LinearMap.ext; intro a
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
    abel

  have hDefect : tateCommRestrict pA f (g ∘ₗ h)
      - tateCommRestrict pA (f ∘ₗ g) h - tateCommRestrict pA (f ∘ₗ h) g
      = (G ∘ₗ CFH - CFH ∘ₗ G)
        + (F ∘ₗ εgh - εgh ∘ₗ F)
        - (εfg ∘ₗ H - H ∘ₗ εfg)
        - (εfh ∘ₗ G - G ∘ₗ εfh) := by
    rw [hLHS, hRHS₁, hRHS₂]
    have := bracket_leibniz_defect (R := K) F G H
    show _ = (G ∘ₗ CFH - CFH ∘ₗ G) + _ - _ - _
    rw [show G ∘ₗ CFH - CFH ∘ₗ G
      = (F ∘ₗ (G ∘ₗ H) - (G ∘ₗ H) ∘ₗ F)
        - ((F ∘ₗ G) ∘ₗ H - H ∘ₗ (F ∘ₗ G))
        - ((F ∘ₗ H) ∘ₗ G - G ∘ₗ (F ∘ₗ H)) from this.symm]
    abel

  have hT1 : finrankTrace (G ∘ₗ CFH - CFH ∘ₗ G) = 0 :=
    finrankTrace_commutator_eq_zero G CFH
  have hT2 : finrankTrace (F ∘ₗ εgh - εgh ∘ₗ F) = 0 :=
    finrankTrace_commutator_eq_zero F εgh
  have hT3' : finrankTrace (H ∘ₗ εfg - εfg ∘ₗ H) = 0 :=
    finrankTrace_commutator_eq_zero H εfg
  have hT3 : finrankTrace (εfg ∘ₗ H - H ∘ₗ εfg) = 0 := by
    have hneg : εfg ∘ₗ H - H ∘ₗ εfg = -(H ∘ₗ εfg - εfg ∘ₗ H) := by abel
    rw [show finrankTrace (εfg ∘ₗ H - H ∘ₗ εfg)
        = finrankTrace (-(H ∘ₗ εfg - εfg ∘ₗ H)) from finrankTrace_congr hneg,
      finrankTrace_neg, hT3', _root_.neg_zero]
  have hT4' : finrankTrace (G ∘ₗ εfh - εfh ∘ₗ G) = 0 :=
    finrankTrace_commutator_eq_zero G εfh
  have hT4 : finrankTrace (εfh ∘ₗ G - G ∘ₗ εfh) = 0 := by
    have hneg : εfh ∘ₗ G - G ∘ₗ εfh = -(G ∘ₗ εfh - εfh ∘ₗ G) := by abel
    rw [show finrankTrace (εfh ∘ₗ G - G ∘ₗ εfh)
        = finrankTrace (-(G ∘ₗ εfh - εfh ∘ₗ G)) from finrankTrace_congr hneg,
      finrankTrace_neg, hT4', _root_.neg_zero]

  unfold tateCommTrace
  set L := tateCommRestrict pA f (g ∘ₗ h)
  set R₁ := tateCommRestrict pA (f ∘ₗ g) h
  set R₂ := tateCommRestrict pA (f ∘ₗ h) g

  set D := L - R₁ - R₂ with hDdef
  haveI : FiniteDimensional K (LinearMap.range D) := by
    rw [hDdef]; exact instFinDimRangeSub _ _
  have hDtrace : finrankTrace D = 0 := by
    rw [finrankTrace_congr hDefect]

    set T1 := G ∘ₗ CFH - CFH ∘ₗ G
    set T2 := F ∘ₗ εgh - εgh ∘ₗ F
    set T3 := εfg ∘ₗ H - H ∘ₗ εfg
    set T4 := εfh ∘ₗ G - G ∘ₗ εfh
    haveI : FiniteDimensional K (LinearMap.range T1) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range T2) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range T3) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range T4) := instFinDimRangeSub _ _
    haveI : FiniteDimensional K (LinearMap.range (T1 + T2)) := instFinDimRangeAdd _ _
    haveI : FiniteDimensional K (LinearMap.range (T1 + T2 - T3)) := instFinDimRangeSub _ _
    calc finrankTrace (T1 + T2 - T3 - T4)
        = finrankTrace (T1 + T2 - T3) - finrankTrace T4 := (finrankTrace_sub _ _).symm
      _ = finrankTrace (T1 + T2) - finrankTrace T3 - finrankTrace T4 := by
          rw [(finrankTrace_sub (T1 + T2) T3).symm]
      _ = finrankTrace T1 + finrankTrace T2 - finrankTrace T3 - finrankTrace T4 := by
          rw [finrankTrace_add T1 T2]
      _ = 0 := by rw [hT1, hT2, hT3, hT4]; ring

  have hLdecomp : L = R₁ + R₂ + D := by rw [hDdef]; abel
  rw [finrankTrace_congr hLdecomp, finrankTrace_add, finrankTrace_add, hDtrace, add_zero]

end LeibnizAbstract
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section TateResLeibniz

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

theorem finiteDimensional_range_epsRestrict_lmulK (φ ψ : u.adicCompletion) :
    FiniteDimensional K (LinearMap.range
      (epsRestrict (tateProj u) (lmulK u φ) (lmulK u ψ))) := by

  haveI hα := finiteDimensional_range_alphaMap u ψ

  set pA := tateProj u
  set β : (u.adicCompletion ⧸ LinearMap.range pA) →ₗ[K] LinearMap.range pA :=
    (LinearMap.range pA).liftQ
      ((pA ∘ₗ lmulK u φ ∘ₗ (LinearMap.id - pA)).codRestrict (LinearMap.range pA)
        (fun x => LinearMap.mem_range_self pA _))
      (by
        rintro x ⟨y, rfl⟩
        apply Subtype.ext
        show (pA ∘ₗ lmulK u φ ∘ₗ (LinearMap.id - pA)) (pA y) = (0 : u.adicCompletion)
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
        rw [show pA (pA y) = pA y from congrFun (congrArg DFunLike.coe (tateProj_idem u)) y,
          sub_self, _root_.map_zero, _root_.map_zero])
    with hβdef

  have hfactor : epsRestrict pA (lmulK u φ) (lmulK u ψ) = β ∘ₗ alphaMap u ψ := by
    apply LinearMap.ext; intro a; apply Subtype.ext
    rw [epsRestrict_apply]
    rfl
  rw [hfactor, LinearMap.range_comp]
  infer_instance

theorem tateRes_leibniz_snd (hfin : KwF4gRRTateCommFinite K L)
    (f g h : u.adicCompletion) :
    haveI := hfin u f (g * h)
    haveI := hfin u (f * g) h
    haveI := hfin u (f * h) g
    tateRes u f (g * h) = tateRes u (f * g) h + tateRes u (f * h) g := by
  haveI := hfin u f (g * h)
  haveI := hfin u (f * g) h
  haveI := hfin u (f * h) g
  haveI := hfin u f h

  have hlmul : ∀ x y : u.adicCompletion, lmulK u (x * y) = lmulK u x ∘ₗ lmulK u y := by
    intro x y
    apply LinearMap.ext; intro z
    show (x * y) * z = x * (y * z)
    ring

  haveI hL : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f) (lmulK u g ∘ₗ lmulK u h))) := by
    rw [← hlmul g h]; exact hfin u f (g * h)
  haveI hR₁ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f ∘ₗ lmulK u g) (lmulK u h))) := by
    rw [← hlmul f g]; exact hfin u (f * g) h
  haveI hR₂ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f ∘ₗ lmulK u h) (lmulK u g))) := by
    rw [← hlmul f h]; exact hfin u (f * h) g

  have hleib := tateCommTrace_leibniz_snd (tateProj u) (lmulK u f) (lmulK u g) (lmulK u h)
    (hfin u f h)
    (finiteDimensional_range_epsRestrict_lmulK u g h)
    (finiteDimensional_range_epsRestrict_lmulK u f g)
    (finiteDimensional_range_epsRestrict_lmulK u f h)

  unfold tateRes
  unfold tateCommTrace at hleib ⊢
  rw [finrankTrace_congr (by rw [hlmul g h] : tateCommRestrict (tateProj u) (lmulK u f)
        (lmulK u (g * h)) = tateCommRestrict (tateProj u) (lmulK u f)
        (lmulK u g ∘ₗ lmulK u h)),
    finrankTrace_congr (by rw [hlmul f g] : tateCommRestrict (tateProj u)
        (lmulK u (f * g)) (lmulK u h) = tateCommRestrict (tateProj u)
        (lmulK u f ∘ₗ lmulK u g) (lmulK u h)),
    finrankTrace_congr (by rw [hlmul f h] : tateCommRestrict (tateProj u)
        (lmulK u (f * h)) (lmulK u g) = tateCommRestrict (tateProj u)
        (lmulK u f ∘ₗ lmulK u h) (lmulK u g))]
  exact hleib

end TateResLeibniz
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section TateResCongr

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem tateRes_congr_fst {fh₁ fh₂ gh : u.adicCompletion} (heq : fh₁ = fh₂)
    [h₁ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁) (lmulK u gh)))]
    [h₂ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₂) (lmulK u gh)))] :
    tateRes u fh₁ gh = tateRes u fh₂ gh := by
  subst heq; rfl

end TateResCongr
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section DerivationFactor

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def KwF4gRRTateDerivationFactorSnd [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]
    (hfinF : KwF4gRRTateCommFinite K F) : Prop :=
  ∀ (w : Place K F) [w.DCoordGenerates] (f : w.adicCompletion) (g : F),
    haveI := hfinF w f (algebraMap F w.adicCompletion g)
    haveI := hfinF w (f * algebraMap F w.adicCompletion
      (w.differentialCoeff (KaehlerDifferential.D K F g)))
      (algebraMap F w.adicCompletion w.uniformizer)
    tateRes w f (algebraMap F w.adicCompletion g)
      = tateRes w (f * algebraMap F w.adicCompletion
          (w.differentialCoeff (KaehlerDifferential.D K F g)))
          (algebraMap F w.adicCompletion w.uniformizer)

end DerivationFactor
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section Reprice

variable {K F E : Type*} [Field K] [Field F] [Algebra K F]
variable [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

theorem kwF4gRRTate_chainRule_of_derivationFactor
    (hfinF : KwF4gRRTateCommFinite K F)
    (hDF : ∀ [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]],
      KwF4gRRTateDerivationFactorSnd K F hfinF) :
    KwF4gRRTateChainRule K F E hfinF := by
  intro _ _ _ _ _ v _ w _ _ fh

  have hDFw := hDF w fh (algebraMap E F v.uniformizer)

  have hker : KaehlerDifferential.D K F (algebraMap E F v.uniformizer)
      = kaehlerPullback K F E v.dCoord :=
    (kaehlerPullback_D (K := K) (F := F) (E := E) v.uniformizer).symm

  have hX : fh * algebraMap F w.adicCompletion
        (w.differentialCoeff (kaehlerPullback K F E v.dCoord))
      = fh * algebraMap F w.adicCompletion
        (w.differentialCoeff (KaehlerDifferential.D K F (algebraMap E F v.uniformizer))) := by
    rw [hker]
  haveI := hfinF w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
  haveI := hfinF w (fh * algebraMap F w.adicCompletion
    (w.differentialCoeff (KaehlerDifferential.D K F (algebraMap E F v.uniformizer))))
    (algebraMap F w.adicCompletion w.uniformizer)
  haveI := hfinF w (fh * algebraMap F w.adicCompletion
    (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
    (algebraMap F w.adicCompletion w.uniformizer)
  calc tateRes w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (KaehlerDifferential.D K F (algebraMap E F v.uniformizer))))
          (algebraMap F w.adicCompletion w.uniformizer) := hDFw
    _ = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
          (algebraMap F w.adicCompletion w.uniformizer) := tateRes_congr_fst w hX.symm

end Reprice
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate"

section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_tateChainRule.LinearMap Submodule P2MW.S_AlgebraicCurve_tateChainRule.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V473a"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section DualDom

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def DualDom (w : Place K F) : Type _ := w.adicCompletion →ₗ[K] K

scoped instance (w : Place K F) : AddCommGroup (DualDom w) :=
  inferInstanceAs (AddCommGroup (w.adicCompletion →ₗ[K] K))

def DualDom.toLM {w : Place K F} (φ : DualDom w) : w.adicCompletion →ₗ[K] K := φ

@[scoped ext] theorem DualDom.ext {w : Place K F} {φ ψ : DualDom w}
    (h : ∀ x, φ.toLM x = ψ.toLM x) : φ = ψ := LinearMap.ext h

p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"
@[scoped simp] theorem DualDom.toLM_add {w : Place K F} (φ ψ : DualDom w) :
    (φ + ψ).toLM = φ.toLM + ψ.toLM := rfl

p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"
scoped instance (w : Place K F) : Module F (DualDom w) where
  smul h φ := φ.toLM ∘ₗ lmulK w (algebraMap F w.adicCompletion h)
  one_smul φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F w.adicCompletion 1 * x) = φ.toLM x
    rw [_root_.map_one, one_mul]
  mul_smul a b φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (a * b) * x) = φ.toLM (algebraMap F _ b * (algebraMap F _ a * x))
    rw [(algebraMap F w.adicCompletion).map_mul, mul_comm (algebraMap F _ a), mul_assoc]
  smul_zero a := DualDom.ext fun _ => rfl
  smul_add a φ ψ := DualDom.ext fun _ => rfl
  add_smul a b φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (a + b) * x)
      = φ.toLM (algebraMap F _ a * x) + φ.toLM (algebraMap F _ b * x)
    rw [(algebraMap F w.adicCompletion).map_add, add_mul, φ.toLM.map_add]
  zero_smul φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ 0 * x) = 0
    rw [(algebraMap F w.adicCompletion).map_zero, zero_mul, φ.toLM.map_zero]

@[scoped simp] theorem DualDom.smul_apply {w : Place K F} (h : F) (φ : DualDom w)
    (x : w.adicCompletion) :
    (h • φ).toLM x = φ.toLM (algebraMap F w.adicCompletion h * x) := rfl

p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"
scoped instance (w : Place K F) : Module K (DualDom w) :=
  inferInstanceAs (Module K (w.adicCompletion →ₗ[K] K))

theorem DualDom.k_smul_apply {w : Place K F} (c : K) (φ : DualDom w)
    (x : w.adicCompletion) :
    (c • φ).toLM x = c • φ.toLM x := rfl

scoped instance (w : Place K F) : IsScalarTower K F (DualDom w) where
  smul_assoc c h φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (c • h) * x) = c • φ.toLM (algebraMap F _ h * x)
    rw [Algebra.smul_def, (algebraMap F w.adicCompletion).map_mul,
      ← IsScalarTower.algebraMap_apply K F w.adicCompletion,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, φ.toLM.map_smul]

end DualDom
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

section GenericFactor

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Nontrivial Ω[F⁄K]]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]

theorem derivation_apply_eq_diffCoeff_smul (w : Place K F) [w.DCoordGenerates]
    (δ : Derivation K F M) (g : F) :
    δ g = w.differentialCoeff (KaehlerDifferential.D K F g) • δ w.uniformizer := by
  have hL := Derivation.liftKaehlerDifferential_comp_D δ
  have hLπ : δ.liftKaehlerDifferential w.dCoord = δ w.uniformizer := hL w.uniformizer
  calc δ g = δ.liftKaehlerDifferential (KaehlerDifferential.D K F g) := (hL g).symm
    _ = δ.liftKaehlerDifferential
        (w.differentialCoeff (KaehlerDifferential.D K F g) • w.dCoord) := by
          rw [w.differentialCoeff_smul_dCoord]
    _ = w.differentialCoeff (KaehlerDifferential.D K F g) • δ w.uniformizer := by
          rw [map_smul, hLπ]

end GenericFactor
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

section TateResDerivation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem range_smul_le {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) : LinearMap.range (c • φ) ≤ LinearMap.range φ := by
  rintro y ⟨x, rfl⟩
  exact (LinearMap.range φ).smul_mem c (LinearMap.mem_range_self φ x)

theorem finDimRangeSMul {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    FiniteDimensional K (LinearMap.range (c • φ)) :=
  Submodule.finiteDimensional_of_le (range_smul_le c φ)

theorem finrankTrace_smul {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    haveI := finDimRangeSMul c φ
    finrankTrace (c • φ) = c • finrankTrace φ := by
  haveI := finDimRangeSMul c φ
  have hW : ∀ x ∈ LinearMap.range φ, (c • φ) x ∈ LinearMap.range φ := fun x _ =>
    range_smul_le c φ (LinearMap.mem_range_self _ x)
  rw [finrankTrace_eq_trace_on_superspace (c • φ) (LinearMap.range φ) (range_smul_le c φ) hW]
  unfold finrankTrace
  rw [← LinearMap.map_smul]
  exact congrArg (LinearMap.trace K _) (LinearMap.ext fun x => Subtype.ext rfl)

theorem tateCommRestrict_smul_snd {V : Type*} [AddCommGroup V] [Module K V]
    (pA φ ψ : V →ₗ[K] V) (c : K) :
    tateCommRestrict pA φ (c • ψ) = c • tateCommRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA φ (c • ψ) a : V) = (c • tateCommRestrict pA φ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply]
  unfold tateComm
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
    smul_sub, Submodule.coe_smul]

theorem tateCommRestrict_smul_fst {V : Type*} [AddCommGroup V] [Module K V]
    (pA φ ψ : V →ₗ[K] V) (c : K) :
    tateCommRestrict pA (c • φ) ψ = c • tateCommRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA (c • φ) ψ a : V) = (c • tateCommRestrict pA φ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply]
  unfold tateComm
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
    smul_sub, Submodule.coe_smul]

theorem tateRes_congr_snd (u : Place K F) {fh gh₁ gh₂ : u.adicCompletion} (heq : gh₁ = gh₂)
    [h₁ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh₁)))]
    [h₂ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh₂)))] :
    tateRes u fh gh₁ = tateRes u fh gh₂ := by
  subst heq; rfl

theorem tateRes_add_snd (u : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (f g h : u.adicCompletion) :
    haveI := hfin u f (g + h); haveI := hfin u f g; haveI := hfin u f h
    tateRes u f (g + h) = tateRes u f g + tateRes u f h := by
  haveI := hfin u f (g + h); haveI := hfin u f g; haveI := hfin u f h
  have heq : lmulK u (g + h) = lmulK u g + lmulK u h := map_add _ _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f) (lmulK u g + lmulK u h))) := by
    rw [← heq]; exact hfin u f (g + h)
  unfold tateRes
  have hct := tateCommTrace_add_snd (tateProj u) (lmulK u f) (lmulK u g) (lmulK u h)
  unfold tateCommTrace at hct ⊢
  rw [← hct]
  exact finrankTrace_congr (by rw [heq])

def tateResFstLM (w : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (gh : w.adicCompletion) : DualDom w where
  toFun f := haveI := hfin w f gh; tateRes w f gh
  map_add' f₁ f₂ := by
    haveI := hfin w f₁ gh; haveI := hfin w f₂ gh
    exact tateRes_add_fst w f₁ f₂ gh
  map_smul' c f := by
    haveI := hfin w f gh; haveI := hfin w (c • f) gh
    show tateRes w (c • f) gh = c • tateRes w f gh
    have heq : tateCommRestrict (tateProj w) (lmulK w (c • f)) (lmulK w gh)
        = c • tateCommRestrict (tateProj w) (lmulK w f) (lmulK w gh) := by
      rw [show lmulK w (c • f) = c • lmulK w f from map_smul _ _ _,
        tateCommRestrict_smul_fst]
    haveI := finDimRangeSMul c (tateCommRestrict (tateProj w) (lmulK w f) (lmulK w gh))
    unfold tateRes tateCommTrace
    rw [finrankTrace_congr heq, finrankTrace_smul]

@[scoped simp] theorem tateResFstLM_apply (w : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (gh f : w.adicCompletion) :
    (tateResFstLM w hfin gh).toLM f = haveI := hfin w f gh; tateRes w f gh := rfl

variable [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]

def tateResSndDer (w : Place K F) [w.DCoordGenerates] [w.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K F) : Derivation K F (DualDom w) :=
  Derivation.mk'
    { toFun := fun g => tateResFstLM w hfin (algebraMap F w.adicCompletion g)
      map_add' := fun g h => DualDom.ext fun f => by
        simp only [tateResFstLM_apply, DualDom.toLM_add, map_add]
        exact tateRes_add_snd w hfin f _ _
      map_smul' := fun c g => DualDom.ext fun f => by
        simp only [tateResFstLM_apply, RingHom.id_apply, DualDom.k_smul_apply]
        haveI := hfin w f (algebraMap F _ (c • g))
        haveI := hfin w f (algebraMap F _ g)
        show tateRes w f (algebraMap F _ (c • g)) = c • tateRes w f (algebraMap F _ g)
        have heq : tateCommRestrict (tateProj w) (lmulK w f)
              (lmulK w (algebraMap F _ (c • g)))
            = c • tateCommRestrict (tateProj w) (lmulK w f)
              (lmulK w (algebraMap F _ g)) := by
          rw [show lmulK w (algebraMap F _ (c • g)) = c • lmulK w (algebraMap F _ g) from by
              rw [Algebra.smul_def, (algebraMap F w.adicCompletion).map_mul,
                ← IsScalarTower.algebraMap_apply K F w.adicCompletion,
                Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
              exact map_smul _ _ _,
            tateCommRestrict_smul_snd]
        haveI := finDimRangeSMul c
          (tateCommRestrict (tateProj w) (lmulK w f) (lmulK w (algebraMap F _ g)))
        unfold tateRes tateCommTrace
        rw [finrankTrace_congr heq, finrankTrace_smul] }
    (fun g h => DualDom.ext fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, tateResFstLM_apply, DualDom.smul_apply,
        DualDom.toLM_add]
      haveI := hfin w f (algebraMap F _ (g * h))
      haveI := hfin w (algebraMap F _ g * f) (algebraMap F _ h)
      haveI := hfin w (algebraMap F _ h * f) (algebraMap F _ g)
      haveI := hfin w f (algebraMap F _ g * algebraMap F _ h)
      haveI := hfin w (f * algebraMap F _ g) (algebraMap F _ h)
      haveI := hfin w (f * algebraMap F _ h) (algebraMap F _ g)
      show tateRes w f (algebraMap F _ (g * h))
        = tateRes w (algebraMap F _ g * f) (algebraMap F _ h)
          + tateRes w (algebraMap F _ h * f) (algebraMap F _ g)
      rw [tateRes_congr_snd w ((algebraMap F w.adicCompletion).map_mul g h),
        tateRes_leibniz_snd w hfin f (algebraMap F _ g) (algebraMap F _ h),
        tateRes_congr_fst w (mul_comm f (algebraMap F _ g)),
        tateRes_congr_fst w (mul_comm f (algebraMap F _ h))])

@[scoped simp] theorem tateResSndDer_apply (w : Place K F) [w.DCoordGenerates] [w.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K F) (g : F) (f : w.adicCompletion) :
    ((tateResSndDer w hfin) g).toLM f
      = haveI := hfin w f (algebraMap F _ g); tateRes w f (algebraMap F _ g) := rfl

end TateResDerivation
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]

theorem kwTateRR2_derivationFactorSnd [∀ w : Place K F, w.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) :
    KwF4gRRTateDerivationFactorSnd K F hfinF := by
  intro w _ f g
  haveI := hfinF w f (algebraMap F _ g)
  haveI := hfinF w (f * algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)))
    (algebraMap F _ w.uniformizer)

  have hδ := derivation_apply_eq_diffCoeff_smul (M := DualDom w) w (tateResSndDer w hfinF) g
  haveI := hfinF w (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f)
    (algebraMap F _ w.uniformizer)
  calc tateRes w f (algebraMap F _ g)
      = ((tateResSndDer w hfinF) g).toLM f := (tateResSndDer_apply w hfinF g f).symm
    _ = (w.differentialCoeff (KaehlerDifferential.D K F g)
          • (tateResSndDer w hfinF) w.uniformizer).toLM f := by rw [hδ]
    _ = ((tateResSndDer w hfinF) w.uniformizer).toLM
          (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f) :=
        DualDom.smul_apply _ _ _
    _ = tateRes w (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f)
          (algebraMap F _ w.uniformizer) := tateResSndDer_apply w hfinF w.uniformizer _
    _ = tateRes w (f * algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)))
          (algebraMap F _ w.uniformizer) :=
        tateRes_congr_fst w (mul_comm _ f)

end Headline
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

section Composite

variable {K F E : Type*} [Field K] [Field F] [Algebra K F]
variable [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

end Composite
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

end ModularCurve.KwF4gRRTate
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V410a P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate.DualDom"

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E] [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue] (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F) : ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule K F E hfinF :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_chainRule_of_derivationFactor hfinF
    (fun {_ _} => ModularCurve.KwF4gRRTate.kwTateRR2_derivationFactorSnd hfinF)

end S_AlgebraicCurve_tateChainRule
end P2MW
export P2MW.S_AlgebraicCurve_tateChainRule (solution)
