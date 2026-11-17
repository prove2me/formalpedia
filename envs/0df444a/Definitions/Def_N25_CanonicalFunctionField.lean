-- Prove2me | Definitions.Def_N25_CanonicalFunctionField
-- name    : N25_CanonicalFunctionField
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:41.340326+00:00
-- url     : https://prove2.me/theorems/b538c94a-53e0-4704-b926-1a3bb6a5a38b
-- title:
--   The birational equivalence of the plane and canonical function fields
-- statement:
--   The file defines the fraction field of the literal unit-plane coordinate ring and the total fraction ring of the canonical principal open. It selects the explicit equivalence of their localized coordinate rings, installs the required scalar towers, and extends that equivalence to a $ℚ$-algebra equivalence of function fields. This is the formal birational identification between the plane and canonical models.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalOpenAlgebra
/-! The function-field equivalence induced by the literal principal-open coordinate rings. -/
noncomputable section
namespace N25

instance unitPlaneRing_domain : IsDomain UnitPlaneRing := unitPlaneRing_isDomain
instance unitPlaneOpenRing_domain : IsDomain UnitPlaneOpenRing := unitPlaneOpenRing_isDomain
instance canonicalOpenChartRing_domain : IsDomain (CanonicalOpenChartRing25 ℚ) :=
  canonicalOpenChartRing_isDomain

/-- The fraction field of the literal plane coordinate ring. -/
abbrev UnitPlaneFF25 := FractionRing UnitPlaneRing

/-- The total fraction ring of the literal canonical principal open. -/
abbrev CanonicalFF25 (k : Type*) [CommRing k] := FractionRing (CanonicalOpenChartRing25 k)

instance unitPlaneFF25Semiring : Semiring UnitPlaneFF25 := inferInstance
instance unitPlaneFF25CommSemiring : CommSemiring UnitPlaneFF25 := inferInstance
instance canonicalFF25Semiring : Semiring (CanonicalFF25 ℚ) := inferInstance
instance canonicalFF25CommSemiring : CommSemiring (CanonicalFF25 ℚ) := inferInstance
instance unitPlaneFF25RatAlgebra : Algebra ℚ UnitPlaneFF25 := inferInstance
instance canonicalFF25RatAlgebra : Algebra ℚ (CanonicalFF25 ℚ) := inferInstance

/-- The canonical principal-open equivalence selected together with its coordinate formulas. -/
def canonicalUnitPlaneOpenAlgEquiv25 : CanonicalOpenChartRing25 ℚ ≃ₐ[ℚ] UnitPlaneOpenRing :=
  canonicalOpenChart_algEquiv_unitPlaneOpen.choose

/-- The selected equivalence has the prescribed normalized canonical coordinates. -/
theorem canonicalUnitPlaneOpenAlgEquiv25_coordinates :
    let l := algebraMap UnitPlaneRing UnitPlaneOpenRing
    let u := l unitPlaneU
    let v := l unitPlaneV
    let h := IsLocalization.Away.invSelf (S := UnitPlaneOpenRing) unitPlaneOpenElement
    ∀ i : Fin 4, canonicalUnitPlaneOpenAlgEquiv25
      (algebraMap (CanonicalAChartRing25 ℚ) (CanonicalOpenChartRing25 ℚ)
        (canonicalAChartCoordinate25 ℚ i)) =
      (![u,u*h*planeY u v,u*h*planeZ u v,u*h*planeW u v] : Fin 4 → UnitPlaneOpenRing) i :=
  canonicalOpenChart_algEquiv_unitPlaneOpen.choose_spec

/-- The localization of the plane ring acts on its fraction field through the canonical lift. -/
instance unitPlaneOpenFractionAlgebra : Algebra UnitPlaneOpenRing UnitPlaneFF25 :=
  IsLocalization.localizationAlgebraOfSubmonoidLe UnitPlaneOpenRing UnitPlaneFF25
    (Submonoid.powers unitPlaneOpenElement) (nonZeroDivisors UnitPlaneRing)
    unitPlaneOpenPowers_le_nonZeroDivisors

instance unitPlaneOpenFractionTower : IsScalarTower UnitPlaneRing UnitPlaneOpenRing UnitPlaneFF25 :=
  IsLocalization.localization_isScalarTower_of_submonoid_le UnitPlaneOpenRing UnitPlaneFF25
    (Submonoid.powers unitPlaneOpenElement) (nonZeroDivisors UnitPlaneRing)
    unitPlaneOpenPowers_le_nonZeroDivisors

instance unitPlaneOpenFractionRatTower : IsScalarTower ℚ UnitPlaneOpenRing UnitPlaneFF25 :=
  IsScalarTower.to₁₃₄ ℚ UnitPlaneRing UnitPlaneOpenRing UnitPlaneFF25

instance unitPlaneOpen_isFractionRing : IsFractionRing UnitPlaneOpenRing UnitPlaneFF25 :=
  IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers unitPlaneOpenElement)
    UnitPlaneOpenRing UnitPlaneFF25 unitPlaneOpenPowers_le_nonZeroDivisors

/-- The coordinate-ring equivalence extends to the two function fields. -/
def canonicalUnitPlaneAlgEquiv25 : UnitPlaneFF25 ≃ₐ[ℚ] CanonicalFF25 ℚ :=
  (IsFractionRing.algEquivOfAlgEquiv (K := CanonicalFF25 ℚ) (L := UnitPlaneFF25)
    canonicalUnitPlaneOpenAlgEquiv25).symm

/-- The field equivalence extends the specified principal-open map on all four coordinates. -/
theorem canonicalUnitPlaneAlgEquiv25_symm_coordinates :
    let l := algebraMap UnitPlaneRing UnitPlaneOpenRing
    let u := l unitPlaneU
    let v := l unitPlaneV
    let h := IsLocalization.Away.invSelf (S := UnitPlaneOpenRing) unitPlaneOpenElement
    ∀ i : Fin 4, canonicalUnitPlaneAlgEquiv25.symm
      (algebraMap (CanonicalOpenChartRing25 ℚ) (CanonicalFF25 ℚ)
        (algebraMap (CanonicalAChartRing25 ℚ) (CanonicalOpenChartRing25 ℚ)
          (canonicalAChartCoordinate25 ℚ i))) =
      algebraMap UnitPlaneOpenRing UnitPlaneFF25
        ((![u,u*h*planeY u v,u*h*planeZ u v,u*h*planeW u v] : Fin 4 → UnitPlaneOpenRing) i) := by
  dsimp only
  intro i
  change IsFractionRing.algEquivOfAlgEquiv canonicalUnitPlaneOpenAlgEquiv25
    (algebraMap (CanonicalOpenChartRing25 ℚ) (CanonicalFF25 ℚ)
      (algebraMap (CanonicalAChartRing25 ℚ) (CanonicalOpenChartRing25 ℚ)
        (canonicalAChartCoordinate25 ℚ i))) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  exact congrArg (algebraMap UnitPlaneOpenRing UnitPlaneFF25)
    (canonicalUnitPlaneOpenAlgEquiv25_coordinates i)

end N25


