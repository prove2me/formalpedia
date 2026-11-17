-- Prove2me | Definitions.Def_N25_CanonicalFunctionFieldOverField
-- name    : N25_CanonicalFunctionFieldOverField
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:08.274703+00:00
-- url     : https://prove2.me/theorems/4a73c40f-d253-4514-b24e-318ee313e272
-- title:
--   The canonical–plane function-field equivalence over an arbitrary field
-- statement:
--   For any field $K$, the file equips the plane principal open with its action on the plane fraction field, records the compatible scalar towers, and identifies the repeated localization with the same function field. It then extends the explicit principal-open equivalence to $$K(plane)≃_K K(canonical).$$ This is the coefficient-uniform version needed at the good primes and their finite extensions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalFunctionCoordinates
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Theorems.Thm_N25_canonicalOpenChartRing25C_isDomain
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
/-! Function fields of the literal canonical and unit-plane models over a field. -/
noncomputable section
namespace N25

variable (K : Type*) [Field K]

local instance instL_N25_CanonicalFunctionFieldOverField_fb3071 : IsDomain (UnitPlaneOpenRing25C K) := unitPlaneOpenRing25C_isDomain
local instance instL_N25_CanonicalFunctionFieldOverField_1adf8f : IsDomain (CanonicalOpenChartRing25 K) := canonicalOpenChartRing25C_isDomain

/-- The plane principal open acts on the fraction field of its coordinate ring. -/
instance unitPlaneOpenFractionAlgebra25C :
    Algebra (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K)
    (Submonoid.powers (unitPlaneOpenElement25C K)) (nonZeroDivisors (UnitPlaneRing25C K))
    unitPlaneOpenPowers25C_le_nonZeroDivisors

/-- Passing through the principal open preserves the coordinate-ring scalar action. -/
instance unitPlaneOpenFractionTower25C :
    IsScalarTower (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K)
    (Submonoid.powers (unitPlaneOpenElement25C K)) (nonZeroDivisors (UnitPlaneRing25C K))
    unitPlaneOpenPowers25C_le_nonZeroDivisors

/-- The coefficient field acts compatibly through the plane principal open. -/
instance unitPlaneOpenFractionCoefficientTower25C :
    IsScalarTower K (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K) :=
  IsScalarTower.to₁₃₄ K (UnitPlaneRing25C K) (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K)

/-- Localizing the plane principal open again gives the same function field. -/
instance unitPlaneOpenIsFractionRing25C :
    IsFractionRing (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K) :=
  IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers (unitPlaneOpenElement25C K))
    (UnitPlaneOpenRing25C K) (UnitPlaneFF25C K)
    unitPlaneOpenPowers25C_le_nonZeroDivisors

/-- The explicit principal-open equivalence induces an equivalence of function fields. -/
def canonicalUnitPlaneAlgEquiv25C : UnitPlaneFF25C K ≃ₐ[K] CanonicalFF25 K :=
  (IsFractionRing.algEquivOfAlgEquiv (K := CanonicalFF25 K) (L := UnitPlaneFF25C K)
    (canonicalUnitPlaneOpenAlgEquiv25C K)).symm

end N25


