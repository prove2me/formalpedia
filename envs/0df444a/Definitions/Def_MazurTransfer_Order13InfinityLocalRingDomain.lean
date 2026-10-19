-- Prove2me | Definitions.Def_MazurTransfer_Order13InfinityLocalRingDomain
-- name    : MazurTransfer_Order13InfinityLocalRingDomain
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:35:14.978169+00:00
-- url     : https://prove2.me/theorems/21e028db-b747-46cf-a876-718e5755fc83
-- title:
--   Domain and nonzero-coordinate facts for the actual infinity local ring
-- statement:
--   Let $K$ be a field of characteristic zero and let $a^2=1$. The actual reciprocal coordinate algebra and its localization at the infinity evaluation kernel are domains, the localization is noetherian, and its reciprocal coordinate satisfies $$z\ne0.$$ These original facts supply the discrete valuation ring structure and the exact Pell valuation orders.
-- source:
--   Original complete four declarations from MazurTheorem Order13InfinityDiscreteValuationRing.lean, Apache-2.0, Vas and contributors. Four complete original closed types are kernel-compared. There are no data-valued definitions; the original instance and proof bodies are retained. Uses the existing public canonical finite-map primitives. Named downstream consumer: actual infinity DVR and Pell orders.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual reciprocal-chart local rings at the two infinity
points are discrete valuation rings, with z as a uniformizer, in characteristic
zero. Named downstream consumer: the exact Pell orders and principal divisor.
-/
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingCoordinates
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitives
noncomputable section
universe u
namespace MazurTransfer.Order13InfinityDiscreteValuationRing
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13InfinityLocalParameter
variable (K : Type u) [Field K] [CharZero K] (a : K) (ha : a ^ 2 = 1)

instance reciprocalRing_isDomain : IsDomain (ReciprocalRing K) :=
  Order13ReciprocalInjectionCurveDomains.reciprocalRing_isDomain K
    (isUnit_iff_ne_zero.mpr (by norm_num))

instance localRing_isDomain : IsDomain (LocalRing K a ha) := by infer_instance

instance localRing_isNoetherianRing : IsNoetherianRing (LocalRing K a ha) := by infer_instance

theorem z_ne_zero : z K a ha ≠ 0 := by
  dsimp [z]
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective
    (ReciprocalRing K) (LocalRing K a ha))).mpr
    (Order13SingleSectionFiniteAlgebra.actual_reciprocal_z_ne_zero K)

end MazurTransfer.Order13InfinityDiscreteValuationRing
#print axioms MazurTransfer.Order13InfinityDiscreteValuationRing.z_ne_zero


