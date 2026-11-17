-- Prove2me | Definitions.Def_N25_UnitPlaneModularMapGoodCharacteristic
-- name    : N25_UnitPlaneModularMapGoodCharacteristic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:08:49.135987+00:00
-- url     : https://prove2.me/theorems/8c46513b-12d8-4ee7-b328-68d8a13e901c
-- title:
--   The unit-plane map in characteristics $2$ and $3$
-- statement:
--   Let $p$ be a prime with $p=2$ or $p=3$, and let $K$ be a field of characteristic $p$. The file defines a $K$-algebra map from the unit-plane function field to the level-$25$ modular function field by $$U_A↦U_0,\qquad V_A↦U_0/U_1.$$ This map transports the explicit plane model to the modular function field in the two good characteristics used for point counting.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_U25C_zero_transcendental
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitRelation25_qExpansion_certificate
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25
import Theorems.Thm_ModularForm_sturm_bound_of_isArithmetic
/-! Evaluation of the plane function field at the modular units in good characteristic. -/
noncomputable section
namespace N25.Endgame

/-- The unit-plane function field maps to the specified modular function field by its two units. -/
def unitPlaneToXHGood25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    N25.UnitPlaneFF25C K →ₐ[K] FBase K := by
  let : IsDomain (N25.UnitPlaneRing25C K) :=
    N25.unitPlaneRing25C_isDomain_good p hp K
  exact N25.unitPlaneFieldPointLift25C (K := K)
      (N25.U25C K 0) (N25.U25C K 0 / N25.U25C K 1)
      (N25.unitRelation25_qExpansion_certificate K)
      (N25.U25C_zero_transcendental K)

end N25.Endgame


