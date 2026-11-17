-- Prove2me | Definitions.Def_N25_NormalizedPointPivot
-- name    : N25_NormalizedPointPivot
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:34.053203+00:00
-- url     : https://prove2.me/theorems/062a8d76-56e1-46cf-97dc-a0c499064ae8
-- title:
--   The unit pivot of a normalized projective point
-- statement:
--   Records that the distinguished first nonzero coordinate of each normalized projective representative is exactly $1$. This small normalization fact is a technical carrier for placing every canonical point in its selected affine chart.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalNormalizedPoints
/-! The selected pivot coordinate of a normalized projective vector is one. -/

namespace N25.Endgame

open MazurProof.RationalPointsN25QuotientWeil

/-- The selected pivot coordinate is one. -/
theorem normalizedCoordinates25_pivot {K : Type*} [Field K]
    (P : NormalizedProjective4 K) :
    normalizedCoordinates25 P (normalizedPivot25 P) = 1 := by
  cases P <;> rfl

end N25.Endgame


