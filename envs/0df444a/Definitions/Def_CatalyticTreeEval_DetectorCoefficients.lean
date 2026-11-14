-- Prove2me | Definitions.Def_CatalyticTreeEval_DetectorCoefficients
-- name    : CatalyticTreeEval_DetectorCoefficients
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:23:05.056407+00:00
-- url     : https://prove2.me/theorems/b06b0edc-1e77-4e00-8295-2729ec097275
-- title:
--   Explicit binomial-inversion coefficients of the weight detector
-- statement:
--   Define the closed binomial-inversion formula for the elementary-symmetric coefficients of a detector with residue r=w mod q. The matrix-inverse specification and this explicit formula are related by a subsequent theorem. This representation makes streamed coefficient generation possible without storing an inverse matrix.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.5.

import Definitions.Def_CatalyticTreeEval_WeightDetector

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Closed binomial-inversion formula for a coefficient of the residue detector. -/
def explicitDetectorCoefficient (p q w : ℕ) (j : Fin q) : ZMod p :=
  (if j.val = 0 then 1 else 0) -
    (if w % q ≤ j.val then (-1 : ZMod p) ^ (j.val - w % q) * (j.val.choose (w % q) : ZMod p) else 0)

end CatalyticTreeEval.Main


