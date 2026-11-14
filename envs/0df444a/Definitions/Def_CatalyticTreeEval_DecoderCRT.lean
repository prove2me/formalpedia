-- Prove2me | Definitions.Def_CatalyticTreeEval_DecoderCRT
-- name    : CatalyticTreeEval_DecoderCRT
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:45:49.101199+00:00
-- url     : https://prove2.me/theorems/32c4abab-c779-416d-98e6-0f446607cdc6
-- title:
--   Canonical tensor decoder over the CRT residue ring
-- statement:
--   The canonical decoder combines explicit base-three indexing, local kernel products, the residue projections and the bounded CRT lift over the product of distinct primes. It has exactly three to the number-of-primes many terms. Correctness and efficient access are separate obligations.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Lemma3.19.

import Definitions.Def_CatalyticTreeEval_DecoderTensor
import Definitions.Def_CatalyticTreeEval_CRT

set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

/-- The exact `3^t`-term decoder from Lemma 3.19. -/
noncomputable def canonicalDecoder {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p) :
    Main.Decoder (Main.modulus p) (3 ^ t) :=
  tensorDecoder (CRT.project p) (CRT.crtLift p hp)

end CatalyticTreeEval.DecoderConstruction


