-- Prove2me | Definitions.Def_RuntimeTransferPacking
-- name    : RuntimeTransferPacking
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:13:48.994884+00:00
-- url     : https://prove2.me/theorems/d21ee961-be40-4d2b-9f9a-70178e4f89db
-- title:
--   Signed packing as an integer-oracle program
-- statement:
--   Defines the query consisting of the two integers obtained by packing integer coefficient lists in base $2^{3p}$. The one-query program charges arbitrary natural numbers $E,D$ before and after the call and returns $2r-1$ balanced digits of the oracle answer, using the existing Kronecker definitions. These definitions impose no coefficient or length bounds. Subsequent correctness hypotheses supply them; $E,D$ are stipulated costs, not verified costs of implementing packing and decoding.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound.

import Definitions.Def_RuntimeTransfer
import Definitions.Def_IntMul_HvdH_KronMul

set_option autoImplicit false
namespace RuntimeTransfer

def packedQuery (p : ℕ) (a b : List ℤ) : ℤ × ℤ :=
  (IntMul.HvdH.kpack (2 ^ (3 * p)) a, IntMul.HvdH.kpack (2 ^ (3 * p)) b)

/-- The cost unit must agree with the multiplication oracle's cost unit. -/
def packingProgram (p r : ℕ) (a b : List ℤ) (E D : ℕ) :
    Program (ℤ × ℤ) ℤ (List ℤ) :=
  .work E (.query (packedQuery p a b) (fun z =>
    .work D (.done (IntMul.HvdH.kunpack (2 ^ (3 * p)) (2 * r - 1) z))))

end RuntimeTransfer


