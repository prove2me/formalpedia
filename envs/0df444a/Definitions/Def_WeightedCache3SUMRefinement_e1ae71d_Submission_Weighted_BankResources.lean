-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:13:30.520504+00:00
-- url     : https://prove2.me/theorems/7a623eb1-6e55-4a14-b5c4-827d3dbe506e
-- title:
--   BankResources
-- statement:
--   Definitions and structural lemmas for BankResources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankResources.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedBankCoordinate
end ThreeSum.LightWeightedBankCoordinate
namespace ThreeSum.LightWeightedBankSweep
end ThreeSum.LightWeightedBankSweep
namespace ThreeSum.LightWeightedBankAssembly
def keyBase (a n : ℕ) : ℕ := a+n
def powersBase (a n : ℕ) : ℕ := keyBase a n+4*n
def fBase (a n N : ℕ) : ℕ := powersBase a n+(2*N+1)
def gBase (a n N : ℕ) : ℕ := fBase a n N+(N+1)*n
def hBase (a n N : ℕ) : ℕ := gBase a n N+(N+1)*n
def space (a n N : ℕ) : ℕ :=hBase a n N+(N+1)*n
def word (a n N V : ℕ) : ℕ :=space a n N+n+2^(2*N+1)+2*N+
  4*(4^N*V)+4*(4^N*valueBound N V)+valueBound N V+100
def depth (d N L : ℕ) : ℕ := d+2*N+L+6
end ThreeSum.LightWeightedBankAssembly
end WeightedCache3SUMRefinement_e1ae71d


