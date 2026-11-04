-- Prove2me | Definitions.Def_Submission_Weighted_BankResources
-- name    : Submission_Weighted_BankResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:54:09.795758+00:00
-- url     : https://prove2.me/theorems/8f307dd4-32f7-4740-889f-c43f1fc8cf81
-- title:
--   Bank Resources
-- statement:
--   Definitions and structural lemmas for Bank Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankResources.lean

import Definitions.Def_Submission_Weighted_BankAssembly
set_option autoImplicit false
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


