-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
-- name    : Submission_ThreeSum_LightTernaryBankResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:57:35.483202+00:00
-- url     : https://prove2.me/theorems/fdd8b086-61d5-4fdc-81af-5f08c9e7ee66
-- title:
--   Light Ternary Bank Resources
-- statement:
--   Definitions and structural lemmas for Light Ternary Bank Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankResources.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
set_option autoImplicit false
namespace ThreeSum.LightTernaryBankCoordinate
end ThreeSum.LightTernaryBankCoordinate
namespace ThreeSum.LightTernaryBankSweep
end ThreeSum.LightTernaryBankSweep
namespace ThreeSum.LightTernaryBankAssembly
def keyBase (a n : ℕ) : ℕ := a+n
def powersBase (a n : ℕ) : ℕ := keyBase a n+4*n
def fBase (a n N : ℕ) : ℕ := powersBase a n+(2*N+1)
def gBase (a n N : ℕ) : ℕ := fBase a n N+(N+1)*n
def hBase (a n N : ℕ) : ℕ := gBase a n N+(N+1)*n
def space (a n N : ℕ) : ℕ :=hBase a n N+(N+1)*n
def word (a n N V : ℕ) : ℕ :=space a n N+n+2^(2*N+1)+2*N+
  4*(4^N*V)+4*(4^N*valueBound N V)+valueBound N V+100
def depth (d N L : ℕ) : ℕ := d+2*N+L+6
end ThreeSum.LightTernaryBankAssembly


