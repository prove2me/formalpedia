-- Prove2me | Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
-- name    : Submission_ThreeSum_LightIrreducibleBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:44:52.087443+00:00
-- url     : https://prove2.me/theorems/fc7b55fc-c692-43c5-8e01-53db9d41ab39
-- title:
--   Light Irreducible Budget
-- statement:
--   Definitions and structural lemmas for Light Irreducible Budget, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleBudget.lean

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
set_option autoImplicit false
namespace ThreeSum.LightIrreducibleFinder
open Light
set_option maxHeartbeats 3000000
def uniformFactorTime (d p q : ℕ) : ℕ :=
  q*q*(2*LightCoefficientDecode.time (2*d) (2*q)+
    LightPolynomialProductCheck.time (d+1) p (2*d)+700)+100
def uniformFactorWord (d p q : ℕ) : ℕ :=
  2*LightCoefficientDecode.word (2*d) p (2*q) 0 1+
    20*((d+2)*(p+1)^2+3*d+11)+200
end ThreeSum.LightIrreducibleFinder


