-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
-- name    : Submission_ThreeSum_TernaryActualSeedEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:33:04.005901+00:00
-- url     : https://prove2.me/theorems/5aa31f0e-23ae-4df9-8c3a-d72587baeeb8
-- title:
--   Ternary Actual Seed Enumeration
-- statement:
--   Definitions and structural lemmas for Ternary Actual Seed Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryActualSeedEnumeration
open TernaryExtensionEncoding Polynomial
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
set_option maxHeartbeats 2000000
def equiv (hf : f.Monic) : (AdjoinRoot f×AdjoinRoot f) ≃ Fin ((p^f.natDegree)*(p^f.natDegree)) :=
  (Equiv.prodCongr (encodedEquiv hf) (encodedEquiv hf)).trans finProdFinEquiv
end ThreeSum.TernaryActualSeedEnumeration


