-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
-- name    : Submission_ThreeSum_LightExtensionMenuSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:32:51.38663+00:00
-- url     : https://prove2.me/theorems/021f6ba2-8021-4123-8c47-64a789a4a9f6
-- title:
--   Light Extension Menu Semantics
-- statement:
--   Definitions and structural lemmas for Light Extension Menu Semantics, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuSemantics.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionMenuMatrix
open TernaryExtensionEncoding
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
def seed (hf : f.Monic) (r : ℕ) (hr : r < (p^f.natDegree)*(p^f.natDegree)) :
    AdjoinRoot f × AdjoinRoot f :=
  let q := p^f.natDegree
  let hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  ((encodedEquiv hf).symm ⟨r/q,(Nat.div_lt_iff_lt_mul hq).mpr hr⟩,
   (encodedEquiv hf).symm ⟨r%q,Nat.mod_lt r hq⟩)
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
end ThreeSum.LightExtensionMenuMatrix


