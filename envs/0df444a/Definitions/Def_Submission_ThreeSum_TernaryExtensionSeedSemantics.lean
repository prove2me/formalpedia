-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
-- name    : Submission_ThreeSum_TernaryExtensionSeedSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:39.641462+00:00
-- url     : https://prove2.me/theorems/7970a0b4-13f4-48ba-87ec-3e75d0d5a927
-- title:
--   Ternary Extension Seed Semantics
-- statement:
--   Definitions and structural lemmas for Ternary Extension Seed Semantics, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
noncomputable local instance _p2m_local_instance_7138b7e7ca_12 (Q : Prop) : Decidable Q := Classical.propDecidable Q
variable {f : (ZMod p)[X]}
def encodedMul (hf : f.Monic) (a b : ℕ) : ℕ :=
  if ha : a<p^f.natDegree then if hb : b<p^f.natDegree then
    encode hf ((encodedEquiv hf).symm ⟨a,ha⟩*(encodedEquiv hf).symm ⟨b,hb⟩) else 0 else 0
def quotientGood (d c x y h r : ℕ) : Prop :=
  LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
    (LightPolynomialQuotientCheck.expected p d (codeDigits (p := p) h)
      (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r)) d d (2*d)
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
end ThreeSum.TernaryExtensionEncoding


