-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
-- name    : Submission_ThreeSum_TernaryPairedColumnEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:18.953854+00:00
-- url     : https://prove2.me/theorems/db6c5ba6-ec56-4bfe-b054-cd52e1805101
-- title:
--   Ternary Paired Column Enumeration
-- statement:
--   Definitions and structural lemmas for Ternary Paired Column Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedColumnEnumeration.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl

set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPairedColumnEnumeration
open TernaryPairedTensor
open scoped BigOperators
abbrev width (m : ℕ) : ℕ := Fintype.card (PairedIndex m)
def equiv (m Λ : ℕ) : (PairedIndex m → Fin Λ) ≃ Fin (Λ^width m) :=
  ((Equiv.arrowCongr (Fintype.equivFin (PairedIndex m)) (Equiv.refl (Fin Λ))).trans
    (Equiv.arrowCongr (Fin.revPerm) (Equiv.refl (Fin Λ)))).trans finFunctionFinEquiv
end ThreeSum.TernaryPairedColumnEnumeration


