-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittVectorGhostEqFrobeniusIterate
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWittVectorGhostEqFrobeniusIterate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:10.791556+00:00
-- url     : https://prove2.me/theorems/acb94462-dc84-4beb-b73b-b562eafbdaa8
-- title:
--   Exists Witt Vector Ghost Eq Frobenius Iterate
-- statement:
--   Definitions and structural lemmas for Exists Witt Vector Ghost Eq Frobenius Iterate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWittVectorGhostEqFrobeniusIterate.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open Finset
namespace GlobalTheory.DworkGhost
open Classical in

noncomputable def coeff {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) : ℕ → A
  | n => if h : ((l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i))
      then h.choose else 0
decreasing_by all_goals exact i.isLt
end GlobalTheory.DworkGhost


