-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:28.946139+00:00
-- url     : https://prove2.me/theorems/eb7fc23a-aecd-43ae-9317-db694147054c
-- title:
--   First Slot Slice Slot Mixed Casimir Zero
-- statement:
--   Definitions and structural lemmas for First Slot Slice Slot Mixed Casimir Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
namespace Formalism.REAL
section U3Basic
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Basic
section U3Inner
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
end U3Inner
section U3Cas
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
end U3Cas
section U3CasArr
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3CasArr
section U3Perm
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Perm
section U3Succ
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Succ
section U3Stable
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}
end U3Stable
section U3Sym
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
end U3Sym
section U3NPos
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n j : ℕ}
end U3NPos
end Formalism.REAL


