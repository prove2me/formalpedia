-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:32.499808+00:00
-- url     : https://prove2.me/theorems/53329471-b5e6-49af-8233-2a7ee6b0aa20
-- title:
--   Compact Casimir Highest Weight
-- statement:
--   Definitions and structural lemmas for Compact Casimir Highest Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
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
section basics
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
end basics
section low
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
def wordWeightShift {m : ℕ} : List (Fin m × Fin m) → Fin m → ℝ
  | [] => 0
  | p :: w => Pi.single p.1 1 - Pi.single p.2 1 + wordWeightShift w
def heightFunctional {m : ℕ} (v : Fin m → ℝ) : ℝ := ∑ a : Fin m, ((a : ℕ) : ℝ) * v a
def heightOperator (F : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ a : Fin n, ((a : ℕ) : ℂ) • F a a
end low
section cas
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
end cas
end Formalism.REAL


