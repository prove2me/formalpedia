-- Prove2me | Definitions.Def_OpenMath_WOWII19
-- name    : OpenMath_WOWII19
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:37:49.670874+00:00
-- url     : https://prove2.me/theorems/bc687423-b9b7-4cef-8f8c-d30857b92e89
-- title:
--   WOWII19
-- statement:
--   Definitions and structural lemmas for WOWII19, from Rhett (v3ai/openmath; definitions reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Proof of WOWII Conjecture 96 (DeLaVina, Graffiti.pc) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedSectionVars false
namespace OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
noncomputable def layer (G : SimpleGraph α) (v : α) (i : ℕ) : Finset α :=
  univ.filter fun w => G.dist v w = i
noncomputable def indepIn (G : SimpleGraph α) (T : Finset α) : ℕ := by
  classical
  exact (T.powerset.filter fun s : Finset α => (↑s : Set α).Pairwise fun x y => ¬ G.Adj x y).sup card
variable {G : SimpleGraph α}
end OpenMath.WOWII19


