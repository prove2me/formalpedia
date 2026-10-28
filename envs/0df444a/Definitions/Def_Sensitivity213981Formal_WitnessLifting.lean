-- Prove2me | Definitions.Def_Sensitivity213981Formal_WitnessLifting
-- name    : Sensitivity213981Formal_WitnessLifting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:08:42.777548+00:00
-- url     : https://prove2.me/theorems/48db7bfb-3b61-4e08-a5a7-46251d4c6937
-- title:
--   Witness Lifting — sensitivity certificate definitions
-- statement:
--   The definitions for Witness Lifting in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundWitness.parent`, `ThreeBoundWitness.reindex`, `ThreeBoundWitness.flip_reindex`, `ThreeBoundWitness.flip_reindex_singleton`, `ThreeBoundWitness.replicate`, `ThreeBoundWitness.planted`, `ThreeBoundWitness.Stage`, `ThreeBoundWitness.child`, `ThreeBoundWitness.pairedBlock`, `ThreeBoundWitness.failed`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; WitnessLifting.lean, lines 1–408.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

namespace Sensitivity213981Formal
section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}

structure Stage (L I V : Type) where
  Adj : V → V → Prop
  loopless : ∀ v, ¬ Adj v v
  label : V → V → Bool
  guard : L → L
  tolerance : L → ℕ
  target : L → ℕ → (I → Bool) → (I → Bool) → Bool

def child (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) : I → Bool :=
  fun i => x ((v,c),i)

noncomputable def failed [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => S.Adj v w ∧ F (S.guard l) (child x w (S.label v w)) = true

noncomputable def parent [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) : Bool := by
  classical
  exact decide (∃ v : V, (failed S F l x v).card ≤ S.tolerance l ∧
    S.target l (failed S F l x v).card (child x v false) (child x v true) = true)





def replicate (z : I → Bool) : ((V × Bool) × I) → Bool := fun p => z p.2

noncomputable def planted (z p : I → Bool) (v : V) : ((V × Bool) × I) → Bool := by
  classical
  exact fun q => if q.1.1 = v then p q.2 else z q.2





















noncomputable def pairedBlock (v : V) (B : Finset I) : Finset ((V × Bool) × I) := by
  classical
  exact ((Finset.univ : Finset Bool).product B).map
    ⟨fun q => ((v,q.1),q.2), by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun q => q.1.2) h
      · exact congrArg (fun q => q.2) h⟩



















/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/
def reindex {J : Type} (e : I ≃ J) (f : (I → Bool) → Bool) : (J → Bool) → Bool :=
  fun x => f (fun i => x (e i))

theorem flip_reindex {J : Type} (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => OAI.Paper320.flip x (B.map e.toEmbedding) (e i)) =
      OAI.Paper320.flip (fun i => x (e i)) B := by
  classical
  funext i
  simp [OAI.Paper320.flip]

theorem flip_reindex_singleton {J : Type} (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => OAI.Paper320.flip x {e i} (e a)) =
      OAI.Paper320.flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}





end ThreeBoundWitness








end
end Sensitivity213981Formal


