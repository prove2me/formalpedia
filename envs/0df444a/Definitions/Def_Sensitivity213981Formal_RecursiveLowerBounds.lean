-- Prove2me | Definitions.Def_Sensitivity213981Formal_RecursiveLowerBounds
-- name    : Sensitivity213981Formal_RecursiveLowerBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:09:51.851525+00:00
-- url     : https://prove2.me/theorems/049b8703-190e-41cd-b59b-9521184f6c45
-- title:
--   Recursive Lower Bounds — sensitivity certificate definitions
-- statement:
--   The definitions for Recursive Lower Bounds in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundWitness.MinMaxRecipe`, `ThreeBoundWitness.minmaxTarget`, `ThreeBoundWitness.MinMaxRecipe.stage`, `ThreeBoundWitness.towerFamily`, `ThreeBoundWitness.CommonWitnesses`, `ThreeBoundWitness.CommonWitnesses.reindex`, `ThreeBoundWitness.IterProd`, `ThreeBoundWitness.iterProdFintype`, `ThreeBoundWitness.tower_input_dimension`, `ThreeBoundWitness.card_iterProd`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RecursiveLowerBounds.lean, lines 1–227.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section
/-
Concrete arbitrary-depth graded/min-max constructions and their lower bounds.
Every recipe sequence below defines total Boolean functions.  No sensitivity
upper bound is claimed; the finite sensitivity-profile soundness remains a
separate obligation for the requested separation exponents.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundWitness
open OAI.Paper320

def IterProd (A : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => A × IterProd A n

instance iterProdFintype (A : Type) [Fintype A] : ∀ n : ℕ, Fintype (IterProd A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
      letI := iterProdFintype A n
      exact inferInstanceAs (Fintype (A × IterProd A n))

theorem card_iterProd (A : Type) [Fintype A] (n : ℕ) :
    Fintype.card (IterProd A n) = (Fintype.card A)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card (A × IterProd A n) = _
      rw [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

structure MinMaxRecipe (L V : Type) where
  Adj : V → V → Prop
  loopless : ∀ v, ¬ Adj v v
  label : V → V → Bool
  guard : L → L
  tolerance : L → ℕ
  lower : L → ℕ → L
  upper : L → ℕ → L

def minmaxTarget {L I : Type} (F : L → (I → Bool) → Bool)
    (t u : L → ℕ → L) (l : L) (d : ℕ) (x y : I → Bool) : Bool :=
  F (t l d) x && F (t l d) y && (F (u l d) x || F (u l d) y)

def MinMaxRecipe.stage {L I V : Type} (r : MinMaxRecipe L V)
    (F : L → (I → Bool) → Bool) : Stage L I V where
  Adj := r.Adj
  loopless := r.loopless
  label := r.label
  guard := r.guard
  tolerance := r.tolerance
  target := minmaxTarget F r.lower r.upper







noncomputable def towerFamily {L V : Type} [Fintype V]
    (r : ℕ → MinMaxRecipe L V) : ∀ n : ℕ,
      L → (IterProd (V × Bool) n → Bool) → Bool
  | 0 => fun _ x => x ()
  | n+1 => parent ((r n).stage (towerFamily r n)) (towerFamily r n)

structure CommonWitnesses {L I : Type} (F : L → (I → Bool) → Bool) (A B : Type) where
  zero : I → Bool
  positive : I → Bool
  positiveBits : A ↪ I
  blocks : B → Finset I
  zero_rejects : ∀ l, F l zero = false
  positive_accepts : ∀ l, F l positive = true
  positive_off : ∀ a l, F l (flip positive {positiveBits a}) = false
  blocks_nonempty : ∀ b, (blocks b).Nonempty
  blocks_disjoint : ∀ a b, a ≠ b → Disjoint (blocks a) (blocks b)
  blocks_on : ∀ b l, F l (flip zero (blocks b)) = true

noncomputable def CommonWitnesses.reindex {L I J A B : Type}
    {F : L → (I → Bool) → Bool} (w : CommonWitnesses F A B) (e : I ≃ J) :
    CommonWitnesses (fun l => ThreeBoundWitness.reindex e (F l)) A B where
  zero := fun j => w.zero (e.symm j)
  positive := fun j => w.positive (e.symm j)
  positiveBits := w.positiveBits.trans e.toEmbedding
  blocks := fun b => (w.blocks b).map e.toEmbedding
  zero_rejects l := by
    simpa only [ThreeBoundWitness.reindex, Equiv.symm_apply_apply] using w.zero_rejects l
  positive_accepts l := by
    simpa only [ThreeBoundWitness.reindex, Equiv.symm_apply_apply] using w.positive_accepts l
  positive_off a l := by
    change F l (fun i => OAI.Paper320.flip (fun j => w.positive (e.symm j))
      {e (w.positiveBits a)} (e i)) = false
    rw [flip_reindex_singleton]
    simpa only [Equiv.symm_apply_apply] using w.positive_off a l
  blocks_nonempty b := (w.blocks_nonempty b).map (f := e.toEmbedding)
  blocks_disjoint a b hab := (Finset.disjoint_map e.toEmbedding).mpr (w.blocks_disjoint a b hab)
  blocks_on b l := by
    change F l (fun i => OAI.Paper320.flip (fun j => w.zero (e.symm j))
      ((w.blocks b).map e.toEmbedding) (e i)) = true
    rw [flip_reindex]
    simpa only [Equiv.symm_apply_apply] using w.blocks_on b l









theorem tower_input_dimension {V : Type} [Fintype V] (n : ℕ) :
    Fintype.card (IterProd (V × Bool) n) = (2 * Fintype.card V)^n := by
  simp only [card_iterProd, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]





end ThreeBoundWitness








end
end Sensitivity213981Formal


