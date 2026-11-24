-- Prove2me | Definitions.Def_CSL_Circuit_Composition_TensorLiftProgram
-- name    : CSL_Circuit_Composition_TensorLiftProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:38:09.783449+00:00
-- url     : https://prove2.me/theorems/1bc6e349-bb6d-4f53-bd61-5ab3c130437a
-- title:
--   Coded sorting library: Circuit / Composition / TensorLiftProgram
-- statement:
--   Module `CodedSorting.Circuit.Composition.TensorLiftProgram` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # The helper-pool schedule for three cyclic copies
--
--   Pool `(i,b,c)` is used once in each globally separated round.  The three
--   associated blocks are `(i,b,c)`, `(i-1,b,pi c)`, and `(i+1,pi b,pi c)`.
--   In a block triple the first component names the data copy.  The last two
--   components label the coordinates following the currently processed axis;
--   the processed axis in rounds one, two, and three is respectively the copy
--   label, its successor, and its second successor.
--
--   These are scheduling facts only.  Orthogonality of the lines, monotonicity of
--   their frames, restoration of dirty helper contents, and the rank charge must
--   be established separately before this schedule is used in the construction.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Composition.TensorLiftProgram

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Parameters_Counts
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.NormNum
import Definitions.Def_CSL_Circuit_Local_LocalPhysicalSemantics

section ThreeCopySchedule
/-!
# The helper-pool schedule for three cyclic copies

Pool `(i,b,c)` is used once in each globally separated round.  The three
associated blocks are `(i,b,c)`, `(i-1,b,pi c)`, and `(i+1,pi b,pi c)`.
In a block triple the first component names the data copy.  The last two
components label the coordinates following the currently processed axis;
the processed axis in rounds one, two, and three is respectively the copy
label, its successor, and its second successor.

These are scheduling facts only.  Orthogonality of the lines, monotonicity of
their frames, restoration of dirty helper contents, and the rank charge must
be established separately before this schedule is used in the construction.
-/

namespace CSL.Construction.ThreeCopySchedule

abbrev Copy := Fin 3
abbrev Line := Fin 111
abbrev Pool := Copy × (Line × Line)
abbrev Block := Copy × (Line × Line)
abbrev DataStream := Copy × (Fin 2 × (Line × (Line × Line)))
abbrev HelperStream := Pool × Fin 439
abbrev IndependentStream := DataStream ⊕ HelperStream

/-- Add one to a copy label, cyclically modulo three. -/
def nextCopy : Equiv.Perm Copy where
  toFun i := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨(i.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide
  right_inv := by decide

theorem nextCopy_three (i : Copy) : nextCopy (nextCopy (nextCopy i)) = i := by
  revert i
  decide

def roundOne : Pool ≃ Block := Equiv.refl _

def roundTwo (pi : Equiv.Perm Line) : Pool ≃ Block :=
  Equiv.prodCongr nextCopy.symm (Equiv.prodCongr (Equiv.refl _) pi)

def roundThree (pi : Equiv.Perm Line) : Pool ≃ Block :=
  Equiv.prodCongr nextCopy (Equiv.prodCongr pi pi)

theorem roundOne_assignment (i : Copy) (b c : Line) :
    roundOne (i, b, c) = (i, b, c) := rfl

theorem roundTwo_assignment (pi : Equiv.Perm Line) (i : Copy) (b c : Line) :
    roundTwo pi (i, b, c) = (nextCopy.symm i, b, pi c) := rfl

theorem roundThree_assignment (pi : Equiv.Perm Line) (i : Copy) (b c : Line) :
    roundThree pi (i, b, c) = (nextCopy i, pi b, pi c) := rfl

/-- All three uses of a pool process the same ambient tensor coordinate. -/
theorem roundTwo_processes_pool_coordinate (pi : Equiv.Perm Line) (pool : Pool) :
    nextCopy ((roundTwo pi pool).1) = pool.1 := by
  simp [roundTwo]

theorem roundThree_processes_pool_coordinate (pi : Equiv.Perm Line) (pool : Pool) :
    nextCopy (nextCopy ((roundThree pi pool).1)) = pool.1 := by
  exact nextCopy_three pool.1

/-- No two pools are assigned to the same local block in a round. -/
theorem roundOne_injective : Function.Injective roundOne := roundOne.injective

theorem roundTwo_injective (pi : Equiv.Perm Line) :
    Function.Injective (roundTwo pi) := (roundTwo pi).injective

theorem roundThree_injective (pi : Equiv.Perm Line) :
    Function.Injective (roundThree pi) := (roundThree pi).injective

private theorem equiv_unique_preimage (e : Pool ≃ Block) (block : Block) :
    ∃! pool : Pool, e pool = block := by
  refine ⟨e.symm block, e.apply_symm_apply block, ?_⟩
  intro pool h
  apply e.injective
  simpa using h

/-- Every local block receives exactly one pool in each round. -/
theorem every_block_has_one_pool (pi : Equiv.Perm Line) (block : Block) :
    (∃! pool : Pool, roundOne pool = block) ∧
    (∃! pool : Pool, roundTwo pi pool = block) ∧
    (∃! pool : Pool, roundThree pi pool = block) := by
  exact ⟨equiv_unique_preimage roundOne block,
    equiv_unique_preimage (roundTwo pi) block,
    equiv_unique_preimage (roundThree pi) block⟩

/-- The inverse assignments identify the unique pool for any requested block. -/
theorem roundTwo_inverse_assignment (pi : Equiv.Perm Line)
    (i : Copy) (b c : Line) :
    (roundTwo pi).symm (i, b, c) = (nextCopy i, b, pi.symm c) := rfl

theorem roundThree_inverse_assignment (pi : Equiv.Perm Line)
    (i : Copy) (b c : Line) :
    (roundThree pi).symm (i, b, c) =
      (nextCopy.symm i, pi.symm b, pi.symm c) := rfl

theorem pool_count : Fintype.card Pool = 3 * 111 ^ 2 := by
  norm_num [Pool, Copy, Line]

theorem helper_count : Fintype.card (Pool × Fin 439) = 16226757 := by
  norm_num [Pool, Copy, Line]

theorem invocation_count : Fintype.card (Fin 3 × Block) = 110889 := by
  norm_num [Block, Copy, Line]

theorem data_stream_count : Fintype.card DataStream = 8205786 := by
  norm_num [DataStream, Copy, Line]

/-- The schedule's declared independent-stream type has exactly the numerical
    stream count used by the exponent certificate. -/
theorem independent_stream_count :
    Fintype.card IndependentStream = CSL.Construction.streamCount := by
  norm_num [IndependentStream, DataStream, HelperStream, Pool, Copy, Line,
    CSL.Construction.streamCount_eq]

end CSL.Construction.ThreeCopySchedule
end ThreeCopySchedule

section TensorLiftProgram
/-! Programs for the three-copy construction. Each round applies the XOR instruction sequence to each disjoint coordinate slice. Original registers are indexed by ThreeCopySchedule.IndependentStream; temporary copies are allocated separately for each round and block. The theorem specifies how these programs transform register values. 







-/

set_option autoImplicit false

namespace CSL.Construction.TensorLiftProgram

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.ThreeCopySchedule
open CSL.Construction.LocalPhysicalSemantics

inductive Round where
  | first | second | third
  deriving DecidableEq

instance : Fintype Round :=
  ⟨{Round.first, Round.second, Round.third}, by intro x; cases x <;> simp⟩

abbrev Coordinates := Line × (Line × Line)
abbrev LocalReg := (Fin 2 × Line) ⊕ (Fin 439 ⊕ Fin 9)
abbrev TemporaryStream := Round × (Block × Fin 9)
abbrev GlobalReg := IndependentStream ⊕ TemporaryStream

noncomputable instance globalRegDecidableEq : DecidableEq GlobalReg := Classical.decEq _

/-- Structured word ports with the exact finite-certificate numbering. -/
def localOriginalIndex : (Fin 2 × Line) ⊕ Fin 439 ≃ OriginalReg :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def localPhysicalIndex : LocalReg ≃ PhysicalReg :=
  (Equiv.sumAssoc (Fin 2 × Line) (Fin 439) (Fin 9)).symm.trans
    (Equiv.sumCongr localOriginalIndex (Equiv.refl _))

/-- The three coordinates are recorded in cyclic order relative to the data
copy. The processed coordinate comes first in this view. -/
def coordinateView : Round → Coordinates ≃ Coordinates
  | .first => Equiv.refl _
  | .second =>
    { toFun := fun p => (p.2.1, p.2.2, p.1)
      invFun := fun p => (p.2.2, p.1, p.2.1)
      left_inv := by rintro ⟨a,b,c⟩; rfl
      right_inv := by rintro ⟨a,b,c⟩; rfl }
  | .third =>
    { toFun := fun p => (p.2.2, p.1, p.2.1)
      invFun := fun p => (p.2.1, p.2.2, p.1)
      left_inv := by rintro ⟨a,b,c⟩; rfl
      right_inv := by rintro ⟨a,b,c⟩; rfl }

/-- The middle XOR round reverses the source and target banks. -/
def bankView : Round → Equiv.Perm (Fin 2)
  | .first => Equiv.refl _
  | .second => Equiv.swap 0 1
  | .third => Equiv.refl _

/-- Decomposing a data register into its fixed-coordinate block and varying
line index is a bijection, hence distinct fibers never overlap. -/
def fiberDataEquiv (round : Round) : Block × (Fin 2 × Line) ≃ DataStream where
  toFun p := (p.1.1, bankView round p.2.1,
    (coordinateView round).symm (p.2.2, p.1.2))
  invFun q := ((q.1, (coordinateView round q.2.2).2),
    (bankView round).symm q.2.1, (coordinateView round q.2.2).1)
  left_inv := by
    rintro ⟨⟨i,b,c⟩,bank,a⟩
    simp
  right_inv := by
    rintro ⟨i,bank,a,b,c⟩
    simp

def fiberMap (round : Round) (assignment : Pool ≃ Block) :
    Block × LocalReg → GlobalReg
  | (block, .inl data) => .inl (.inl (fiberDataEquiv round (block, data)))
  | (block, .inr (.inl helper)) => .inl (.inr (assignment.symm block, helper))
  | (block, .inr (.inr temporary)) => .inr (round, block, temporary)

theorem fiberMap_injective (round : Round) (assignment : Pool ≃ Block) :
    Function.Injective (fiberMap round assignment) := by
  rintro ⟨b, d | h | t⟩ ⟨c, e | j | u⟩ heq
  all_goals simp only [fiberMap, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl] at heq
  · have hh := (fiberDataEquiv round).injective heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hh
    rfl
  · obtain ⟨hb, rfl⟩ := Prod.mk.inj heq
    have hc := assignment.symm.injective hb
    subst c
    rfl
  · obtain ⟨_, hb, rfl⟩ := Prod.mk.inj heq
    rfl

def fiberEmbedding (round : Round) (assignment : Pool ≃ Block) (block : Block) :
    LocalReg ↪ GlobalReg where
  toFun r := fiberMap round assignment (block, r)
  inj' := by
    intro r s h
    exact congrArg Prod.snd (fiberMap_injective round assignment h)

theorem fiberEmbedding_disjoint (round : Round) (assignment : Pool ≃ Block)
    (b c : Block) (hbc : b ≠ c) (r s : LocalReg) :
    fiberEmbedding round assignment b r ≠ fiberEmbedding round assignment c s := by
  intro h
  exact hbc (congrArg Prod.fst (fiberMap_injective round assignment h))

/-- Only actual lifted word XOR gates occur in a round. -/
noncomputable def roundProgram (word : List (XorGate LocalReg))
    (round : Round) (assignment : Pool ≃ Block) : List (XorGate GlobalReg) :=
  partitionProgram (fiberEmbedding round assignment) Finset.univ.toList word

/-- Exact executable semantics on a fiber; every fiber occurs once. -/
theorem roundProgram_fiber (word : List (XorGate LocalReg))
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (block : Block) :
    runProgram (roundProgram word round assignment) state ∘
      fiberEmbedding round assignment block =
    runProgram word (state ∘ fiberEmbedding round assignment block) := by
  have h := partitionProgram_restrict (fiberEmbedding round assignment)
    (fiberEmbedding_disjoint round assignment) Finset.univ.toList
    (Finset.nodup_toList _) word state block
  simpa [roundProgram] using h

/-- The exact word contract, including restoration of arbitrary dirty
helper values. Temporary outputs intentionally have no restoration premise. -/
structure LocalCorrect (word : List (XorGate LocalReg)) : Prop where
  source : ∀ state a,
    runProgram word state (.inl (0,a)) = state (.inl (0,a))
  target : ∀ state a,
    runProgram word state (.inl (1,a)) = state (.inl (1,a)) + state (.inl (0,a))
  helper : ∀ state h,
    runProgram word state (.inr (.inl h)) = state (.inr (.inl h))

theorem roundProgram_source (word : List (XorGate LocalReg)) (hc : LocalCorrect word)
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (block : Block) (a : Line) :
    runProgram (roundProgram word round assignment) state
      (fiberEmbedding round assignment block (.inl (0,a))) =
    state (fiberEmbedding round assignment block (.inl (0,a))) := by
  exact (congrFun (roundProgram_fiber word round assignment state block) (.inl (0,a))).trans
    (hc.source _ a)

theorem roundProgram_target (word : List (XorGate LocalReg)) (hc : LocalCorrect word)
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (block : Block) (a : Line) :
    runProgram (roundProgram word round assignment) state
      (fiberEmbedding round assignment block (.inl (1,a))) =
    state (fiberEmbedding round assignment block (.inl (1,a))) +
      state (fiberEmbedding round assignment block (.inl (0,a))) := by
  exact (congrFun (roundProgram_fiber word round assignment state block) (.inl (1,a))).trans
    (hc.target _ a)

theorem roundProgram_helper (word : List (XorGate LocalReg)) (hc : LocalCorrect word)
    (round : Round) (assignment : Pool ≃ Block) (state : GlobalReg → Bit)
    (pool : Pool) (h : Fin 439) :
    runProgram (roundProgram word round assignment) state (.inl (.inr (pool,h))) =
      state (.inl (.inr (pool,h))) := by
  have ht := (congrFun (roundProgram_fiber word round assignment state (assignment pool))
    (.inr (.inl h))).trans (hc.helper _ h)
  simpa [fiberEmbedding, fiberMap] using ht

end CSL.Construction.TensorLiftProgram
end TensorLiftProgram


