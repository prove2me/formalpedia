-- Prove2me | Definitions.Def_CSL_Circuit_Local_ReverseLocalProgram
-- name    : CSL_Circuit_Local_ReverseLocalProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:55:06.856271+00:00
-- url     : https://prove2.me/theorems/a9b49e2f-73a4-42ef-b4a0-e57a3f03953d
-- title:
--   Coded sorting library: Circuit / Local / ReverseLocalProgram
-- statement:
--   Module `CodedSorting.Circuit.Local.ReverseLocalProgram` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Connecting the finite physical word to the tensor local contract
--
--   This is a change of register coordinates, with no new numeric replay claim.
--   It accepts the original-register semantics of an actual physical word and
--   produces precisely the contract consumed by the executable fiber programs.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.ReverseLocalProgram

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Composition_TensorLiftProgram

section LocalPhysicalContract
/-!
# Connecting the finite physical word to the tensor local contract

This is a change of register coordinates, with no new numeric replay claim.
It accepts the original-register semantics of an actual physical word and
produces precisely the contract consumed by the executable fiber programs.
-/

set_option autoImplicit false

namespace CSL.Construction.LocalPhysicalContract

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.FiniteCertificate CSL.Construction.FiniteSemantics
open CSL.Construction.ExplicitCopies CSL.Construction.LocalPhysicalSemantics
open CSL.Construction.TensorLiftProgram CSL.Construction.ThreeCopySchedule

def sourceIndex (a : Line) : OriginalReg := ⟨a.val, by
  have h := a.isLt
  change a.val < 661
  omega⟩

def targetIndex (a : Line) : OriginalReg := ⟨111 + a.val, by
  have h := a.isLt
  change 111 + a.val < 661
  omega⟩

def helperIndex (h : Fin 439) : OriginalReg := ⟨222 + h.val, by
  have hh := h.isLt
  change 222 + h.val < 661
  omega⟩

theorem index_source (a : Line) :
    localPhysicalIndex (.inl (0,a)) = .inl (sourceIndex a) := by
  apply congrArg Sum.inl
  apply Fin.ext
  simp [localPhysicalIndex, localOriginalIndex, sourceIndex, finProdFinEquiv, finSumFinEquiv]
  rfl

theorem index_target (a : Line) :
    localPhysicalIndex (.inl (1,a)) = .inl (targetIndex a) := by
  apply congrArg Sum.inl
  apply Fin.ext
  simp [localPhysicalIndex, localOriginalIndex, targetIndex, finProdFinEquiv,
    finSumFinEquiv, Nat.add_comm]
  rfl

theorem index_helper (h : Fin 439) :
    localPhysicalIndex (.inr (.inl h)) = .inl (helperIndex h) := rfl

@[simp] theorem index_symm_source (a : Line) :
    localPhysicalIndex.symm (.inl (sourceIndex a)) = .inl (0,a) := by
  rw [← index_source, Equiv.symm_apply_apply]

@[simp] theorem index_symm_target (a : Line) :
    localPhysicalIndex.symm (.inl (targetIndex a)) = .inl (1,a) := by
  rw [← index_target, Equiv.symm_apply_apply]

@[simp] theorem index_symm_helper (h : Fin 439) :
    localPhysicalIndex.symm (.inl (helperIndex h)) = .inr (.inl h) := by
  rw [← index_helper, Equiv.symm_apply_apply]

theorem localOutput_source (input : OriginalReg → Bit) (a : Line) :
    localOutput input (sourceIndex a) = input (sourceIndex a) := by
  have ha := a.isLt
  simp [localOutput, sourceIndex, portCount, show ¬111 ≤ a.val by omega]

theorem localOutput_target (input : OriginalReg → Bit) (a : Line) :
    localOutput input (targetIndex a) = input (targetIndex a) + input (sourceIndex a) := by
  have ha := a.isLt
  have hp : previousPort (targetIndex a) = sourceIndex a := by
    apply Fin.ext
    simp [previousPort, targetIndex, sourceIndex, portCount]
  simp only [localOutput]
  rw [if_pos (by simp only [targetIndex, portCount]; constructor <;> omega), hp]

theorem localOutput_helper (input : OriginalReg → Bit) (h : Fin 439) :
    localOutput input (helperIndex h) = input (helperIndex h) := by
  simp [localOutput, helperIndex, portCount, show ¬222 + h.val < 222 by omega]

noncomputable def structuredProgram (word : List (XorGate PhysicalReg)) :
    List (XorGate LocalReg) := word.map (XorGate.lift localPhysicalIndex.symm.toEmbedding)

theorem structuredProgram_at (word : List (XorGate PhysicalReg))
    (state : LocalReg → Bit) (r : LocalReg) :
    runProgram (structuredProgram word) state r =
      runProgram word (state ∘ localPhysicalIndex.symm) (localPhysicalIndex r) := by
  have h := congrFun (runProgram_lift_restrict localPhysicalIndex.symm.toEmbedding word state)
    (localPhysicalIndex r)
  simpa [structuredProgram] using h

/-- An arbitrary physical word with the stated 661-register semantics is a
valid local word for every tensor fiber, even on dirty temporary states. -/
theorem localCorrect_of_physical (word : List (XorGate PhysicalReg))
    (hword : ∀ state, originalState (runProgram word state) = localOutput (originalState state)) :
    LocalCorrect (structuredProgram word) := by
  constructor
  · intro state a
    rw [structuredProgram_at, index_source]
    have h := congrFun (hword (state ∘ localPhysicalIndex.symm)) (sourceIndex a)
    rw [localOutput_source] at h
    change _ = state (localPhysicalIndex.symm (.inl (sourceIndex a))) at h
    simpa only [originalState, Function.comp_apply, index_symm_source] using h
  · intro state a
    rw [structuredProgram_at, index_target]
    have h := congrFun (hword (state ∘ localPhysicalIndex.symm)) (targetIndex a)
    rw [localOutput_target] at h
    change _ = state (localPhysicalIndex.symm (.inl (targetIndex a))) +
      state (localPhysicalIndex.symm (.inl (sourceIndex a))) at h
    simpa only [originalState, Function.comp_apply, index_symm_target, index_symm_source] using h
  · intro state h
    rw [structuredProgram_at, index_helper]
    have hh := congrFun (hword (state ∘ localPhysicalIndex.symm)) (helperIndex h)
    rw [localOutput_helper] at hh
    change _ = state (localPhysicalIndex.symm (.inl (helperIndex h))) at hh
    simpa only [originalState, Function.comp_apply, index_symm_helper] using hh

end CSL.Construction.LocalPhysicalContract
end LocalPhysicalContract

section ReverseLocalProgram
/-!
# Reverse the reduced XOR word, then insert fresh overwrite copies

Reduced XOR gates are involutions when their controls avoid their targets.
The local shear is itself an involution. Therefore the reversed reduced word
has the same local payload semantics. The physical middle word is obtained
by inserting fresh overwrite copies before its reversed scatter segment.

The already expanded physical word must not be reversed as an inverse:
overwrite copies are not invertible. Complementing matrix labels changes no
payload operation and is verified by the separate geometry modules.
-/

set_option autoImplicit false

namespace CSL.Construction.ReverseLocalProgram

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.FiniteCertificate CSL.Construction.SymbolicXor
open CSL.Construction.FiniteSemantics CSL.Construction.ExplicitCopies
open CSL.Construction.ScatterCopies CSL.Construction.LocalPhysicalSemantics

private theorem bit_add_self (a : Bit) : a + a = 0 :=
  (by decide : ∀ b : Bit, b + b = 0) a

section Reverse

variable {R : Type*} [DecidableEq R]

def ControlsAvoidTargets (g : XorGate R) : Prop :=
  ∀ r ∈ g.targets, ∀ c ∈ g.controls r, c ∉ g.targets

theorem xorGate_involutive (g : XorGate R) (h : ControlsAvoidTargets g) :
    Function.Involutive g.eval := by
  intro state
  funext r
  rw [XorGate.eval_eq_add_delta, XorGate.delta_eval g g state h,
    XorGate.eval_eq_add_delta, add_assoc, bit_add_self, add_zero]

theorem reverse_left_inverse (word : List (XorGate R))
    (hinv : ∀ g ∈ word, Function.Involutive g.eval) (state : R → Bit) :
    runProgram word.reverse (runProgram word state) = state := by
  induction word generalizing state with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.reverse_cons, runProgram_append, runProgram]
    rw [ih (fun h hh => hinv h (List.mem_cons_of_mem g hh))]
    exact hinv g (by simp) state

theorem reversed_word_of_involutive_semantics (word : List (XorGate R))
    (hinv : ∀ g ∈ word, Function.Involutive g.eval)
    (semantics : (R → Bit) → (R → Bit)) (hsem : Function.Involutive semantics)
    (hword : ∀ state, runProgram word state = semantics state) (state : R → Bit) :
    runProgram word.reverse state = semantics state := by
  have h := reverse_left_inverse word hinv (semantics state)
  rw [hword, hsem state] at h
  exact h

end Reverse

theorem compileGate_controls_avoid (n : Nat) (g : Gate)
    (hnot : g.destination ∉ g.sources) : ControlsAvoidTargets (compileGate n g) := by
  intro r hr c hc htarget
  simp only [compileGate, Finset.mem_filter, Finset.mem_univ, true_and] at htarget
  simp only [compileGate, sourceRegisters, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  exact hnot (htarget ▸ hc)

theorem compileProgram_involutive_gates (n : Nat) (word : Array Gate)
    (hnot : ∀ g ∈ word.toList, g.destination ∉ g.sources) :
    ∀ g ∈ compileProgram n word, Function.Involutive g.eval := by
  intro g hg
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hg
  exact xorGate_involutive _ (compileGate_controls_avoid n row (hnot row hrow))

theorem localOutput_involutive : Function.Involutive localOutput := by
  intro input
  funext r
  by_cases hr : portCount ≤ r.val ∧ r.val < 2 * portCount
  · have hprev : ¬ portCount ≤ (previousPort r).val := by
      simp only [previousPort]
      omega
    simp [localOutput, hr, hprev, add_assoc, bit_add_self]
  · simp [localOutput, hr]

theorem reversed_scalar_correct_of_certificate (word : Array Gate)
    (hreplay : runCoefficients word = coefficientExpected)
    (hnodup : ∀ g ∈ word.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ word.toList, ∀ s ∈ g.sources, s < registerCount)
    (hnot : ∀ g ∈ word.toList, g.destination ∉ g.sources)
    (input : OriginalReg → Bit) :
    runProgram (compileProgram registerCount word).reverse input = localOutput input := by
  exact reversed_word_of_involutive_semantics _
    (compileProgram_involutive_gates registerCount word hnot) localOutput
    localOutput_involutive
    (localProgram_correct_of_certificate word hreplay hnodup hbound) input

section Decomposition

variable {R T : Type*} [DecidableEq R] [DecidableEq T]

theorem reverse_reducedProgram (helper : T ↪ R) (before after : List (XorGate R))
    (rows : List (ScatterRow R T)) :
    (reducedProgram helper before after rows).reverse =
      reducedProgram helper after.reverse before.reverse rows.reverse := by
  simp [reducedProgram, reducedScatter, List.reverse_append, List.map_reverse,
    List.append_assoc]

end Decomposition

/-- New copies appear after the reversed old after-segment, immediately
before the reversed scatter rows. The old copy gates are never reversed. -/
noncomputable def reverseLocalPhysicalProgram (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg)) : List (XorGate PhysicalReg) :=
  localPhysicalProgram after.reverse before.reverse rows.reverse

theorem reverseLocalPhysical_original
    (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg))
    (hsafe : ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination)
    (state : PhysicalReg → Bit) :
    originalState (runProgram (reverseLocalPhysicalProgram before after rows) state) =
      runProgram (reducedProgram retainedHelper before after rows).reverse (originalState state) := by
  unfold reverseLocalPhysicalProgram localPhysicalProgram
  rw [expandedProgram_original retainedHelper allTemporaries allTemporaries_complete
    after.reverse before.reverse rows.reverse
    (fun row hr => hsafe row (List.mem_reverse.mp hr)), reverse_reducedProgram]

/-- Conditional consumer for the actual physical middle word, valid for
every original input and every dirty temporary input. -/
theorem reverseLocalPhysical_correct_of_certificate (word : Array Gate)
    (hreplay : runCoefficients word = coefficientExpected)
    (hnodup : ∀ g ∈ word.toList, g.sources.Nodup)
    (hbound : ∀ g ∈ word.toList, ∀ s ∈ g.sources, s < registerCount)
    (hnot : ∀ g ∈ word.toList, g.destination ∉ g.sources)
    (before after : List (XorGate OriginalReg))
    (rows : List (ScatterRow OriginalReg TemporaryReg))
    (hdecompose : compileProgram registerCount word =
      reducedProgram retainedHelper before after rows)
    (hsafe : ∀ row ∈ rows, ∀ t, retainedHelper t ≠ row.destination)
    (state : PhysicalReg → Bit) :
    originalState (runProgram (reverseLocalPhysicalProgram before after rows) state) =
      localOutput (originalState state) := by
  rw [reverseLocalPhysical_original before after rows hsafe, ← hdecompose]
  exact reversed_scalar_correct_of_certificate word hreplay hnodup hbound hnot (originalState state)

end CSL.Construction.ReverseLocalProgram
end ReverseLocalProgram


