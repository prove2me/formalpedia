-- Prove2me | Definitions.Def_BalanceSpecificaton_Forbidden
-- name    : BalanceSpecificaton_Forbidden
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:33:44.191859+00:00
-- url     : https://prove2.me/theorems/cb6fe11a-c16e-46f4-b851-971060c793c8
-- title:
--   Forbidden
-- statement:
--   Definitions and structural lemmas for Forbidden, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Forbidden.lean

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
variable {A : Type*}
def wordCylinder (w : Word A) (k : ℤ) : Set (Configuration A) :=
  {x | block x k w.length = w}
theorem mem_wordCylinder_iff {w : Word A} {k : ℤ} {x : Configuration A} :
    x ∈ wordCylinder w k ↔ ∀ i : Fin w.length, x (k + i.val) = w[i.val] := by
  constructor
  · intro h i
    have hi := List.getElem_of_eq h (show i.val < (block x k w.length).length by
      simpa only [length_block] using i.isLt)
    simpa only [block, List.getElem_ofFn] using hi
  · intro h
    apply List.ext_getElem
    · exact length_block x k w.length
    · intro i _ hi
      simpa only [block, List.getElem_ofFn] using h ⟨i, hi⟩
theorem wordCylinder_eq_iInter (w : Word A) (k : ℤ) :
    wordCylinder w k = ⋂ i : Fin w.length,
      {x : Configuration A | x (k + i.val) = w[i.val]} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_wordCylinder_iff]
variable [TopologicalSpace A] [DiscreteTopology A]
theorem isOpen_wordCylinder (w : Word A) (k : ℤ) : IsOpen (wordCylinder w k) := by
  rw [wordCylinder_eq_iInter]
  apply isOpen_iInter_of_finite
  intro i
  change IsOpen ((fun x : Configuration A => x (k + (i.val : ℤ))) ⁻¹'
    ({w[i.val]} : Set A))
  exact (isOpen_discrete _).preimage (continuous_apply _)
def forbiddenConfigurations (F : Set (Word A)) : Set (Configuration A) :=
  {x | ∀ w ∈ F, ∀ k : ℤ, block x k w.length ≠ w}
theorem isClosed_forbiddenConfigurations (F : Set (Word A)) :
    IsClosed (forbiddenConfigurations F) := by
  have heq : forbiddenConfigurations F =
      ⋂ (w : Word A) (_ : w ∈ F) (k : ℤ), (wordCylinder w k)ᶜ := by
    ext x
    simp only [forbiddenConfigurations, wordCylinder, Set.mem_ofPred_eq,
      Set.mem_iInter, Set.mem_compl_iff]
  rw [heq]
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    isClosed_iInter fun k => (isOpen_wordCylinder w k).isClosed_compl
omit [TopologicalSpace A] [DiscreteTopology A] in
theorem shift_mem_forbiddenConfigurations {F : Set (Word A)} {x : Configuration A}
    (hx : x ∈ forbiddenConfigurations F) (k : ℤ) :
    SymbolicDynamics.FullShift.shift k x ∈ forbiddenConfigurations F := by
  intro w hw l
  rw [block_shift]
  exact hx w hw (k + l)
def forbiddenShift (F : Set (Word A)) : ShiftSpace A where
  carrier := forbiddenConfigurations F
  isClosed := isClosed_forbiddenConfigurations F
  mapsTo := fun k _ hx => shift_mem_forbiddenConfigurations hx k
end BalanceSpecification


