-- Prove2me | Definitions.Def_BalanceSpecificaton_Coded
-- name    : BalanceSpecificaton_Coded
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:33:36.702796+00:00
-- url     : https://prove2.me/theorems/b9070ea6-5040-43ab-9da4-d0c25dfcaa5e
-- title:
--   Coded
-- statement:
--   Definitions and structural lemmas for Coded, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Coded.lean

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_block_shift

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BalanceSpecification
variable {A : Type*}
def generatedWords (C : Set (Word A)) : Set (Word A) :=
  {w | ∃ ws : List (Word A), (∀ v ∈ ws, v ∈ C) ∧ ws.flatten = w}
def IsConcatenation (C : Set (Word A)) (x : Configuration A) : Prop :=
  ∃ p : ℤ → ℤ, StrictMono p ∧ ∀ i : ℤ,
    block x (p i) ((p (i + 1) - p i).toNat) ∈ C
theorem isConcatenation_shift {C : Set (Word A)} {x : Configuration A}
    (hx : IsConcatenation C x) (k : ℤ) :
    IsConcatenation C (SymbolicDynamics.FullShift.shift k x) := by
  obtain ⟨p, hp, hwords⟩ := hx
  refine ⟨fun i => p i - k, fun a b hab => sub_lt_sub_right (hp hab) k, ?_⟩
  intro i
  have hlen : (p (i + 1) - k - (p i - k)) = p (i + 1) - p i := by ring
  rw [hlen, block_shift]
  have hstart : k + (p i - k) = p i := by ring
  rw [hstart]
  exact hwords i
def codedShift [TopologicalSpace A] (C : Set (Word A)) : ShiftSpace A where
  carrier := closure {x | IsConcatenation C x}
  isClosed := isClosed_closure
  mapsTo := fun k => (show Set.MapsTo (SymbolicDynamics.FullShift.shift k)
    {x | IsConcatenation C x} {x | IsConcatenation C x} from
      fun _ hx => isConcatenation_shift hx k).closure
        (SymbolicDynamics.FullShift.continuous_shift k)
def IsCoded [TopologicalSpace A] (X : ShiftSpace A) : Prop :=
  ∃ C : Set (Word A), (codedShift C).carrier = X.carrier
def periodicConfiguration (w : Word A) (hw : 0 < w.length) : Configuration A :=
  fun i => w[(i % (w.length : ℤ)).toNat]'(by
    have hp : (0 : ℤ) < w.length := Nat.cast_pos.mpr hw
    have hlow := Int.emod_nonneg i hp.ne'
    have hhigh := Int.emod_lt_of_pos i hp
    omega)
end BalanceSpecification


