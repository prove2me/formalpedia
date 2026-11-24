-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_GateInvariants
-- name    : Sensitivity214439_Phase0_Solutions_GateInvariants
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:40.601819+00:00
-- url     : https://prove2.me/theorems/085553f1-c279-4f57-b81b-53eaeeca04de
-- title:
--   Recipe nesting, row separation, and strict uniqueness conditions
-- statement:
--   Compatible guard counts at ranks $i\le j$ are ordered soft counts within the stronger allowance. Equal soft cutoffs force equal counts; a stronger hard cutoff below either relevant soft cutoff forces its count to be zero.
--
--   A nesting recipe has antitone soft and hard cutoffs and transports every accepted stronger target assignment to a permitted weaker assignment that is componentwise no larger. A finite scalar version states the same checks for bounded failure counts and one target function.
--
--   A guard family separates rows when every distinct pair has a check in at least one direction inspecting a socket of the other row. A strict recipe above core $c$ forbids guard activity at a fixed cutoff and requires all targets to reach at least that cutoff. The finite scalar strict predicate gives the corresponding bounded-count version. These conditions are the structural hypotheses used to preserve nesting and strict color uniqueness through a gate stage.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GateInvariants.lean lines 52–176; SHA256 203148c2a2707c40a0d239913f4dc7b44ef2cce2545e7545006824d075c324e5; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
# Nesting and strict identities of the actual gates

The finite recipe conditions below describe every possible pair of soft guard
counts at two grades. They include the extra zero-count information supplied
by a hard cutoff, so the warm rows can be checked without replacing their
semantics by a stronger condition.
-/

namespace SensitivityRankedConstruction

noncomputable section
open scoped Classical









def GuardCompatible {L : ℕ} (soft hard allowance : Fin L → ℕ)
    (i j : Fin L) (f g : ℕ) : Prop :=
  f ≤ g ∧ g ≤ allowance j ∧
  (soft i = soft j → f = g) ∧
  (hard j ≤ soft i → f = 0) ∧
  (hard j ≤ soft j → g = 0)

structure RecipeNesting {S : Type} {L : ℕ} (recipe : GateRecipe S L) : Prop where
  soft_antitone : Antitone recipe.soft
  hard_antitone : Antitone recipe.hard
  assignments : ∀ (i j : Fin L) (f g : ℕ), i ≤ j →
    GuardCompatible recipe.soft recipe.hard recipe.allowance i j f g →
    f ≤ recipe.allowance i ∧
    ∀ assignment ∈ recipe.targets j g,
      ∃ weaker ∈ recipe.targets i f, ∀ s, weaker s ≤ assignment s



/-- A finite scalar check suffices for unary targets, and applying the same
check to both components suffices for a matching paired target. -/
def FiniteScalarNesting {L : ℕ} (bound : ℕ)
    (soft hard allowance : Fin L → ℕ) (target : Fin L → ℕ → Fin L) : Prop :=
  (∀ j, allowance j < bound) ∧
  (∀ i j, i ≤ j → soft j ≤ soft i ∧ hard j ≤ hard i) ∧
  ∀ (i j : Fin L) (f g : Fin bound), i ≤ j →
    GuardCompatible soft hard allowance i j f.val g.val →
    f.val ≤ allowance i ∧ target i f.val ≤ target j g.val







def SeparatesRows {V S : Type} (guards : GuardFamily V S) : Prop :=
  ∀ v w, v ≠ w →
    (∃ check ∈ guards v, ∃ s, (w, s) ∈ check) ∨
    (∃ check ∈ guards w, ∃ s, (v, s) ∈ check)

structure StrictRecipe {S : Type} {L : ℕ} (recipe : GateRecipe S L)
    (core cutoff : ℕ) : Prop where
  forbids : ∀ j : Fin L, core ≤ j.val →
    (recipe.allowance j = 0 ∧ recipe.soft j ≤ cutoff) ∨ recipe.hard j ≤ cutoff
  targets : ∀ (j : Fin L) (f : ℕ), core ≤ j.val → f ≤ recipe.allowance j →
    ∀ assignment ∈ recipe.targets j f, ∀ s, cutoff ≤ (assignment s).val

def FiniteScalarStrict {L : ℕ} (bound core cutoff : ℕ)
    (soft hard allowance : Fin L → ℕ) (target : Fin L → ℕ → Fin L) : Prop :=
  (∀ j, allowance j < bound) ∧
  (∀ j : Fin L, core ≤ j.val →
    (allowance j = 0 ∧ soft j ≤ cutoff) ∨ hard j ≤ cutoff) ∧
  ∀ (j : Fin L) (f : Fin bound), core ≤ j.val → f.val ≤ allowance j →
    cutoff ≤ (target j f.val).val














end
end SensitivityRankedConstruction


