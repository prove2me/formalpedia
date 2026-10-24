-- Prove2me | Definitions.Def_PricingWithTips3DM_d3fa2b92541a58df50ce1d93
-- name    : PricingWithTips3DM_d3fa2b92541a58df50ce1d93
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:35:54.142192+00:00
-- url     : https://prove2.me/theorems/2f97e624-7ddd-46dc-8b67-043fc5ac3708
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Logic.OneInThree3Sat.Monotone
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_700c4ea915bd5ddbfce98a0b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# MONOTONE ONE-IN-THREE 3SAT

ONE-IN-THREE 3SAT with no negated literal anywhere — Garey–Johnson's comment
under [LO4], "remains NP-complete even if no `c ∈ C` contains a negated
literal".

Dropping negation costs exactly-one satisfaction less than it costs plain
satisfaction, which is the point of the entry: an all-positive formula is
trivially satisfiable, and trivially not-all-equal satisfiable as soon as its
clauses have two variables, but an all-positive *exactly-one* instance is a
genuine combinatorial question. It is in fact an exact cover: read each clause
as a three-element set of variables, and an assignment making exactly one
literal of each clause true is a set of variables meeting every clause once.
That is the shape in which this problem reaches the set-covering entries.

Not to be confused with MONOTONE 3SAT (Gold 1974, the comment under [LO2]),
where a clause must be all-positive *or* all-negative and satisfaction is the
ordinary one.

Hardness proof (in `Monotone/`): from ONE-IN-THREE 3SAT
(`FromOneInThree3Sat.lean`, one complementary variable per variable; certified
in `FromOneInThree3Sat/Certified.lean`).
-/

namespace Hardness

variable {V W : Type*}

/-- A formula is *positive* when no literal in it is negated. -/
def CNF.Positive (φ : CNF V) : Prop :=
  ∀ c ∈ φ, ∀ l ∈ c, l.polarity = true

instance [DecidableEq V] (φ : CNF V) : Decidable φ.Positive := by
  unfold CNF.Positive
  infer_instance

/-- Positivity survives a relabeling in both directions: a naming map touches
variables, never polarities. The invariance lemma the representation pair and
every gadget certificate consume. -/
theorem CNF.positive_relabel {f : V → W} {φ : CNF V} :
    (φ.relabel f).Positive ↔ φ.Positive := by
  constructor
  · intro h c hc l hl
    exact h (c.map (Literal.relabel f)) (List.mem_map_of_mem hc) (l.relabel f)
      (List.mem_map_of_mem hl)
  · intro h c hc l hl
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    exact h d hd l₀ hl₀

/-- MONOTONE ONE-IN-THREE 3SAT: exactly-one satisfiability of a formula whose
clauses have three literals, none of them negated. In the promise-free
formulation of `Problem.restrict`, so a formula with a negated literal is
simply a no-instance. -/
def MONOTONE_ONE_IN_THREE_SAT3 : Problem SatInstance :=
  ONE_IN_THREE_SAT3.restrict fun x ↦ x.φ.Positive

end Hardness


