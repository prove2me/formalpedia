-- Prove2me | Definitions.Def_PricingWithTips3DM_ddcced5313ed447b67330e23
-- name    : PricingWithTips3DM_ddcced5313ed447b67330e23
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:43.326025+00:00
-- url     : https://prove2.me/theorems/06f519fc-90d6-4031-9b41-639295987429
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Logic.Sat3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_559a735c0442b6eef1922892
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# 3-SAT

The bounded-width variant of CNF satisfiability: every clause may contain at
most three literals. A restriction of SAT in the sense of `Problem.restrict`,
promoted to its own catalog entry (as in Garey–Johnson) because of its role
as a source problem.

Hardness proof (in `Sat3/`): from SAT (`FromSat.lean`, clause splitting;
certified in `FromSat/Code.lean` and `FromSat/Adequacy.lean`).

Restriction (in `Sat3/`): `BoundedOcc.lean` — clauses of length two or three
and at most three occurrences per variable, hard from SAT and from 3SAT
(`BoundedOcc/FromSat.lean`).
-/

namespace Hardness

/-- 3SAT: SAT restricted to formulas of clause width at most three, in the
promise-free formulation of `Problem.restrict` — the width condition is
conjoined into the predicate rather than imposed on the instance type, so
`SAT3` is a problem over arbitrary `SatInstance`s (an instance with a wide
clause is simply a no-instance). -/
def SAT3 : Problem SatInstance :=
  SAT.restrict fun x ↦ ∀ c ∈ x.φ, c.length ≤ 3

/-- The formula consisting of the empty clause is unsatisfiable — a fixed
no-instance of SAT. -/
theorem not_satisfiable_emptyClause : ¬ CNF.Satisfiable ([[]] : CNF ℕ) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨l, hl, -⟩ := hσ [] (List.mem_singleton_self _)
  simp at hl

/-- 3SAT is a special case of SAT: hardness-even-if implies plain hardness.
The map is *not* the identity (`Reduction.ofRestrict`): wide instances are
yes-instances of neither problem but their formulas may be satisfiable, so
they go to a fixed no-instance — which is why the width condition has to be
decidable. -/
def sat3ToSat : SAT3 ⟶ᵣ SAT :=
  Reduction.ofRestrict _ { V := ℕ, φ := [[]] } not_satisfiable_emptyClause

end Hardness


