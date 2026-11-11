-- Prove2me | Definitions.Def_ReconfRes_Frozen_PrivateTags
-- name    : ReconfRes_Frozen_PrivateTags
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:23:13.710002+00:00
-- url     : https://prove2.me/theorems/53523b77-3fef-46e0-87a3-d34c4571016a
-- title:
--   Private tags: the tagged formula {C_i ∪ {¬t_i}, {t_i}} and the lift of an indexed tight refutation (Lemma 3.60)
-- statement:
--   Let $C_1,\dots,C_\alpha$ be an inventory of axiom occurrences (repetitions allowed) and $t_1,\dots,t_\alpha$ distinct fresh variables. Put
--   $$D_i=C_i\cup\{\neg t_i\},\qquad U_i=\{t_i\},\qquad H=\{D_i,U_i:1\le i\le\alpha\}.$$
--   A **tight** indexed refutation with this inventory is a lean refutation of the formula $\{C_1,\dots,C_\alpha\}$ of size at most $2\alpha-1$ whose axiom nodes are indexed by $i\mapsto$ `pos i`, the node `pos i` carrying $C_i$. Its **lift** replaces its $i$-th source by the resolution of $D_i$ and $U_i$ on $t_i$: the node `pos i` keeps the clause $C_i$ and receives a new $D_i$ parent and a new $U_i$ parent.
--
--   **Formalization Note.** The lift has the nodes `Fin (n + (α + α))`: the old nodes, then the $D_i$, then the $U_i$.
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 78, Lemma 3.60

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-!
# Private tags (Lemma 3.60)

Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, §3.13, p. 78.

For an inventory `C₁, …, C_α` (indexed by `Fin α`, repetitions allowed) and tag variables
`t₁, …, t_α`, put `Dᵢ = Cᵢ ∪ {¬tᵢ}`, `Uᵢ = {tᵢ}` and `H = {Dᵢ, Uᵢ}`. The lift of an indexed
refutation `(R, pos)` (the `i`-th source is the axiom node `pos i`) replaces the `i`-th source by
the resolution of `Dᵢ` and `Uᵢ` on `tᵢ`: the node `pos i` keeps its label `Cᵢ` and receives two
new parents, a `Dᵢ` axiom node and a `Uᵢ` axiom node. The lift has the nodes `Fin (n + (α + α))`:
first the old nodes, then the `α` nodes `Dᵢ`, then the `α` nodes `Uᵢ`.
-/

variable {V : Type} [DecidableEq V] {α : ℕ}

/-- The tagged clause `Dᵢ = Cᵢ ∪ {¬tᵢ}`. -/
def tagD (C : Fin α → Clause V) (t : Fin α → V) (i : Fin α) : Clause V := insert (t i, false) (C i)

/-- The tag unit `Uᵢ = {tᵢ}`. -/
def tagU (t : Fin α → V) (i : Fin α) : Clause V := {(t i, true)}

/-- The tagged formula `H = {Dᵢ, Uᵢ : 1 ≤ i ≤ α}`. -/
def tagFormula (C : Fin α → Clause V) (t : Fin α → V) : CNF V :=
  Finset.univ.image (tagD C t) ∪ Finset.univ.image (tagU t)

/-- The formula of an inventory: the set of its clauses. -/
def inventoryFormula (C : Fin α → Clause V) : CNF V := Finset.univ.image C

/-- A tight refutation with the indexed inventory `C`: a lean refutation of the inventory's
formula, of size at most `2α − 1`, whose axiom nodes are indexed by `pos` with `pos i` labelled
`Cᵢ`. -/
def IsTightIndexed (C : Fin α → Clause V) (R : ProofDag V) (pos : Fin α → Fin R.n) : Prop :=
  R.IsRefutationOf (inventoryFormula C) ∧ R.IsLean ∧ R.size + 1 ≤ 2 * α ∧
    IsIndexedBy C Finset.univ R pos

/-- The lift of an indexed refutation: its `i`-th source `pos i` becomes the resolution of a new
`Dᵢ` axiom node and a new `Uᵢ` axiom node on `tᵢ`. -/
def lift (C : Fin α → Clause V) (t : Fin α → V) (R : ProofDag V) (pos : Fin α → Fin R.n) :
    ProofDag V where
  n := R.n + (α + α)
  label := Fin.addCases R.label (Fin.addCases (tagD C t) (tagU t))
  edges :=
    R.edges.image (fun e => (Fin.castAdd (α + α) e.1, Fin.castAdd (α + α) e.2)) ∪
    Finset.univ.image (fun i => (Fin.natAdd R.n (Fin.castAdd α i), Fin.castAdd (α + α) (pos i))) ∪
    Finset.univ.image (fun i => (Fin.natAdd R.n (Fin.natAdd α i), Fin.castAdd (α + α) (pos i)))
  sink := Fin.castAdd (α + α) R.sink

end ReconfRes.Frozen


