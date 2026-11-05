-- Prove2me | Definitions.Def_TenChallenges_UnfriendlyPartition
-- name    : TenChallenges_UnfriendlyPartition
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T20:19:03.970302+00:00
-- url     : https://prove2.me/theorems/d1be095f-fdda-41a2-bdb7-6f89990d599e
-- title:
--   Partial partitions, unfriendliness at a vertex, and the partitioning game with an ordinal clock
-- statement:
--   The definitions behind Challenge 10 of the Ten Challenges benchmark, for a simple graph $G$ on a vertex type $V$.
--
--   1. **Partial partitions.** A partial partition is a function $f$ from $V$ to $\{\text{undefined}, 0, 1\}$. The *empty partition* is undefined everywhere; $f$ has *finite domain* if only finitely many vertices are assigned a class; $g$ *extends* $f$ if every assignment made by $f$ is kept by $g$.
--   2. **Unfriendly at $v$.** $f$ is unfriendly at $v$ if $f(v)=b$ is defined and the cardinality of the set of neighbours of $v$ assigned $b$ is at most the cardinality of the set of neighbours assigned the opposite class $1-b$. Unassigned neighbours are not counted.
--   3. **Legal response.** Given $f$ and a challenged vertex $v$, a partial partition $g$ is a legal response if it extends $f$, has finite domain, and is unfriendly at $v$.
--   4. **Partitioner wins.** For an ordinal clock $\alpha$, $\mathrm{PartitionerWins}(G,f,\alpha)$ holds if for every vertex $v$ and every ordinal $\beta<\alpha$ there is a legal response $g$ to $(f,v)$ with $\mathrm{PartitionerWins}(G,g,\beta)$. For $\alpha=0$ this holds vacuously.
--
--   These definitions encode the $r$-partitioning game: Challenger names $v$ and $\beta<\alpha$, Partitioner answers with a legal response, and play continues with clock $\beta$.
--
--   **Formalization Note.** Classes are `Option Bool`; cardinalities are Mathlib's `Cardinal.mk` of subtypes of `V`; the recursion on the ordinal is well-founded recursion (`termination_by α`). The vertex type and the ordinal have independent universe parameters `u` and `v`.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/UnfriendlyPartition.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/UnfriendlyPartition.lean; the game is defined on the Ten Challenges website, challenge 10 (Definition "The r-partitioning game"); unfriendly partitions as in R. Aharoni, E. C. Milner, K. Prikry, Unfriendly partitions of a graph, JCTB 50 (1990).

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

universe u v

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- Neighbours of `v` mapped to value `b` by `f`. -/
def NeighColored {β : Type*} (f : V → β)
    (v : V) (b : β) : Type u := ↥(G.neighborSet v ∩ f ⁻¹' {b})

/-- `v` is coloured, with at least as many neighbours of the opposite colour as of its own. -/
def UnfriendlyAt (f : V → Option Bool)
    (v : V) : Prop :=
  ∃ b : Bool, f v = some b ∧
    #(NeighColored G f v (some b)) ≤ #(NeighColored G f v (some (!b)))

/-- The empty partial partition. -/
def emptyPartition (V : Type u) : V → Option Bool :=
  fun _ => none

/-- Only finitely many vertices are assigned a colour. -/
def HasFiniteDomain {V : Type u} (f : V → Option Bool) : Prop :=
  {v : V | f v ≠ none}.Finite

/-- `g` extends `f` when all assignments already made by `f` are preserved. -/
def Extends {V : Type u} (f g : V → Option Bool) : Prop :=
  ∀ v b, f v = some b → g v = some b

/-- A finite extension of `f` that is unfriendly at the challenged vertex `v`. -/
def IsLegalResponse {V : Type u} (G : SimpleGraph V)
    (f g : V → Option Bool) (v : V) : Prop :=
  Extends f g ∧ HasFiniteDomain g ∧ UnfriendlyAt G g v

/-- Partitioner wins from `(f, α)`, by recursion on the ordinal clock `α`. -/
def PartitionerWins {V : Type u} (G : SimpleGraph V)
    (f : V → Option Bool) (α : Ordinal.{v}) : Prop :=
  ∀ v : V, ∀ β : Ordinal.{v}, β < α →
    ∃ g : V → Option Bool,
      IsLegalResponse G f g v ∧ PartitionerWins G g β
termination_by α


