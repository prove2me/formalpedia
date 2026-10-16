-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
-- name    : OAI_Combinatorics_GraphThreshold_EmbeddingExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:10:22.08142+00:00
-- url     : https://prove2.me/theorems/0ff89230-4bc9-412d-9738-f37463e969d8
-- title:
--   Two injections into a finite set differ by a permutation of the target
-- statement:
--   Let $\alpha$ and $\beta$ be sets with $\beta$ finite, and let $f,g:\alpha\to\beta$ be injective maps. Then there is a permutation $\sigma$ of $\beta$ such that
--
--   $$\sigma\bigl(f(a)\bigr)=g(a)\qquad\text{for every } a\in\alpha .$$
--
--   No finiteness of $\alpha$ is assumed; it follows from the injectivity of $f$.
--
--   Applied with $\beta=\{0,1,\dots,n-1\}$, the statement says that two placements of the same finite graph on $n$ labelled vertices differ by a relabelling of all $n$ vertices. Because it concerns arbitrary injections, it moves isolated vertices of the placed graph as well as vertices incident to edges. It is the tool that turns an isomorphism between two subgraphs of the complete graph $K_n$ into a permutation of $\{0,\dots,n-1\}$ carrying one onto the other.
--
--   **Formalization Note** The statement is `exists_perm_comp_embedding` for embeddings `f g : α ↪ β` with `[Finite β]`, where $\alpha$ and $\beta$ are arbitrary types and the permutation is an `Equiv.Perm β`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/EmbeddingExtension.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/EmbeddingExtension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability

namespace OAI

/-! Two placements of the same finite graph differ by an ambient permutation.
The statement is about arbitrary embeddings and therefore preserves isolated
vertices as well as vertices incident to edges. -/

namespace LeanBlast.SecondKahnKalai

theorem exists_perm_comp_embedding {α β : Type*} [Finite β]
    (f g : α ↪ β) : ∃ σ : Equiv.Perm β, ∀ a, σ (f a) = g a := by
  classical
  let : Finite α := Finite.of_injective f f.injective
  let : Fintype α := Fintype.ofFinite α
  let e : Set.range f ≃ Set.range g := f.toEquivRange.symm.trans g.toEquivRange
  refine ⟨e.extendSubtype, ?_⟩
  intro a
  rw [e.extendSubtype_apply_of_mem (f a) ⟨a, rfl⟩]
  change (e (f.toEquivRange a) : β) = g a
  simp [e]

end LeanBlast.SecondKahnKalai

end OAI


