-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
-- name    : CountingMatroid_Analysis_ExchangePathCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:04:01.82264+00:00
-- url     : https://prove2.me/theorems/d09a0327-3a66-4033-8119-e40ae80202f7
-- title:
--   Reverse-listed augmenting walks and shortest-path certificates
-- statement:
--   Let $g$ be an exchange graph with vertex set $[n]$, source and sink flags, and directed edge relation $E_g$. A source walk is a nonempty list stored in reverse traversal order: $[v]$ is allowed when $v$ is a source, and
--   $$\operatorname{SourceWalk}(u::p)\ \land\ E_g(u,v)
--   \quad\Longrightarrow\quad
--   \operatorname{SourceWalk}(v::u::p).$$
--   An augmenting walk is a source walk whose first listed vertex is a sink; its last listed vertex is therefore a source. A shortest certificate for a list $p$ requires that it is augmenting, has no repeated vertices, and satisfies
--   $$|p|\leq n,\qquad
--   |p|\leq |q|\quad\text{for every augmenting walk }q.$$
--   Lengths count listed vertices. The certificate is a proposition packaging these obligations, not a claim that such a walk always exists.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangePathCertificate.lean#L10-L14

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
section


set_option autoImplicit false

/-! Proof-side certificates use the search's reverse list orientation. Minimality
is over all source-to-sink walks, not just paths discovered by the implementation. -/
namespace CountingMatroid.Analysis.ExchangePathCertificate
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: A nonempty reverse walk whose last vertex is a source. -/
inductive SourceWalk {n : ℕ} (g : ExchangeGraph n) : List (Fin n) → Prop
  | source (v : Fin n) : (g.terminals v).1 = true → SourceWalk g [v]
  | step (u v : Fin n) (tail : List (Fin n)) : SourceWalk g (u :: tail) →
      g.edges u v = true → SourceWalk g (v :: u :: tail)

/-- INTERNAL: A reverse source walk ending at a sink. -/
def AugmentingWalk {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) : Prop :=
  SourceWalk g p ∧ ∃ v tail, p = v :: tail ∧ (g.terminals v).2 = true

/-- INTERNAL: Mathematical interface between the capped BFS and matroid exchange.
The length bound makes the program's final take harmless. -/
structure ShortestCertificate {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) : Prop where
  augmenting : AugmentingWalk g p
  simple : p.Nodup
  length_le : p.length ≤ n
  minimal : ∀ q, AugmentingWalk g q → p.length ≤ q.length


end CountingMatroid.Analysis.ExchangePathCertificate

end


