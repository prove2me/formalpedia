-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ExchangeWalkReversal
-- name    : CountingMatroid_Analysis_ExchangeWalkReversal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:04:42.423258+00:00
-- url     : https://prove2.me/theorems/6ef74a64-feb8-4edb-afc3-aaf937f8c883
-- title:
--   Reversing an exchange graph
-- statement:
--   An exchange graph on $[n]$ consists of Boolean source and sink flags at each vertex and a Boolean directed-edge relation. Its reverse swaps the terminal roles and reverses every edge:
--   $$\operatorname{source}_{g^{\mathrm{rev}}}(v)=\operatorname{sink}_g(v),\qquad
--   \operatorname{sink}_{g^{\mathrm{rev}}}(v)=\operatorname{source}_g(v),\qquad
--   E_{g^{\mathrm{rev}}}(u,v)=E_g(v,u).$$
--   This construction is defined for every exchange graph, without assumptions about paths, reachability, or matroid realizability.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ExchangeWalkReversal.lean#L12-L14

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
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
import Mathlib.Data.List.Chain
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

/-! Reversing an exchange graph interchanges its sources and sinks. Reverse
list paths then satisfy the same augmentation and shortestness predicates. -/
namespace CountingMatroid.Analysis.ExchangeWalkReversal
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: Reverse every edge and interchange source and sink flags. -/
def reverse_exchange_graph {n : ℕ} (g : ExchangeGraph n) : ExchangeGraph n :=
  ⟨fun v => ((g.terminals v).2, (g.terminals v).1), fun u v => g.edges v u⟩









end CountingMatroid.Analysis.ExchangeWalkReversal

end


