-- Prove2me | Definitions.Def_CountingMatroid_Analysis_FeasibilitySolver
-- name    : CountingMatroid_Analysis_FeasibilitySolver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:31.916992+00:00
-- url     : https://prove2.me/theorems/c8a1b352-8cb9-43e2-9d6b-84d502abd6f6
-- title:
--   Rank-zero and rank-one feasibility wrappers
-- statement:
--   Let $F$ be a feasibility implementation taking ground size $n$, natural target rank $r$, and Boolean subset oracles $o_1,o_2$. The wrappers perform charged rank comparisons and define
--   $$
--   F_0(n,r,o_1,o_2)=
--   \begin{cases}\mathrm{true},&r=0,\\F(n,r,o_1,o_2),&r\ne0,\end{cases}
--   $$
--   and
--   $$
--   F_1(n,r,o_1,o_2)=
--   \begin{cases}
--   \operatorname{singletonScan}(o_1,o_2),&r=1,\\
--   F(n,r,o_1,o_2),&r\ne1.
--   \end{cases}
--   $$
--   The singleton scan tests acceptance of each singleton by both oracles. These definitions add special-case branches to an arbitrary implementation; they do not themselves impose correctness assumptions on the implementation or the oracles. Charges refer to abstract model operations.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FeasibilitySolver.lean#L60-L66

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_ExchangePathCertificate
import Definitions.Def_CountingMatroid_Analysis_ExchangeWalkReversal
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
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
import Mathlib.Data.Finset.SymmDiff
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

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.IntersectionAugmentation
end CountingMatroid.Analysis.IntersectionAugmentation
namespace CountingMatroid.Analysis.FoundPathAugmentation
end CountingMatroid.Analysis.FoundPathAugmentation
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
end CountingMatroid.Analysis.ShortestExchangeAugmentation
namespace CountingMatroid.Analysis.ShortestSourceWalkIndependence
end CountingMatroid.Analysis.ShortestSourceWalkIndependence
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
end CountingMatroid.Analysis.ExchangeWalkCardinality
namespace CountingMatroid.Analysis.FindPathCertificate
end CountingMatroid.Analysis.FindPathCertificate
namespace CountingMatroid.Analysis.FrozenPathTable
end CountingMatroid.Analysis.FrozenPathTable
namespace CountingMatroid.Analysis.NoPathSeparator
end CountingMatroid.Analysis.NoPathSeparator
namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
section


set_option autoImplicit false

/-!
The common-base predicate is connected to the paper's feasibility pretest.
Ranks zero and one are implemented and verified using the charged interface;
the rank-one implementation is the first augmentation from the empty set.
An explicit capped exchange-graph implementation handles arbitrary rank.
Its uniform cost certificate is proved. The parent now reduces correctness to
the augmentation-progress obligation in a separate child file, which remains
open. The parent proof has no open tactic goals but depends on that obligation.
-/

namespace CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model
open scoped Classical





/-- INTERNAL: A charged rank test handles the empty common independent set
before invoking a solver for positive rank.
TEXLINE: main.tex:283-289 -/
def rankZeroGuard (solver : FeasibilityImplementation) : FeasibilityImplementation where
  run n r o₁ o₂ := do
    let zero ← Operations.natEqual r 0
    if zero then pure true else solver.run n r o₁ o₂







/-- INTERNAL: Use the verified first augmentation when the requested rank is
one; leave larger ranks to the intersection solver.
TEXLINE: main.tex:283-289 -/
def rankOneGuard (solver : FeasibilityImplementation) : FeasibilityImplementation where
  run n r o₁ o₂ := do
    let one ← Operations.natEqual r 1
    if one then RankOneFeasibility.singletonScan o₁ o₂ else solver.run n r o₁ o₂













end CountingMatroid.Analysis.FeasibilitySolver

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r17 · partial · proved the complementary-basis cardinality separator used by augmentation_progress; isolated the remaining no-path obligations as basis certificates for the computed reachable set. The single-child handoff was also mechanically rejected; all new files remain owned locally.

* r16 · partial · proved the explicit solver's unconditional polynomial resource certificate after the two-child handoff was mechanically rejected. Only augmentation_progress remains open; parent cardinality induction and contract assembly elaborate against that obligation.

* r15 · decomposed · constructed a charged capped exchange-graph/BFS implementation and reduced the parent to its independent augmentation-progress and uniform-cost certificates. Proved exact query/table specifications and the parent cardinality induction; the two child certificates remain open pending live handoff.

* r14 · partial · implemented and verified the first augmentation from the empty set as a charged singleton scan; proved exact correctness and unconditional costs, and wired its rank-one guard and polynomial bounds into the parent. The remaining witness requires correctness only for 1 < r; no new open helper or transferred proof debt.
* r13 · partial · implemented the charged rank-zero guard; proved its value, zero additional oracle cost, and one-comparison overhead. The parent now handles rank zero and absorbs the guard cost into its polynomial coefficient. The positive-rank intersection implementation and its uniform bounds remain open; no new unproved declarations.
* r12 · open · library-first search again found no deterministic two-oracle intersection solver with polynomial charged bounds; checked augmentation and direct-sum independence statements. Preserved the existing bridge and target, and proposed the explicitly cited Schrijver dependency for Prior review; no new proof debt introduced.
* r11 · open · searched pinned Mathlib and Arlib for common independent sets, intersection algorithms, augmenting paths, and submodular minimization; no matching solver was found. Checked the single-matroid augmentation signatures and the unconditional cost quantifiers; the existing charged implementation dependency remains unresolved.
* r10 · recovery · isolated the missing charged augmenting-path implementation and its two cost proofs; a mathematical decider or a prior theorem alone cannot instantiate this contract without charged code.
* r9 · open · searched pinned Mathlib and Arlib for a two-oracle intersection algorithm or submodular minimization route; only single-matroid augmentation is present. The remaining goal is the cited solver's charged implementation and both uniform polynomial bounds.
* r8 · open · rechecked the entire pinned Mathlib and Arlib sources by matroid-intersection, common-independent-set, and augmenting-path statements; no executable two-oracle solver or cost certificate matches `FeasibilityContract`. The Schrijver citation remains the missing borrowed dependency.
* r7 · open · searched the pinned Mathlib matroid sources and all Arlib Lean sources by matroid-intersection and augmentation statement shape; no two-oracle implementation or polynomial charged certificate exists. The cited Schrijver theorem supplies an external algorithmic result, but the custom charged realization remains a local obligation.
* r6 · open · rechecked the contract shape and pinned Matroid/Computation sources; Mathlib has single-matroid augmentation but no executable matroid-intersection pretest or polynomial charged cost certificate. The Schrijver result remains a Prior proposal.
* r5 · open · searched pinned Mathlib and Arlib for matroid-intersection code; none supplies a charged polynomial pretest, while exhaustive candidate enumeration has exponential oracle cost.
* r4 · decomposed · proved the common-base/size-r-independent bridge and narrowed the remaining executable solver obligation to the predicate in Schrijver's cited pretest.
* r3 · open · recovery identified the irreducible boundary as executable charged code plus correctness and two uniform cost bounds; no smaller cited library theorem supplies it.
* r2 · open · checked the contract, its project uses, and pinned Matroid/Computation sources; no executable polynomial matroid-intersection result supplies this contract.
* r1 · open · library search found no charged matroid-intersection implementation; the cited polynomial pretest still needs code and a cost proof.
-/

end


