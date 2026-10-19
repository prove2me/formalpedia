-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:37:21.055868+00:00
-- url     : https://prove2.me/theorems/7fc55cc2-f14c-4ada-8f75-abba26b7fb73
-- title:
--   Index pairs $(n,E)$, step sizes $1/(n+1)$ and an ultrafilter refining the tails
-- statement:
--   Let $A$ be a set (in applications, a unital $C^*$-algebra).
--
--   1. **Index set.** $\mathcal{I}_A=\mathbb{N}\times\mathcal{F}(A)$, where $\mathcal{F}(A)$ is the set of finite subsets of $A$, ordered componentwise: $(n,E)\le(n',E')$ if and only if $n\le n'$ and $E\subseteq E'$. This is a directed set.
--
--   2. **Step size.** For $i=(n,E)\in\mathcal{I}_A$,
--
--      $$
--      \eta(i)=\frac{1}{n+1}.
--      $$
--
--   3. **Ultrafilter.** $\mathcal{U}_A$ is a fixed ultrafilter on $\mathcal{I}_A$ that refines the filter of tails, i.e. contains every set $\{\,i\in\mathcal{I}_A : i\ge i_0\,\}$; it is chosen using the axiom of choice.
--
--   Since $\mathcal{U}_A$ contains all tails, $\eta(i)\to0$ along $\mathcal{U}_A$, and for each $w\in A$ the set of indices $(n,E)$ with $w\in E$ belongs to $\mathcal{U}_A$. In the avoidance argument one makes, for each index $(n,E)$, a choice adapted to the tolerance $\eta(n,E)$ and to the finite set $E$, and then passes to the limit along $\mathcal{U}_A$, so that tolerances tend to $0$ while every element of $A$ is eventually taken into account. The file also fixes, for the lemmas of its module, the usual order on unital $C^*$-algebras: $a\le b$ if and only if $b-a$ is positive.
--
--   **Formalization Note** Lean names: `FourIndex A`, an abbreviation for the product of the natural numbers with `Finset A` (with the product order), `fourEta A i`, and `fourUltra A := Ultrafilter.of atTop`, defined with classical decidable equality on `A` so that finite subsets form a lattice. The local instances `ultrafilterPartialOrder` and `ultrafilterStarOrderedRing` select Mathlib's spectral order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Ultrafilter.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Ultrafilter.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndividualStrongInfiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable (A : Type*)
abbrev FourIndex := ℕ × Finset A

def fourEta (i : FourIndex A) : ℝ := 1 / ((i.1 : ℝ)+1)

noncomputable def fourUltra : Ultrafilter (FourIndex A) := by
  classical
  exact Ultrafilter.of atTop

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
local instance ultrafilterPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance ultrafilterStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

end MainGap

end

end OAI


