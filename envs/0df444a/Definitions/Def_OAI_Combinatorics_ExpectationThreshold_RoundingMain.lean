-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMain
-- name    : OAI_Combinatorics_ExpectationThreshold_RoundingMain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:45:59.321103+00:00
-- url     : https://prove2.me/theorems/b51d0915-52ff-40cc-80de-ad1affb09b84
-- title:
--   The member masses induced by a fractional cover
-- statement:
--   Let $X$ be a finite set and $\mathcal{F}$ a family of subsets of $X$. A fractional cover is a function $g$ on subsets of $X$ with values in $[0,1]$ and $\sum_{S\subseteq H}g(S)\ge1$ for every $H\in\mathcal{F}$; its cost at density $r$ is $\sum_Sg(S)r^{|S|}$. Let $r\ge0$ and let $g$ be a fractional cover of cost at most $\frac12$ at density $r$.
--
--   The mass family attaches to each member $H\in\mathcal{F}$ the rounding mass
--   $$
--   \pi_H(x)=\frac{1}{M_g(H)}\sum_{\substack{\emptyset\ne S\subseteq H\\ x\in S}}\frac{g(S)}{|S|},\qquad M_g(H)=\sum_{\emptyset\ne S\subseteq H}g(S).
--   $$
--   Each $\pi_H$ is a probability vector supported in $H$, because $M_g(H)\ge\frac12>0$.
--
--   These are the concrete inputs of the multiscale selector in the rounding argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/RoundingMain.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingMain.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandExpectationThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorGlobalCost

namespace OAI

/-!
# Actual rounding of an unrestricted fractional cover

The concrete member masses feed the proved multiscale selector. The same
independent color law supplies the lower and upper bounds on the subset-product
score. No selector hypothesis or bound on support sizes appears in the result.
-/

open scoped BigOperators

noncomputable section

namespace TalagrandThreshold

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual normalized probability masses attached to family members. -/
def fractionalMassFamily (F : Family α) (g : Finset α → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hcover : FractionalCover F g) (hcost : fracCost r g ≤ 1 / 2) :
    Selector.MassFamily F where
  weight H := roundingMass g H.val
  nonneg H x := roundingMass_nonneg g H.val hcover.nonneg
    (memberMass_pos_of_fractionalCover hcover H.property hr hcost) x
  total H := roundingMass_sum g H.val
    (memberMass_pos_of_fractionalCover hcover H.property hr hcost)
  supported H _ hx := roundingMass_eq_zero_of_not_mem g H.val hx

end TalagrandThreshold

end

end OAI


