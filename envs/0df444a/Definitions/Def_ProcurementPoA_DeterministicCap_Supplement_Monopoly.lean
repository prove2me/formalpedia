-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Monopoly
-- name    : ProcurementPoA_DeterministicCap_Supplement_Monopoly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:33:27.152772+00:00
-- url     : https://prove2.me/theorems/68654f22-e5b4-4fe2-9bb3-4bc992755e28
-- title:
--   Monopoly profit, largest monopoly bid, and regularity
-- statement:
--   For an acceptance function $S$ with upper phantom bound $R$ and a cost $c\ge1$, monopoly profit is the optimal profit of a supplier whose bid is always lowest:
--   $$\pi(c)=\sup_{b\in\mathbb R}(b-c)S(b).$$
--   When $\pi(c)>0$, $b^m(c)$ is the largest maximizing bid and $\sigma(c)=S(b^m(c))$. When $\pi(c)=0$, the conventions are exactly $b^m(c)=R+1$ and $\sigma(c)=0$. The monopoly price for cost $1$ is $T_1=b^m(1)$.
--
--   The acceptance function is regular when $S(b)>0$ for some $b>1$ and
--   $$b\longmapsto(b-1)S(b)\quad\text{is nondecreasing on }[1,T_1].$$
--   These quantities are used in the rejection bound, the integral bound and the regular-mechanism lower bound; regularity is separate from being an acceptance function.
--
--   **Formalization Note** The supremum defining profit is a real supremum of a nonempty set bounded above by $\max(0,R-c)$. At positive profit the maximizing set is nonempty, closed, and bounded, so its real supremum is its largest element. The zero-profit branch avoids the unbounded set of zero-profit bids above $R$. The functions are total on raw real functions, but theorem applications always require an actual acceptance function. The bodies also give harmless extensions to costs below $1$; no theorem uses that extension.
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Definitions 5.4 and 5.6, printed p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Acceptance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- Definition 5.4: the actual optimal one-supplier profit over all real bids.
For an acceptance function the range is nonempty and bounded above. -/
noncomputable def monopolyProfit (S : ℝ → ℝ) (c : ℝ) : ℝ :=
  sSup (Set.range fun b : ℝ => (b - c) * S b)

/-- Largest maximizing bid; the zero-profit branch follows the source exactly.
For valid acceptance functions, positive-profit maximizers form a nonempty compact set. -/
noncomputable def monopolyBid (R : ℝ) (S : ℝ → ℝ) (c : ℝ) : ℝ :=
  if monopolyProfit S c = 0 then R + 1
  else sSup {b : ℝ | (b - c) * S b = monopolyProfit S c}

noncomputable def sigma (R : ℝ) (S : ℝ → ℝ) (c : ℝ) : ℝ :=
  if monopolyProfit S c = 0 then 0 else S (monopolyBid R S c)

/-- Definition 5.6, without a density or strict monotonicity requirement. -/
def IsRegular (R : ℝ) (S : ℝ → ℝ) : Prop :=
  (∃ b : ℝ, 1 < b ∧ 0 < S b) ∧
  MonotoneOn (fun b => (b - 1) * S b) (Set.Icc 1 (monopolyBid R S 1))

end ProcurementPoA.DeterministicCap.Supplement


