-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Supplement_Orthant
-- name    : IndependentInfoPricing_Main_Supplement_Orthant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:48:04.393899+00:00
-- url     : https://prove2.me/theorems/508f4ba6-e6a0-4ea1-a7a5-9793d025f26d
-- title:
--   Fixed orthant with regular magnitudes and budget-constrained separate selling
-- statement:
--   A **fixed orthant** (54) is given by independent probability marginals $F_1,\dots,F_Q$ and a set $S$ of coordinates, both $S$ and its complement nonempty ($m,n\ge1$), such that $v_i>0$ almost surely for $i\in S$ and $v_j<0$ almost surely for $j\notin S$. The magnitudes are $X_i=v_i$ ($i\in S$) and $Y_j=-v_j$ ($j\notin S$); the orthant is **regular** when every magnitude is a regular magnitude in the scope of §4.4 (positive $C^1$ density on an interval support, finite monopoly price).
--
--   For $t\ge0$ the **budget-constrained separate-selling revenues** (64) are
--   $$\operatorname{Sep}_+(t)=\sup_{\substack{p_i\ge0\\ \sum_{i\in S}p_i\le t}}\ \sum_{i\in S}p_i\Pr(X_i\ge p_i),\qquad \operatorname{Sep}_-(t)=\sup_{\substack{q_j\ge0\\ \sum_{j\notin S}q_j\le t}}\ \sum_{j\notin S}q_j\Pr(Y_j\ge q_j).$$
--
--   These are used by Lemmas 4.15 and 4.18 and Theorem 4.11, together with $\bar a=\sum_{i\in S}\operatorname{Rev}(X_i)$ and $\bar b=\sum_{j\notin S}\operatorname{Rev}(Y_j)$ of (56) (base `aBar`, `bBar`).
--
--   **Formalization Note** The source re-indexes so that the positive coordinates come first; here the positive block is the set $S$. Price vectors are indexed by all coordinates, and only the block's entries enter the sum and the budget.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §4.4 and (64), printed p.36–40 (PDF p.38–42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis
import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The fixed orthant (54): independent probability marginals; coordinates in `S` are positive
almost surely (`v_i = X_i`), coordinates outside `S` negative almost surely (`v_j = −Y_j`), with
both blocks nonempty (`m, n ≥ 1`). -/
def FixedOrthant (F : Marginals ι) (S : Finset ι) : Prop :=
  ProbabilityMarginals F ∧ S.Nonempty ∧ (Finset.univ \ S).Nonempty ∧
  (∀ i ∈ S, F i (Set.Ioi 0) = 1) ∧ ∀ i ∉ S, F i (Set.Iio 0) = 1

/-- Fixed orthant whose magnitude variables `X_i` (positive branches on `S`) and `Y_j` (negative
branches off `S`) are all regular, in the scope of §4.4. -/
def RegularOrthant (F : Marginals ι) (S : Finset ι) : Prop :=
  FixedOrthant F S ∧ (∀ i ∈ S, RegularMagnitude (positiveBranch (F i))) ∧
    ∀ i ∉ S, RegularMagnitude (negativeBranch (F i))

/-- `Sep₊(t)` of (64): best classical separate-selling revenue of the positive block with total
price at most `t`. -/
def sepPlus (F : Marginals ι) (S : Finset ι) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (p : ι → ℝ) (_ : ∀ i, 0 ≤ p i) (_ : ∑ i ∈ S, p i ≤ t),
    ∑ i ∈ S, ENNReal.ofReal (p i) * positiveBranch (F i) (Set.Ici (p i))

/-- `Sep₋(t)` of (64): the same for the negative block of magnitudes `Y_j`. -/
def sepMinus (F : Marginals ι) (S : Finset ι) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (q : ι → ℝ) (_ : ∀ j, 0 ≤ q j) (_ : ∑ j ∈ Finset.univ \ S, q j ≤ t),
    ∑ j ∈ Finset.univ \ S, ENNReal.ofReal (q j) * negativeBranch (F j) (Set.Ici (q j))

end IndependentInfoPricing.Main.Supplement


