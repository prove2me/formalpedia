-- Prove2me | Definitions.Def_su_feasibleRegion
-- name    : su_feasibleRegion
-- status  : Definition
-- author  : @2017Advanced@
-- created : 2026-11-06T17:52:12.586201+00:00
-- url     : https://prove2.me/theorems/ffa6bdb1-055f-463a-a7db-844d05b4375f
-- title:
--   Definition 3 — the feasible region $\mathcal{R}$
-- statement:
--   Let $\mathcal{P}=\{p_\mu\}$ be a family of candidate distributions indexed by a parameter $\mu$, let $p_1,q_1$ be an unwanted and a retained member of the family, and let $f_d,f_c$ be baseline trade-off functions. The **feasible region** is the set of parameters whose distribution satisfies $(f_d,f_c)$-distributional unlearning with respect to $p_1$ and $q_1$:
--   $$\mathcal{R}=\{\,\mu : T(p_\mu,p_1)\le f_d \ \text{and}\ T(p_\mu,q_1)\ge f_c\,\}.$$
--   It is the set of edited distributions that simultaneously erase the unwanted domain to the prescribed level and preserve the retained one. In Lean this is `StatUnlearn.feasibleRegion fam p₁ q₁ f_d f_c`, a `Set` of parameters.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, p. 4, Definition 3

/-
Mission: Statistical Unlearning of Distributions
Source: A. Pandey, S. Kulkarni, arXiv:2605.16645 — Definition 3 (the feasible region).
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Real.Basic
import Definitions.Def_su_unlearning

open MeasureTheory

namespace StatUnlearn

/-- **Feasible region** (Definition 3 of the paper).

For a family of probability distributions `fam` indexed by `ι` (the paper's class
`𝒫`), unwanted/retained members `p₁, q₁ : ι`, and baseline trade-off functions
`f_d, f_c`, the feasible region is the set of indices `μ` whose distribution satisfies
`(f_d, f_c)`-unlearning with respect to `fam p₁` and `fam q₁`. -/
def feasibleRegion {W : Type*} [MeasurableSpace W] {ι : Type*} (fam : ι → Measure W)
    (p₁ q₁ : ι) (f_d f_c : ℝ → ℝ) : Set ι :=
  {μ | IsUnlearning (fam μ) (fam p₁) (fam q₁) f_d f_c}

end StatUnlearn


