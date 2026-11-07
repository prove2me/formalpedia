-- Prove2me | Definitions.Def_su_unlearning
-- name    : su_unlearning
-- status  : Definition
-- author  : @2017Advanced@
-- created : 2026-11-06T17:51:56.9951+00:00
-- url     : https://prove2.me/theorems/40baa833-d33b-40c3-b167-fea3b461c6ce
-- title:
--   Definition 2 — $(f_d,f_c)$ distributional unlearning
-- statement:
--   For baseline trade-off functions $f_d$ (removal) and $f_c$ (preservation), a distribution $p$ satisfies **$(f_d,f_c)$-distributional unlearning** with respect to an unwanted distribution $p_1$ and a retained distribution $q_1$ when
--   $$T(p,p_1)\le f_d \quad\text{(removal)},\qquad T(p,q_1)\ge f_c \quad\text{(preservation)},$$
--   both required to hold at every type-I level $t$. The removal condition says the edited data can be told apart from the unwanted domain at least as easily as the baseline pair defining $f_d$; the preservation condition says it cannot be told apart from the retained domain more easily than the baseline pair defining $f_c$. In Lean this is `StatUnlearn.IsUnlearning p p₁ q₁ f_d f_c`.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, p. 3, Definition 2, eq. (2.2)

/-
Mission: Statistical Unlearning of Distributions
Source: A. Pandey, S. Kulkarni, arXiv:2605.16645 — Definition 2 (eq. (2.2)).
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Real.Basic
import Definitions.Def_su_tof

open MeasureTheory

namespace StatUnlearn

/-- **`(f_d, f_c)` distributional unlearning** (Definition 2 of the paper, eq. (2.2)).

A distribution `p` satisfies `(f_d, f_c)`-unlearning with respect to the unwanted
distribution `p₁` and the retained distribution `q₁` when the removal condition
`T(p, p₁) ≤ f_d` and the preservation condition `T(p, q₁) ≥ f_c` hold for every
type-I error level `t`. -/
def IsUnlearning {W : Type*} [MeasurableSpace W] (p p₁ q₁ : Measure W)
    (f_d f_c : ℝ → ℝ) : Prop :=
  (∀ t, tof p p₁ t ≤ f_d t) ∧ ∀ t, f_c t ≤ tof p q₁ t

end StatUnlearn


