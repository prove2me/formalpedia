-- Prove2me | Definitions.Def_su_tof
-- name    : su_tof
-- status  : Definition
-- author  : @2017Advanced@
-- created : 2026-11-06T17:51:41.66118+00:00
-- url     : https://prove2.me/theorems/d047e6c1-c047-4079-a42a-98b854b9a0ce
-- title:
--   Definition 1 — the trade-off function $T(P,Q)$
-- statement:
--   Given two probability distributions $P$ and $Q$ on a measurable space $W$, the trade-off function is the map
--   $$T(P,Q)(t)=\inf\{\,\beta_\varphi : \alpha_\varphi \le t\,\},$$
--   where the infimum runs over all measurable functions $\varphi : W \to [0,1]$, with $\alpha_\varphi=\int\varphi\,dP$ the type-I error and $\beta_\varphi=\int(1-\varphi)\,dQ$ the type-II error. Intuitively, $T(P,Q)(t)$ is the smallest type-II error an adversary can achieve at type-I level $t$, so a *larger* trade-off function means the two distributions are harder to distinguish; $T(P,P)(t)=1-t$ is the largest possible value. In Lean this is `StatUnlearn.tof P Q t`, an `sInf` over measurable `[0,1]`-valued tests against `P` and `Q`.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, p. 3, Definition 1, eq. (2.1)

/-
Mission: Statistical Unlearning of Distributions
Source: A. Pandey, S. Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis
Testing Approach", arXiv:2605.16645 — Definition 1 (eq. (2.1)).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory

namespace StatUnlearn

/-- **Trade-off function** (Definition 1 of the paper).

Given two probability distributions `P`, `Q` on a measurable space `W`, and a level
`t` of type-I error, `tof P Q t` is the infimum of the achievable type-II errors
`β_φ = ∫ (1 - φ) dQ` over all randomized tests `φ : W → [0,1]` that are measurable and
satisfy `α_φ = ∫ φ dP ≤ t`.

This is the paper's
`T(P,Q)(α) := inf { β_φ : α_φ ≤ α }` of equation (2.1). -/
noncomputable def tof {W : Type*} [MeasurableSpace W] (P Q : Measure W) (t : ℝ) : ℝ :=
  sInf {β : ℝ | ∃ φ : W → ℝ, Measurable φ ∧ (∀ w, φ w ∈ Set.Icc (0 : ℝ) 1) ∧
    (∫ w, φ w ∂P) ≤ t ∧ β = ∫ w, (1 - φ w) ∂Q}

end StatUnlearn


