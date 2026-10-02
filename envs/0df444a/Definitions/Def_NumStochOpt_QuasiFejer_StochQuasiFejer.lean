-- Prove2me | Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer
-- name    : NumStochOpt_QuasiFejer_StochQuasiFejer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T20:25:57.332129+00:00
-- url     : https://prove2.me/theorems/371c1891-c0ec-4b7c-9cae-9d2806b0c264
-- title:
--   Stochastic quasi-Féjer sequence for a set $Z$, Eq. (6.14)
-- statement:
--   Let $(\Theta,\mathcal R,\mu)$ be a probability space and $Z\subseteq\mathbb R^n$. A sequence of random vectors $z^0,z^1,\dots$ is a **stochastic quasi-Féjer sequence** for $Z$ if $E\|z^0\|^2<\infty$ and there are random variables $r_s\ge0$ with
--   $$
--   \sum_{s=0}^\infty E\,r_s<\infty
--   $$
--   such that for every $z\in Z$ and every $s=0,1,\dots$
--   $$
--   E\{\|z-z^{s+1}\|^2\mid z^0,\dots,z^s\}\le\|z-z^s\|^2+r_s\qquad\text{almost surely.}
--   $$
--
--   This is the stochastic analogue of a Féjer sequence ($\|z-z^{s+1}\|<\|z-z^s\|$ for all $z\in Z$): the distance to each point of $Z$ may increase, but only by a summable amount on average. It is the notion through which Theorem 6.1 yields convergence of the stochastic quasigradient projection method.
--
--   **Formalization Note** The random vectors are required to be measurable and square integrable at every step; the book states $E\|z^0\|^2<\infty$ only, and square integrability of the later $z^s$ follows from the defining inequality whenever $Z$ is nonempty. It is written out because a Lean conditional expectation of a non-integrable function is $0$, which would make the inequality empty. The $r_s$ do not depend on $z$, as on the page, and are measurable; $\sum_s E\,r_s$ is a sum of lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, p. 143, Eq. (6.14)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

open MeasureTheory

namespace NumStochOpt.QuasiFejer

/-- A **stochastic quasi-Féjer sequence** for a set `Z ⊆ ℝⁿ` (Ermoliev, Ch. 6 of Ermoliev & Wets
(1988), p. 143, Eq. (6.14)): a sequence of random vectors `z⁰, z¹, …` on `(Ω, μ)` with
`E‖z⁰‖² < ∞` for which there are random variables `r_s ≥ 0` with `∑_s E r_s < ∞` such that for
every `w ∈ Z` and every `s`,
`E{‖w - z^{s+1}‖² | z⁰, …, z^s} ≤ ‖w - z^s‖² + r_s` almost surely.
The random vectors are measurable and square integrable at every step (square integrability of
`z^s` for `s ≥ 1` is implied by the book's definition as soon as `Z` is nonempty; it is written
out so that the Lean conditional expectation is not the junk value of a non-integrable
function). -/
def IsStochQuasiFejer {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ s, Measurable (z s)) ∧ (∀ s, MemLp (z s) 2 μ) ∧
    ∃ r : ℕ → Ω → ℝ, (∀ s, Measurable (r s)) ∧ (∀ s, ∀ᵐ ω ∂μ, 0 ≤ r s ω) ∧
      (∑' s, ∫⁻ ω, ENNReal.ofReal (r s ω) ∂μ) < ⊤ ∧
      ∀ w ∈ Z, ∀ s,
        condExp (historySigma z s) μ (fun ω => ‖w - z (s + 1) ω‖ ^ 2)
          ≤ᵐ[μ] fun ω => ‖w - z s ω‖ ^ 2 + r s ω

end NumStochOpt.QuasiFejer


