-- Prove2me | Definitions.Def_StrategicNRM_Decoupled
-- name    : StrategicNRM_Decoupled
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:25.550453+00:00
-- url     : https://prove2.me/theorems/51bfce40-e6b2-4698-81e2-0f36781d4ed5
-- title:
--   The decoupled problem (7) and its value $\hat J$
-- statement:
--   With one payment per product, an outcome is $y=(\tau,a,p^1,\dots,p^n)$, and the utility attributed to product $j$ is
--
--   $$
--   U_j(\phi,y)=v^j_\phi e^{-d^j_\phi(\tau-t_\phi)}a^j-p^j .
--   $$
--
--   $\hat J$ is the optimal value of the problem of maximizing $E[\sum_{\phi\in\mathcal H_T}\sum_{j}p^j_\phi]$ subject to, for all $j$, $\phi$, $w\ge 0$,
--
--   $$
--   E_{-\phi}[U_j(\phi,y_\phi)]\ge E_{-\phi}[U_j(\phi,y_{\phi_{j,w}})],\qquad E_{-\phi}[U_j(\phi,y_\phi)]\ge 0,
--   $$
--
--   with $\mathbf 1^\top a_\phi\le 1$, $a_\phi\in\{0,1\}^n$ and $\sum_{\phi\in\mathcal H_T}\sum_j A_{ij}a^j_\phi\le x_0^i$ almost surely. The constraints are decoupled by product, and agents manipulate only their valuations, which is what opens the problem to a one-dimensional analysis.
--
--   **Formalization Note** $\tau\in[t_\phi,T]$ is not displayed in (7), but is part of what a variable $y_\phi$ is (p.11). The objective is an extended real, the expected total of the positive parts minus that of the negative parts, with the latter required finite. A Bochner integral would be wrong here: the solution of (7) built from a mechanism of (5) has non-negative payments whose expectation may be $+\infty$ under heavy tails, and this is a value of (7), not a $0$. For integrable payments it is the Bochner integral.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, pp.13–14, (6) and problem (7)

import Mathlib
import Definitions.Def_StrategicNRM_Instance

open MeasureTheory
open scoped ENNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- `Uⱼ(φ, y) = vʲ e^{−dʲ(τ−t)} aʲ − pʲ` (6), p.13, for `y = (τ, a, p¹, …, pⁿ)`. -/
noncomputable def utilityj (φ : CType n) (j : Fin n) (y : ℝ × Option (Fin n) × (Fin n → ℝ)) : ℝ :=
  φ.2.1 j * Real.exp (-φ.2.2 j * (y.1 - φ.1)) * alloc y.2.1 j - y.2.2 j

/-- The constraints of problem (7), pp.13–14, with variables `y φ c = (τ, a, p¹, …, pⁿ)`:

* (ICⱼ) `E₋φ[Uⱼ(φ, y_φ)] ≥ E₋φ[Uⱼ(φ, y_{φ_{j,w}})]` for every `j`, `φ` and `w ≥ 0`;
* (IRⱼ) `E₋φ[Uⱼ(φ, y_φ)] ≥ 0`;
* `1ᵀa ≤ 1` and `a ∈ {0,1}ⁿ`, built into `Option`;
* the inventory constraint, almost surely.

**Formalization Note.** `τ ∈ [t_φ, T]` is not displayed in (7), but it is part of what a variable
`y_φ` is (p.11), and `b ≤ 1` needs it. The fields `meas_*` and `int_pay` say that the expectations
are defined. The negative parts of the payments have finite total expectation, so that the
objective of (7) is defined in `(−∞, ∞]`; see `objHat`. -/
structure IsDecoupledFeasible (I : Instance n m)
    (y : CType n → Crowd (CType n) → ℝ × Option (Fin n) × (Fin n → ℝ)) : Prop where
  meas_time : Measurable fun x : CType n × Crowd (CType n) => (y x.1 x.2).1
  meas_alloc : ∀ j, MeasurableSet {x : CType n × Crowd (CType n) | (y x.1 x.2).2.1 = some j}
  meas_pay : ∀ j, Measurable fun x : CType n × Crowd (CType n) => (y x.1 x.2).2.2 j
  time_mem : ∀ φ, I.IsType φ → ∀ c, (y φ c).1 ∈ Set.Icc φ.1 I.T
  int_pay : ∀ φ j, I.IsType φ → Integrable (fun c => (y φ c).2.2 j) I.law
  ic : ∀ φ j w, I.IsType φ → 0 ≤ w →
    ∫ c, utilityj φ j (y (withVal φ j w) c) ∂I.law ≤ ∫ c, utilityj φ j (y φ c) ∂I.law
  ir : ∀ φ j, I.IsType φ → 0 ≤ ∫ c, utilityj φ j (y φ c) ∂I.law
  inventory : ∀ᵐ c ∂I.law, ∀ r, ∑ i, I.usage r (y (c.2 i) (c.others i)).2.1 ≤ I.x0 r
  neg_total : ∫⁻ c, ∑ i, ∑ j, ENNReal.ofReal (-(y (c.2 i) (c.others i)).2.2 j) ∂I.law ≠ ⊤

/-- The objective `E[Σ_{φ ∈ H_T} Σⱼ pʲ_φ]` of problem (7), p.13, as an extended real: the expected
total of the positive parts minus that of the negative parts.

**Formalization Note.** The expectation is not a Bochner integral. The solution that Lemma 3
builds from a mechanism of (5) has non-negative payments whose expectation may be `+∞` when the
valuations have heavy tails, and this `+∞` is a value of (7), which a Bochner integral would turn
into `0`. When the payments are integrable this is the Bochner integral. -/
noncomputable def objHat (I : Instance n m)
    (y : CType n → Crowd (CType n) → ℝ × Option (Fin n) × (Fin n → ℝ)) : EReal :=
  ((∫⁻ c, ∑ i, ∑ j, ENNReal.ofReal ((y (c.2 i) (c.others i)).2.2 j) ∂I.law : ℝ≥0∞) : EReal) -
    ((∫⁻ c, ∑ i, ∑ j, ENNReal.ofReal (-(y (c.2 i) (c.others i)).2.2 j) ∂I.law : ℝ≥0∞) : EReal)

/-- `Ĵ`, the optimal value of problem (7), pp.13–14. -/
noncomputable def Jhat (I : Instance n m) : EReal :=
  ⨆ y : {y // IsDecoupledFeasible I y}, objHat I y.1

end StrategicNRM


