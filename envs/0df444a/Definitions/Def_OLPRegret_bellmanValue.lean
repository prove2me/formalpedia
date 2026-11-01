-- Prove2me | Definitions.Def_OLPRegret_bellmanValue
-- name    : OLPRegret_bellmanValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:39.154246+00:00
-- url     : https://prove2.me/theorems/caa5022d-8a34-4700-b6be-c5299d067fce
-- title:
--   The Bellman value and the optimal action
-- statement:
--   The Bellman value $W_t(b)=\mathrm E(v_t^b)$ solves
--   $$
--   W_0(b)=0,\qquad W_t(b)=\mathrm E\Big[\max_{x_t\in\{0,1\}}x_tu_t+W_{t-1}\big(\psi_t^b(x_ta_t)\big)\ \text{ s.t. }\ x_ta_t\le tb\Big].
--   $$
--   The **optimal action** $\pi_t^b$ accepts the period-$t$ customer when $a_t\le tb$ and $u_t+W_{t-1}(\psi_t^b(a_t))$ exceeds $W_{t-1}(\psi_t^b(0))$. Following it from $b_n=\beta$ yields the **Bellman policy**, whose online value is $v_n^\beta$.
--
--   This is the optimal online policy that Theorems 1 and 3 and Lemmas 7 and 8 concern.
--
--   **Formalization Note** Acceptance is excluded when $a\not\le tb$; ties are rejected ("exceeds", p.18). Under Assumptions 2–3, $W_t$ is bounded and upper semicontinuous in $b$, so it is Borel and the integrand is integrable.
-- source:
--   Bray, arXiv:1912.08917v6, (12)–(15), p.18

import Mathlib
import Definitions.Def_OLPRegret_Policy

set_option autoImplicit false

open MeasureTheory

namespace OLPRegret

open scoped Classical in
/-- The Bellman value `E(vₜᵇ)` (Bray, arXiv:1912.08917v6, (12)–(13), p.18):
`E(v₀ᵇ) = 0` and
`E(vₜᵇ) = E[max_{xₜ ∈ {0,1}} xₜuₜ + E(v_{t−1}^{ψₜᵇ(xₜaₜ)}) s.t. xₜaₜ ≤ tb]`.

**Formalization Note** Acceptance is excluded when `a ≰ tb` rather than given value `−∞`. Under
Assumptions 2–3 each `W t` lies in `[0, t E(u₁)]` and is upper semicontinuous in `b` (by induction:
`{a ≤ tb}` is closed, and reverse Fatou applies with the integrable bound), so it is Borel and the
integrand below is integrable; the Bochner integral is not a junk value. -/
noncomputable def W {m : ℕ} (μ : Measure (Customer m)) : ℕ → E m → ℝ
  | 0, _ => 0
  | t + 1, b =>
    ∫ z, (if VLe z.2 (((t + 1 : ℕ) : ℝ) • b)
      then max (z.1 + W μ t (psi (t + 1) b z.2)) (W μ t (psi (t + 1) b 0))
      else W μ t (psi (t + 1) b 0)) ∂μ

open scoped Classical in
/-- The optimal action `πₜᵇ` (Bray, arXiv:1912.08917v6, (14), p.18): accept iff there is inventory
enough, `aₜ ≤ tb`, and `uₜ + E(v_{t−1}^{ψₜᵇ(aₜ)})` exceeds `E(v_{t−1}^{ψₜᵇ(0)})`.

**Formalization Note** Ties are rejected ("exceeds", p.18). The natural-number subtraction `t - 1`
is used at `t ≥ 1` only. -/
noncomputable def bellmanRule {m : ℕ} (μ : Measure (Customer m)) (t : ℕ) (b : E m)
    (z : Customer m) : Bool :=
  decide (VLe z.2 ((t : ℝ) • b) ∧
    W μ (t - 1) (psi t b 0) < z.1 + W μ (t - 1) (psi t b z.2))

/-- The Bellman policy (14) as a scheme of horizon `n`. Its online value is `vₙᵝ` of (15). -/
noncomputable def bellmanScheme {m n : ℕ} (μ : Measure (Customer m)) : Scheme m n :=
  ruleScheme (bellmanRule μ)

end OLPRegret


