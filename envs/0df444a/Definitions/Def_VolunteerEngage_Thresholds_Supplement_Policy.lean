-- Prove2me | Definitions.Def_VolunteerEngage_Thresholds_Supplement_Policy
-- name    : VolunteerEngage_Thresholds_Supplement_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:08:43.113516+00:00
-- url     : https://prove2.me/theorems/f753a697-0c52-40d7-b795-f6600c9c5b79
-- title:
--   The nested threshold policy (72), corrected at τ₁
-- statement:
--   Let $\tau_l=v^{-1}(p-\hat c_l)$, $1\le l\le L$, with $\tau_{L+1}=0$, be the strictly decreasing engagement thresholds of a Bellman solution. Using the drift increments $\eta_l$ of (51), define
--
--   $$\theta^*_{\tau}(z)=\theta_0+\sum_{l=1}^L\eta_l\,\mathbf1_{\{z<\tau_l\}}.$$
--
--   For $z\ge0$ this is (72): $\theta_L$ below $\tau_L$, $\theta_l$ on $[\tau_{l+1},\tau_l)$, and $\theta_0$ on $[\tau_1,\infty)$. It remains valid for $L=1$, when the middle range is empty. This is a function of the thresholds, independently of $\psi$.
--
--   **Formalization Note** The last branch of (72) prints $\tau_1<z$, omitting equality. The definition uses $\tau_1\le z$, as (70), (E8) and the explicit instruction after (75) require. The original counterexample to branch coverage is $z=\tau_1$. No cases are excluded. Values at negative workloads are unused.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, pp. 22–23, (71)–(72), (75)–(76)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

namespace VolunteerEngage.Thresholds.Supplement

/-- The nested policy (72), equivalently the activity switches (75)–(76).
At equality z = τ₁ the drift is θ₀, repairing the strict inequality in (72). -/
noncomputable def candidate (M : Model) (τ : ℕ → ℝ) (z : ℝ) : ℝ :=
  M.θ0 + ∑ l ∈ Finset.Icc 1 M.L, if z < τ l then M.η l else 0

end VolunteerEngage.Thresholds.Supplement


