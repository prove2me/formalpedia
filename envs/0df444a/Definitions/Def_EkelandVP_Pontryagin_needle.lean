-- Prove2me | Definitions.Def_EkelandVP_Pontryagin_needle
-- name    : EkelandVP_Pontryagin_needle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:09:03.046994+00:00
-- url     : https://prove2.me/theorems/a6a06d37-5231-4922-8378-ebea90f80d90
-- title:
--   (7.18) — the needle variation v_τ of a control u_ε at time t₀ with value u₀ and width τ
-- statement:
--   Let $T$ be a real number, $u_\varepsilon : \mathbb R \to K$ a control, $u_0 \in K$ a control value, $t_0$ a time and $\tau$ a width. The **needle variation** $v_\tau : \mathbb R \to K$ of $u_\varepsilon$ is
--
--   $$
--   v_\tau(t) = \begin{cases} u_0 & \text{if } t \in [0, T] \cap\, ]t_0 - \tau, t_0[, \\ u_\varepsilon(t) & \text{if } t \notin [0, T] \cap\, ]t_0 - \tau, t_0[. \end{cases} \qquad (7.18)
--   $$
--
--   It replaces the control by the constant value $u_0$ on an open interval of length $\tau$ ending at $t_0$. Needle variations are the perturbations used in the proof of the maximum principle (Lemma 7.4 computes the derivative of the terminal cost in $\tau$ at $\tau = 0$).
--
--   **Formalization Note** The interval is open, as printed in (7.18). The case distinction uses classical decidability.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 350, §7, (7.18)

import Mathlib

namespace EkelandVP.Pontryagin

open Classical in
/-- Ekeland (1974), §7, p. 350, (7.18): the needle variation `v_τ` of the control `uε` at time `t₀`
with value `u₀` and width `τ`: `v_τ(t) = u₀` if `t ∈ [0, T] ∩ ]t₀ − τ, t₀[`, and `v_τ(t) = uε(t)`
otherwise. -/
noncomputable def needle {K : Type*} (T : ℝ) (uε : ℝ → K) (u₀ : K) (t₀ τ : ℝ) : ℝ → K :=
  fun t => if t ∈ Set.Icc 0 T ∩ Set.Ioo (t₀ - τ) t₀ then u₀ else uε t

end EkelandVP.Pontryagin


