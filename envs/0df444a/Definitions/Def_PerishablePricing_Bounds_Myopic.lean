-- Prove2me | Definitions.Def_PerishablePricing_Bounds_Myopic
-- name    : PerishablePricing_Bounds_Myopic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:07.328663+00:00
-- url     : https://prove2.me/theorems/6cc7c2be-14b4-4ff3-8bf4-7deb11157e61
-- title:
--   §6.1, p. 294 — v_t, θ̃, the myopic objectives Π_t and Π̃_t, and largest maximizers
-- statement:
--   In the model of `PerishablePricing.Bounds.Model` (lifetime $l=L+1$, zero lead time, backlogging), §6.1 introduces the following objects. Let
--
--   $$\tilde\theta=\theta+\gamma c-h^+,\qquad v_t(s_l,d_t)=-(1-\gamma)cs_l-\gamma c d_t-h^+(s_l-d_t)^+-h^-(d_t-s_l)^+ .$$
--
--   The myopic objectives are
--
--   $$\Pi_t(s_l,d)=P(d)d+\mathbb E\big[v_t(s_l,d+\varepsilon_t)\big],$$
--
--   $$\tilde\Pi_t(s_l,d)=\Pi_t(s_l,d)-\gamma c\,s_l-\big(\gamma h^++\gamma^2h^++\dots+\gamma^{l-2}h^++\gamma^{l-1}\tilde\theta\big)\,\mathbb E\big[(s_l-d_t)^+\big].$$
--
--   $\bar S_t(d)$ and $\underline S_t(d)$ are maximizers of $\Pi_t(\cdot,d)$ and $\tilde\Pi_t(\cdot,d)$ over $s_l\ge 0$. A point $x$ is the **largest maximizer** of $F$ over a set $S$ if $x$ maximizes $F$ over $S$ and every maximizer of $F$ over $S$ is at most $x$.
--
--   $\bar S_t(d)$ is the myopic order-up-to level that charges only the disposal cost of the minimal depletion; $\underline S_t(d)$ charges every excess unit the holding cost until it expires $l$ periods later and then the disposal cost.
--
--   **Formalization Note.** The weight of $\mathbb E[(s_l-d_t)^+]$ is `K L` $=\sum_{j=1}^{L-1}\gamma^jh^++\gamma^L\tilde\theta$; for $l=2$ the $h^+$ sum is empty and the weight is $\gamma\tilde\theta$. The page writes $-\gamma c\,\tilde s_{l-1}$ in $\tilde\Pi_t$, where $\tilde s_{l-1}=s_l-(d_t\vee s_1)$ depends on the state and the noise, while $\underline S_t(d)$ is a function of $d$ alone; it is read as $-\gamma c\,s_l$, which differs from $-\gamma c\,\mathbb E[\tilde s_{l-1}]$ by a term independent of $s_l$, so the maximizers are unchanged. The page prints "$\bar S_t(d)=\arg\max_{s_l\ge0}$, where $\Pi_t(s_l,d)=\dots$" without the objective; the objective is $\Pi_t(\cdot,d)$. "argmax" is read as the largest maximizer (`IsLargestMaxOn`), taken as a hypothesis wherever it is used.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §6.1, p. 294 (definitions of v_t, θ̃, Π_t, S̄_t(d), Π̃_t, S̲_t(d))

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Model

namespace PerishablePricing.Bounds

open MeasureTheory

/-!
# Chen, Pang and Pan (2014), §6.1, p. 294: the myopic objectives `Π_t`, `Π̃_t` and largest maximizers

The lifetime is `l = L + 1`, so the page's `γh⁺ + γ²h⁺ + ⋯ + γ^{l−2}h⁺ + γ^{l−1}θ̃` is
`∑_{j=1}^{L−1} γ^j h⁺ + γ^L θ̃` (empty sum when `L = 1`).
-/

namespace Model

variable (M : Model)

/-- `θ̃ = θ + γc − h⁺` (p. 294). -/
def θt : ℝ := M.θ + M.γ * M.c - M.hp

/-- The weight `γh⁺ + γ²h⁺ + ⋯ + γ^{l−2}h⁺ + γ^{l−1}θ̃` of `Π̃_t` (p. 294), with `l − 1 = L`. -/
noncomputable def K (L : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 L, M.γ ^ j * M.hp + M.γ ^ L * M.θt

/-- `v_t(s_l, d_t) = −(1 − γ) c s_l − γ c d_t − h⁺ (s_l − d_t)⁺ − h⁻ (d_t − s_l)⁺`, backlogging case
(p. 294). -/
def v (sl dt : ℝ) : ℝ :=
  -(1 - M.γ) * M.c * sl - M.γ * M.c * dt - M.hp * max (sl - dt) 0 - M.hm * max (dt - sl) 0

/-- `Π_t(s_l, d) = R(d, s_l) + E[v_t(s_l, d + ε_t)]` (p. 294), with `R(d, s_l) = P(d) d`. -/
noncomputable def Pi (sl d : ℝ) : ℝ :=
  M.P d * d + ∫ ε, M.v sl (d + ε) ∂M.μ

/-- `Π̃_t(s_l, d) = Π_t(s_l, d) − γ c s_l − (γh⁺ + ⋯ + γ^{l−2}h⁺ + γ^{l−1}θ̃) E[(s_l − d_t)⁺]`
(p. 294). The page writes `− γ c s̃_{l−1}`; as a function of the decision `s_l` (for fixed `d`)
this is read as `− γ c s_l`, which differs from it by a term not depending on `s_l`. -/
noncomputable def PiT (L : ℕ) (sl d : ℝ) : ℝ :=
  M.Pi sl d - M.γ * M.c * sl - M.K L * ∫ ε, max (sl - (d + ε)) 0 ∂M.μ

end Model

/-- The set of maximizers of `F` over `S`. -/
def argmaxOn (F : ℝ → ℝ) (S : Set ℝ) : Set ℝ := {x | x ∈ S ∧ ∀ y ∈ S, F y ≤ F x}

/-- `x` is the **largest maximizer** of `F` over `S`: `x` maximizes `F` over `S`, and every
maximizer is `≤ x`. -/
def IsLargestMaxOn (F : ℝ → ℝ) (S : Set ℝ) (x : ℝ) : Prop := IsGreatest (argmaxOn F S) x

end PerishablePricing.Bounds


