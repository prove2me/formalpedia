-- Prove2me | Definitions.Def_TeschlODE_HigherDim_omegaPlusSet
-- name    : TeschlODE_HigherDim_omegaPlusSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:10:04.431456+00:00
-- url     : https://prove2.me/theorems/d98fefe7-ffc2-4c4a-b816-83a152b66c93
-- title:
--   The $\omega_+$-limit set $\omega_+(X)$ of a set $X$
-- statement:
--   Let $\Phi$ be a flow on $M$ with maximal intervals $I_x$ and let $X \subseteq M$. The **$\omega_+$-limit set** of $X$ is the set of all points $y \in M$ for which there exist sequences $t_k \to +\infty$ and $x_k \in X$ with $\Phi(t_k, x_k) \to y$:
--   $$\omega_+(X) = \{\, y \in M : \exists\, t_k \to \infty,\ x_k \in X,\ \Phi(t_k, x_k) \to y \,\}.$$
--   In general $\bigcup_{x \in X} \omega_+(x) \subseteq \omega_+(X)$ (8.2), and the inclusion can be strict.
--
--   **Formalization Note.** Only the $\sigma = +$ case is defined; it is the only one this mission uses (the book also works with $\sigma = +$ from Lemma 8.2 on). Each time $t_k$ is required to lie in $I_{x_k}$, so that $\Phi(t_k, x_k)$ is a value of the local flow; under the book's completeness assumption this is automatic.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 229, §8.1, definition of ω±(X)

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 229: the `ω₊`-limit set of a set `X ⊆ M`: the points `y ∈ M` for which
there are sequences `t_k → ∞` and `x_k ∈ X` with `Φ(t_k, x_k) → y`. Each `t_k` lies in the
existence interval `I (x_k)` of `x_k`, so `Φ(t_k, x_k)` is a value of the (local) flow. -/
def omegaPlusSet {E : Type*} [NormedAddCommGroup E] (M : Set E) (I : E → Set ℝ)
    (Φ : ℝ → E → E) (X : Set E) : Set E :=
  {y | y ∈ M ∧ ∃ (t : ℕ → ℝ) (x : ℕ → E), (∀ k, x k ∈ X ∧ t k ∈ I (x k)) ∧
    Filter.Tendsto t Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => Φ (t k) (x k)) Filter.atTop (nhds y)}

end TeschlODE.HigherDim


