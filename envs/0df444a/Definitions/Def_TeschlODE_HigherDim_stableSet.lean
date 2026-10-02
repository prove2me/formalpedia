-- Prove2me | Definitions.Def_TeschlODE_HigherDim_stableSet
-- name    : TeschlODE_HigherDim_stableSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:13:57.687651+00:00
-- url     : https://prove2.me/theorems/17e62a5c-a190-45d5-8880-a2e64cc4fbd1
-- title:
--   Stable and unstable sets $W^\pm(\Lambda)$ (8.8)
-- statement:
--   Let $\Phi$ be a flow on $M$ with maximal intervals $I_x$, let $\Lambda \subseteq M$ and $\sigma \in \{1, -1\}$. The **stable** ($\sigma = 1$) respectively **unstable** ($\sigma = -1$) **set** of $\Lambda$ is
--   $$W^{\sigma}(\Lambda) = \{\, x \in M : \lim_{t \to \sigma\infty} d(\Phi_t(x), \Lambda) = 0 \,\}, \qquad (8.8)$$
--   where $d(x, A) = \inf\{|x - y| : y \in A\}$ is the distance from $x$ to $A$. The unstable set of a point, $W^-(x)$, is $W^-(\{x\})$: the points whose solution tends to $x$ as $t \to -\infty$.
--
--   **Formalization Note.** For a local flow the limit $t \to \sigma\infty$ only makes sense if the solution through $x$ exists for all $\sigma t \ge 0$; this is required explicitly. The limit is written as $s \to +\infty$ with $t = \sigma s$. The sign is the real number $\sigma = \pm 1$; the theorems use $\sigma = 1$ and $\sigma = -1$ only. $d(x, A)$ is `Metric.infDist`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 231, §8.1, Eq. (8.8)

import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 231, (8.8): the stable (`σ = 1`) or unstable (`σ = -1`) set of `Λ`,
`W^σ(Λ) = {x ∈ M | lim_{t→σ∞} d(Φ_t(x), Λ) = 0}`. For the local flow the limit requires the
solution through `x` to exist for all `σ t ≥ 0`, i.e. `x` is `σ` complete; the limit
`t → σ∞` is written as `s → ∞` with `t = σ s`. Here `d(x, Λ)` is `Metric.infDist x Λ`. -/
def stableSet {E : Type*} [NormedAddCommGroup E] (M : Set E) (I : E → Set ℝ)
    (Φ : ℝ → E → E) (σ : ℝ) (Λ : Set E) : Set E :=
  {x | x ∈ M ∧ (∀ t : ℝ, 0 ≤ σ * t → t ∈ I x) ∧
    Filter.Tendsto (fun s : ℝ => Metric.infDist (Φ (σ * s) x) Λ) Filter.atTop (nhds 0)}

end TeschlODE.HigherDim


