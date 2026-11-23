-- Prove2me | Definitions.Def_RiddledBasins_Dynamics
-- name    : RiddledBasins_Dynamics
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T20:32:32.526579+00:00
-- url     : https://prove2.me/theorems/4fe1c859-94d2-41ee-8657-7ca87b0687b0
-- title:
--   Basins, Milnor attractors, riddled and intermingled basins
-- statement:
--   This file fixes the dynamical-systems vocabulary used throughout the mission, following the primer in the paper's Methods.
--
--   Let $\Phi:\mathbb R^d\to\mathbb R^d$ be the map generating the training dynamics and write $\Phi^{t}$ for its $t$-fold iterate. The **$\omega$-limit set** of an initialization $\theta$ is
--   $$\omega(\theta)=\bigcap_{t\ge0}\overline{\{\Phi^{s}(\theta):s>t\}},$$
--   the set of accumulation points of its trajectory, and the **basin of attraction** of a set $A$ is $\beta(A)=\{\theta:\omega(\theta)\subseteq A\}$. A set $A$ is **invariant** when $\Phi^{t}(A)\subseteq A$ for every $t$. Writing $l$ for Lebesgue measure on $\mathbb R^d$, $A$ is a **Milnor attractor** when it is invariant, $l(\beta(A))>0$, and $l(\beta(A)\setminus\beta(A'))>0$ for every proper compact subset $A'\subsetneq A$. Its basin is **riddled** when
--   $$\forall\theta\in\beta(A),\ \forall\delta>0:\quad l\big(B_\delta(\theta)\cap\beta(A)^{c}\big)>0,$$
--   and two basins are **intermingled** when each has positive measure in every ball centred at any of its own points, with the roles of the two basins exchanged.
--
--   These notions are the measure-theoretic substrate of the paper's argument: unlike Lyapunov-stable attractors, a Milnor attractor may have a basin containing no neighbourhood of the attractor, which is what allows riddling to persist arbitrarily close to the destination.
--
--   **Formalization Note.** Parameter space is `EuclideanSpace ℝ (Fin d)` with `MeasureTheory.volume`; measure positivity is stated in `ℝ≥0∞`, so infinite measure is allowed and no measurability assumption is imposed here. The closure in the $\omega$-limit set is explicit, as required by the paper's phrase "set of accumulation points"; intersecting over all $t\in\mathbb N$ rather than $t>0$ gives the same set.
-- source:
--   A. Ly & P. Gong, Fractal basin geometry and the limits to predictability and reproducibility in deep learning, Nature Machine Intelligence (2026), https://doi.org/10.1038/s42256-026-01336-3, PDF p. 8, Methods, 'A dynamical systems primer' (definitions of ω-limit set, basin β(A), Milnor attractor, riddled basin); PDF p. 4, 'The emergence of riddling' (intermingled basins)

import Mathlib

open MeasureTheory Metric Set Filter Topology

namespace RiddledBasins

/-- Ambient parameter space `ℝ^d`, with its Euclidean metric and Lebesgue measure. -/
abbrev Param (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The `ω`-limit set of `θ`: the accumulation points of the trajectory `Φ^[t] θ`. -/
noncomputable def omegaLimit {d : ℕ} (Φ : Param d → Param d) (θ : Param d) : Set (Param d) :=
  ⋂ t : ℕ, closure {y | ∃ s : ℕ, t < s ∧ Φ^[s] θ = y}

/-- The basin of attraction `β(A) = {θ | ω(θ) ⊆ A}`. -/
noncomputable def basin {d : ℕ} (Φ : Param d → Param d) (A : Set (Param d)) : Set (Param d) :=
  {θ | omegaLimit Φ θ ⊆ A}

/-- Invariance: every iterate maps `A` into itself. -/
def IsInvariant {d : ℕ} (Φ : Param d → Param d) (A : Set (Param d)) : Prop :=
  ∀ t : ℕ, Φ^[t] '' A ⊆ A

/-- Milnor attractor: invariant, with a positive-measure basin that no proper compact
subset of `A` captures up to measure zero. -/
def IsMilnorAttractor {d : ℕ} (Φ : Param d → Param d) (A : Set (Param d)) : Prop :=
  IsInvariant Φ A ∧ 0 < volume (basin Φ A) ∧
    ∀ A' : Set (Param d), A' ⊆ A → IsCompact A' → A' ≠ A →
      0 < volume (basin Φ A \ basin Φ A')

/-- A riddled basin: every ball around every point of the basin meets its complement
in a set of positive Lebesgue measure. -/
def IsRiddled {d : ℕ} (Φ : Param d → Param d) (A : Set (Param d)) : Prop :=
  ∀ θ ∈ basin Φ A, ∀ δ > 0, 0 < volume (Metric.ball θ δ ∩ (basin Φ A)ᶜ)

/-- Intermingled basins: each basin has positive measure in every ball around each of
its points, and vice versa. -/
def AreIntermingled {d : ℕ} (Φ : Param d → Param d) (A B : Set (Param d)) : Prop :=
  (∀ θ ∈ basin Φ A, ∀ δ > 0, 0 < volume (Metric.ball θ δ ∩ basin Φ B)) ∧
    (∀ θ ∈ basin Φ B, ∀ δ > 0, 0 < volume (Metric.ball θ δ ∩ basin Φ A))

end RiddledBasins


