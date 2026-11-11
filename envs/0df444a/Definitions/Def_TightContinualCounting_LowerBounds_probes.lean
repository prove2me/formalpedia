-- Prove2me | Definitions.Def_TightContinualCounting_LowerBounds_probes
-- name    : TightContinualCounting_LowerBounds_probes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:26.813408+00:00
-- url     : https://prove2.me/theorems/9b8f8f17-e70e-4b13-a4e9-16152109b0f6
-- title:
--   Mean and midrange probes with variance and range potentials
-- statement:
--   Let $v\in\mathbb R^d$ and let $u\subseteq[d]$ be a nonempty finite set. Its mean, variance, midrange and range are
--
--   $$
--   \mu_u(v)=\frac1{|u|}\sum_{i\in u}v_i,\qquad
--   V_u(v)=\frac1{|u|}\sum_{i\in u}(v_i-\mu_u(v))^2,
--   $$
--   $$
--   c_u(v)=\frac{\max_{i\in u}v_i+\min_{i\in u}v_i}{2},\qquad
--   r_u(v)=\max_{i\in u}v_i-\min_{i\in u}v_i.
--   $$
--
--   The probe rule has exactly two choices, mean and midrange. Its associated spread statistic is respectively variance or range. These computed functions support the two error bounds in the tree argument; variance uses the population denominator $|u|$.
--
--   **Formalization Note** Coordinates are zero-based finite indices. Extrema are actual finite maxima and minima. The empty set has explicit zero extrema, mean and variance, but all source applications use nonempty sets.
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), p.5, probe–potential table and Eq. (1)

import Mathlib

namespace TightContinualCounting.LowerBounds

/-- Probes are used only on nonempty finite sets; empty extrema have the explicit default 0. -/
noncomputable def coordinateMax {d : ℕ} (u : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  if h : u.Nonempty then u.sup' h v else 0

noncomputable def coordinateMin {d : ℕ} (u : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  if h : u.Nonempty then u.inf' h v else 0

noncomputable def meanProbe {d : ℕ} (u : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  (∑ i ∈ u, v i) / (u.card : ℝ)

noncomputable def variancePotential {d : ℕ} (u : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  (∑ i ∈ u, (v i - meanProbe u v) ^ 2) / (u.card : ℝ)

noncomputable def midProbe {d : ℕ} (u : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  (coordinateMax u v + coordinateMin u v) / 2

noncomputable def rangePotential {d : ℕ} (u : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  coordinateMax u v - coordinateMin u v

inductive ProbeRule where
  | mid
  | mean
  deriving DecidableEq

noncomputable def probe (φ : ProbeRule) {d : ℕ}
    (u : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  match φ with
  | .mid => midProbe u v
  | .mean => meanProbe u v

end TightContinualCounting.LowerBounds


