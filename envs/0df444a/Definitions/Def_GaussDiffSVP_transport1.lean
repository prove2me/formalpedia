-- Prove2me | Definitions.Def_GaussDiffSVP_transport1
-- name    : GaussDiffSVP_transport1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:47.637284+00:00
-- url     : https://prove2.me/theorems/658ed953-706b-47eb-9bf6-7c13d2781a79
-- title:
--   Transport map $\Phi_q(f,g)$
-- statement:
--   For a pair map $T$ and an activation weight $q$,
--   $$\Phi_q(f,g)(z) = \sum_{T(x,y)=z} q(x,y)\,f(x)\,g(y),$$
--   which transports one copy of the input counts $f$, $g$ to the output. Sums are in $[0,\infty]$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (20), p.23

import Mathlib

open scoped ENNReal

namespace GaussDiffSVP

/-- The positive map `Φ_q(f, g)(z) = ∑_{T(x,y) = z} q(x, y) f(x) g(y)` (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (20), p.23), which
transports one copy of the input counts through the pair map `T` and activation weight `q`.

**Formalization Note.** An unconditional sum in `ℝ≥0∞` over the pairs `(x, y)` with
`T(x, y) = z`. -/
noncomputable def transport1 {α β γ : Type*} (T : α → β → γ) (q : α → β → ℝ≥0∞)
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) (z : γ) : ℝ≥0∞ :=
  ∑' p : {p : α × β // T p.1 p.2 = z}, q p.1.1 p.1.2 * f p.1.1 * g p.1.2

end GaussDiffSVP


