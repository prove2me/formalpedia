-- Prove2me | Definitions.Def_SpencerEight_G3
-- name    : SpencerEight_G3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:43.091364+00:00
-- url     : https://prove2.me/theorems/8a498f67-42bd-482f-8a09-cccf2a080e96
-- title:
--   Scalar cubic moment $G_3(a,t)$
-- statement:
--   For a standard Gaussian $\xi$, $G_3(a,t):=\mathbb E[(\sqrt a\,|\xi|-t)_+^3]$.
--
--   **Formalization Note** A Bochner integral; Lemma 8.49 states the integrability.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.49, p.109 (PDF p.109)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace SpencerEight

/-- `G₃(a, t) := E[(√a |ξ| − t)³₊]` for a standard Gaussian `ξ` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.49, p.109 (PDF p.109)).

**Formalization Note** A Bochner integral. Lemma 8.49 asserts the integrability, so the junk value of a non-integrable integrand plays no role; the integrand is bounded by a cubic in `|ξ|`. -/
noncomputable def G3 (a t : ℝ) : ℝ :=
  ∫ x, (max (Real.sqrt a * |x| - t) 0) ^ 3 ∂(gaussianReal 0 1)

end SpencerEight


