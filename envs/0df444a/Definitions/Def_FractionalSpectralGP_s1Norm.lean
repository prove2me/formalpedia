-- Prove2me | Definitions.Def_FractionalSpectralGP_s1Norm
-- name    : FractionalSpectralGP_s1Norm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:25.600689+00:00
-- url     : https://prove2.me/theorems/b06763bb-a76e-4d02-849b-81f1468d7751
-- title:
--   The norms $|||g|||_k$ of $S_1$
-- statement:
--   For $g\in S_1$ and $k\in\mathbb N_0$,
--
--   $$
--   |||g|||_k=\Big(\sum_{\alpha\in\ell}(\alpha!)^2\,|g_\alpha|^2\,(2\mathbb N)^{k\alpha}\Big)^{1/2}.
--   $$
--
--   These norms define the projective limit topology of $S_1$ and hence its bounded sets.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.5), p.11

import Mathlib
import Definitions.Def_FractionalSpectralGP_multiFactorial
import Definitions.Def_FractionalSpectralGP_kondWeight

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The norm `|||g|||_k = (Σ_α (α!)² |g_α|² (2ℕ)^{kα})^{1/2}` of `𝓗_k`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (4.5), p.11).

**Formalization Note.** Meaningful for `g ∈ S₁` (`MemS1 g`), where the series converges. -/
noncomputable def s1Norm (k : ℕ) (g : (ℕ →₀ ℕ) → ℂ) : ℝ :=
  Real.sqrt (∑' α, ((multiFactorial α : ℝ)) ^ 2 * ‖g α‖ ^ 2 * kondWeight α ^ k)

end FractionalSpectralGP


