-- Prove2me | Definitions.Def_FractionalSpectralGP_MemS1
-- name    : FractionalSpectralGP_MemS1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:16.917119+00:00
-- url     : https://prove2.me/theorems/628bce06-6444-4e7d-b918-0881e777e21b
-- title:
--   Membership in the Kondratiev test space $S_1$
-- statement:
--   A formal series $g=\sum_\alpha g_\alpha H_\alpha$ belongs to the Kondratiev space $S_1$ of stochastic test functions if, for every $k$,
--
--   $$
--   |||g|||_k^2=\sum_{\alpha\in\ell}(\alpha!)^2\,|g_\alpha|^2\,(2\mathbb N)^{k\alpha}<\infty .
--   $$
--
--   $S_1=\bigcap_k\mathcal H_k$ is the first element of the Gelfand triple $S_1\subset\mathcal W\subset S_{-1}$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.5), p.11

import Mathlib
import Definitions.Def_FractionalSpectralGP_multiFactorial
import Definitions.Def_FractionalSpectralGP_kondWeight

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Membership in the Kondratiev space `S₁` of stochastic test functions, the intersection of the
Hilbert spaces `𝓗_k` with `|||f|||²_k = Σ_α (α!)² |f_α|² (2ℕ)^{kα} < ∞`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (4.5), p.11). -/
def MemS1 (g : (ℕ →₀ ℕ) → ℂ) : Prop :=
  ∀ k : ℕ, Summable fun α => ((multiFactorial α : ℝ)) ^ 2 * ‖g α‖ ^ 2 * kondWeight α ^ k

end FractionalSpectralGP


