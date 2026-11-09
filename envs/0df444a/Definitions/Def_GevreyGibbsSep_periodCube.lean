-- Prove2me | Definitions.Def_GevreyGibbsSep_periodCube
-- name    : GevreyGibbsSep_periodCube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:48.377774+00:00
-- url     : https://prove2.me/theorems/d1cb1ee5-caea-44ce-bb43-c410860e7b79
-- title:
--   The period cell $[0,2\pi)^d$
-- statement:
--   The **period cell** is the half-open cube $[0,2\pi)^d\subseteq\mathbb R^d$. Integrals over the torus are Lebesgue integrals over this cell, as in Eq. (1): $\int_{\mathbb T^d}f=\int_{[0,2\pi)^d}f(x)\,dx$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (1), p.5

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The period cell `[0, 2π)^d ⊆ ℝ^d` over which the paper integrates (arXiv:2608.24527
(sha256 d4fd40eb…), Eq. (1), p.5). -/
def periodCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Ico 0 (2 * Real.pi))

end GevreyGibbsSep


