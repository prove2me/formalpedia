-- Prove2me | Definitions.Def_GevreyGibbsSep_toTorus
-- name    : GevreyGibbsSep_toTorus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:37.667203+00:00
-- url     : https://prove2.me/theorems/73b6af26-21d7-4768-bc30-f123508be35c
-- title:
--   Quotient map $\mathbb R^d\to\mathbb T^d$
-- statement:
--   The quotient map $\mathbb R^d\to\mathbb T^d$ reduces every coordinate modulo $2\pi$. A function on $\mathbb T^d$ is the same object as a $2\pi$-periodic function on $\mathbb R^d$ (its periodic lift), and this map is the identification.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Appendix B 1, p.34

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The quotient map `ℝ^d → T^d`, coordinatewise reduction modulo `2π` (arXiv:2608.24527
(sha256 d4fd40eb…), Appendix B 1, p.34: a function on `T^d` is a `2π`-periodic function on `ℝ^d`). -/
noncomputable def toTorus {d : ℕ} (x : Fin d → ℝ) : Torus d :=
  fun i => (x i : AddCircle (2 * Real.pi))

end GevreyGibbsSep


