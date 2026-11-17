-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_stdGaussian
-- name    : EffRobustLearn_Supplement_stdGaussian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:16:25.567067+00:00
-- url     : https://prove2.me/theorems/6bb2615c-af68-40ae-b294-a2c0ac77c03f
-- title:
--   The standard Gaussian $N(0,I_d)$ and the uniform law on $\{\pm1\}^d$, as laws on $\mathbb R^d$
-- statement:
--   Two distributions on $\mathbb R^d$:
--
--   1. the **standard Gaussian** $N(0,I_d)$, the product of $d$ standard normal laws;
--   2. the **uniform distribution on the Boolean cube** $\{\pm1\}^d$, viewed as a law on $\mathbb R^d$ supported on the cube: independent coordinates, each equal to $+1$ or $-1$ with probability $1/2$.
--
--   These are the two distributions of Theorem 4.10.
--
--   **Formalization Note** The module defines `stdGaussian d` and `unifCube d` on `Fin d → ℝ`.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Theorem 4.10, p.24 (PDF p.25)

import Mathlib

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

/-- The standard Gaussian distribution `N(0, I_d)` on `ℝ^d` (Theorem 4.10 of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…),
p.24, PDF p.25): the product of `d` standard normal laws. -/
noncomputable def stdGaussian (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1

/-- The uniform distribution on the Boolean cube `{±1}^d`, as a law on `ℝ^d` supported on the cube
(Theorem 4.10, p.24): independent coordinates, each `±1` with probability `1/2`. -/
noncomputable def unifCube (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => (2⁻¹ : ENNReal) • (Measure.dirac (1 : ℝ) + Measure.dirac (-1))

end Supplement

end EffRobustLearn


