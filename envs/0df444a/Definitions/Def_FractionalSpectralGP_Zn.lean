-- Prove2me | Definitions.Def_FractionalSpectralGP_Zn
-- name    : FractionalSpectralGP_Zn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:08.697846+00:00
-- url     : https://prove2.me/theorems/d146453e-9e3d-49e6-9325-a5d87e3519e7
-- title:
--   The Gaussian variables $Z_n=\widetilde{h_n}$ (6.1)
-- statement:
--   Given the isometry $f\mapsto\widetilde f$ and an orthonormal basis $(h_n)$ of $L^2(\mathbb R,dx)$,
--
--   $$
--   Z_n=\widetilde{h_n},\qquad n=0,1,\dots
--   $$
--
--   For a real basis these are independent standard Gaussian variables (theorem `eq_6_2_expansion`). They are the building blocks of $X_\sigma$, $W_\sigma$ and of the chaos basis $H_\alpha$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (6.1), p.21

import Mathlib
import Definitions.Def_FractionalSpectralGP_Omega

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The random variables `Z_n = h̃_n`, `n = 0, 1, …` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (6.1), p.21): the images of
the basis functions `h_n` under the isometry `f ↦ f̃`. -/
noncomputable def Zn (P : Measure Omega) (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (n : ℕ) :
    Lp ℂ 2 P :=
  ι (h n)

end FractionalSpectralGP


