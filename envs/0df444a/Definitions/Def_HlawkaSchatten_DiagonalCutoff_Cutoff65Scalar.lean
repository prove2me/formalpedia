-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalCutoff_Cutoff65Scalar
-- name    : HlawkaSchatten_DiagonalCutoff_Cutoff65Scalar
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-10T06:14:43.355084+00:00
-- url     : https://prove2.me/theorems/6df1ac19-aa9f-47e6-9003-2f09041b69ce
-- title:
--   Scalar lower models for the cutoff-65 confinement window
-- statement:
--   Three explicit rational functions of $x\in[\frac1{66},\frac1{65}]$ used as lower models in the cutoff-$65$ scalar comparison.
--
--   $N^{\mathrm{lo}}(x)$ is a degree-four lower model for the cyclic numerator, $D^{\mathrm{up}}(x)$ is a degree-four upper model for the cyclic denominator, and $G^{\mathrm{lo}}(x)$ is a lower model for one minus the scalar-envelope root at confinement radius $\frac{91}{250}$. They are data: the comparisons $N^{\mathrm{lo}}(x)\,(2G^{\mathrm{lo}}(x))>(1-\frac{91}{250})D^{\mathrm{up}}(x)$ and $x N^{\mathrm{lo}}(x)>\frac{23}{50}D^{\mathrm{up}}(x)$ are separate theorems.
--
--   **Formalization Note.** The Lean names are `cutoff65Nlo`, `cutoff65Dup`, and `cutoff65Glo`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — rational scalar models for confinement radius 91/250 on the exponent window from 65 to 66.

import Mathlib.Data.Real.Basic
namespace HlawkaSchatten.DiagonalCutoff
noncomputable def cutoff65Nlo (x : ℝ) : ℝ :=
  let z := (371849888/10^8 : ℝ)*x+1/84
  let y := (6931471803/10^10+3/8*x-9/64*x^2)*x
  let c := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2)-(1+c+c^2/2+c^3/6+c^4/12)*(1+z-z^2/2+z^3/6+z^4/12)
noncomputable def cutoff65Dup (x : ℝ) : ℝ :=
  let t := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  6*(t+t^2/2+t^3/6+t^4/12)
noncomputable def cutoff65Glo (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/1000)*x
  g-(6931471808/10^10*x)^2/2+g^3/6-(6931471808/10^10*x)^4/12

end HlawkaSchatten.DiagonalCutoff


