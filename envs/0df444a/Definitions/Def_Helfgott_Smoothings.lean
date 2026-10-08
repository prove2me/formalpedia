-- Prove2me | Definitions.Def_Helfgott_Smoothings
-- name    : Helfgott_Smoothings
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-04T21:07:33.535749+00:00
-- url     : https://prove2.me/theorems/c93ee551-83de-46a2-9f9f-0c5be413d419
-- title:
--   Mellin convolution and the coordinated Goldbach smoothings
-- statement:
--   Define the real Mellin convolution ∫₀∞ f(t/w)g(w) dw/w, the common box smoothing η₁=2·1_[1/2,1], its logarithmic triangular smoothing η₂(t)=4 max(log2−|log(2t)|,0) for t>0 (zero otherwise), and φ(t)=t² exp(−t²/2). Define η*(t)=(η₂ *_M φ)(49t). Also define the symmetric smoothing η_circle on [0,2] and the final major-arc smoothing η+(t)=h_200(t)t exp(−t²/2), with h(t)=t²(2−t)³ exp(t−1/2) on [0,2] and h_H its Mellin band-limited approximation. The band kernel H/π·sinc(H log w) gives the continuous value H/π at w=1. These are data definitions, not claims of integrability or any arc estimate. The box interval follows equations (4.7) and (4.10); the inconsistent interval in the section-7 introductory line is not used. The t² factor in h and extra factor t in η+ follow the final section-7 convention.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (4.3), (4.7), (4.9), (4.10), and the definitions at the start of section 7 (with κ=49), https://arxiv.org/html/1312.7748v2 . The η₁ and η₂ smoothings also occur in T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656. Written by Codex.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory

namespace Helfgott

noncomputable def mellinConv (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ w in Set.Ioi (0 : ℝ), f (t / w) * g w / w

noncomputable def etaOne (t : ℝ) : ℝ :=
  (Set.Icc (1 / 2 : ℝ) 1).indicator (fun _ => (2 : ℝ)) t

noncomputable def etaTwo (t : ℝ) : ℝ :=
  if 0 < t then 4 * max (Real.log 2 - |Real.log (2 * t)|) 0 else 0

noncomputable def phi (t : ℝ) : ℝ := t ^ 2 * Real.exp (-(t ^ 2) / 2)

noncomputable def etaStar (t : ℝ) : ℝ := mellinConv etaTwo phi (49 * t)

noncomputable def etaCircle (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) 2).indicator
    (fun t => t ^ 3 * (2 - t) ^ 3 * Real.exp (-((t - 1) ^ 2) / 2)) t

noncomputable def majorKernel (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) 2).indicator
    (fun t => t ^ 2 * (2 - t) ^ 3 * Real.exp (t - 1 / 2)) t

noncomputable def bandKernel (H t : ℝ) : ℝ :=
  H / Real.pi * Real.sinc (H * Real.log t)

noncomputable def bandLimitedMajorKernel (H t : ℝ) : ℝ :=
  mellinConv majorKernel (bandKernel H) t

noncomputable def etaPlus (t : ℝ) : ℝ :=
  bandLimitedMajorKernel 200 t * t * Real.exp (-(t ^ 2) / 2)

end Helfgott


