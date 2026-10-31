-- Prove2me | Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals
-- name    : LevyExtrema_SBA_LevyMeasureIntegrals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:07.824233+00:00
-- url     : https://prove2.me/theorems/83c48b30-5fd1-412b-86e9-bd59e072aaf8
-- title:
--   Lévy-measure moments $I^p_0$, $I^p_+$, $I^p_-$ ((4.5), (2.1))
-- statement:
--   For the Lévy measure $\nu$ of $X$ and $p\ge0$, the paper uses the three moments
--
--   $$I^p_0=\int_{(-1,1)}|x|^p\,\nu(dx),\qquad I^p_+=\int_{[1,\infty)}x^p\,\nu(dx),\qquad I^p_-=\int_{(-\infty,-1]}|x|^p\,\nu(dx).$$
--
--   $I^p_0$ measures the activity of small jumps and defines the Blumenthal–Getoor index; $I^p_\pm$ are the moments of the large jumps, and $I^p_+<\infty$ is equivalent to $\mathbb E[\overline X_t^p]<\infty$.
--
--   **Formalization Note** All three are extended nonnegative reals ($\mathbb R_{\ge0}\cup\{\infty\}$), so the value $\infty$ is kept. With the convention $0^0=1$ and $\nu(\{0\})=0$, $I^0_0=\nu((-1,1))$.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (2.1), p. 6; (4.5), p. 21

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy

open MeasureTheory
open scoped ENNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **I^p_0 = ∫_{(−1,1)} |x|^p ν(dx)**, (4.5).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (4.5), p. 21:
"I^p_0 = ∫_{(−1,1)} |x|^p ν(dx), for any p ≥ 0".

**Formalization Note.** Valued in `ℝ≥0∞` (a lintegral), so the value `∞` is kept. `Real.rpow` has
`0^0 = 1`; since a Lévy measure has no atom at 0, `I0 Tr 0 = ν((−1,1))`. -/
noncomputable def I0 (Tr : Triplet) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioo (-1 : ℝ) 1, ENNReal.ofReal (|x| ^ p) ∂Tr.levyMeasure

/-- **I^p_+ = ∫_{[1,∞)} x^p ν(dx)**, (2.1), p. 6 (`ℝ≥0∞`-valued). -/
noncomputable def Iplus (Tr : Triplet) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ici (1 : ℝ), ENNReal.ofReal (x ^ p) ∂Tr.levyMeasure

/-- **I^p_− = ∫_{(−∞,−1]} |x|^p ν(dx)**, (2.1), p. 6 (`ℝ≥0∞`-valued). -/
noncomputable def Iminus (Tr : Triplet) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Iic (-1 : ℝ), ENNReal.ofReal (|x| ^ p) ∂Tr.levyMeasure

end LevyExtrema.SBA


