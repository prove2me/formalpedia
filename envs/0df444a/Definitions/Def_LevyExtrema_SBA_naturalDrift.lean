-- Prove2me | Definitions.Def_LevyExtrema_SBA_naturalDrift
-- name    : LevyExtrema_SBA_naturalDrift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:36.808585+00:00
-- url     : https://prove2.me/theorems/75edbc76-c9b8-41ea-aebc-19b49d7cdc3e
-- title:
--   Natural drift $b_0=b-\int_{(-1,1)}x\,\nu(dx)$
-- statement:
--   When the jumps have finite variation, $I^1_0=\int_{(-1,1)}|x|\,\nu(dx)<\infty$, the **natural drift** of a Lévy process with triplet $(\sigma^2,\nu,b)$ (cutoff $\mathbb 1_{\{|x|<1\}}$) is
--
--   $$b_0=b-\int_{(-1,1)}x\,\nu(dx).$$
--
--   It is the drift of the process when the small jumps are not compensated.
--
--   **Formalization Note** The integral is a Bochner integral, equal to the paper's value whenever $I^1_0<\infty$; every use in the mission is under that condition.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §4.3, p. 21 (after (4.5))

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy

open MeasureTheory

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Natural drift b_0 = b − ∫_{(−1,1)} x ν(dx).**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, §4.3, p. 21: "I^1_0 < ∞ if and only
if the jumps of X have finite variation, in which case we may define the natural drift
b_0 = b − ∫_{(−1,1)} xν(dx)".

**Formalization Note.** `b` is the triplet's `γ` (cutoff `1{|x|<1}`). The integral is a Bochner
integral; it is the paper's value whenever `I^1_0 < ∞`, and every use of `naturalDrift` in this
mission is guarded by `I0 Tr 1 < ⊤` (in `alpha`, in `Cp3`, and in the case β₊ ≤ 1 of (4.14), which
forces `I^1_0 < ∞`). -/
noncomputable def naturalDrift (Tr : Triplet) : ℝ :=
  Tr.γ - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂Tr.levyMeasure

end LevyExtrema.SBA


