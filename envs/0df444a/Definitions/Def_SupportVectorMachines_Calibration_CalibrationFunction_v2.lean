-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction_v2
-- name    : SupportVectorMachines_Calibration_CalibrationFunction_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:49:22.416495+00:00
-- url     : https://prove2.me/theorems/078461b5-5d22-446f-87b1-b0488982001d
-- title:
--   Calibration function $\delta_{\max}$ and $L_{\mathrm{tar}}$-calibration (Definitions 3.13, 3.18) — over bundled losses
-- statement:
--   For losses $L_{\mathrm{tar}}, L_{\mathrm{sur}}$, a distribution $Q$ on the labels, $x \in X$ and $\varepsilon \in [0,\infty]$, the **calibration function** is $\delta_{\max}(\varepsilon,Q,x) := \inf_{t \notin M_{L_{\mathrm{tar}},Q,x}(\varepsilon)} C_{L_{\mathrm{sur}},Q,x}(t) - C^*_{L_{\mathrm{sur}},Q,x}$ if $C^*_{L_{\mathrm{sur}},Q,x} < \infty$ and $:= \infty$ otherwise, with $\inf \emptyset := \infty$ (Definition 3.13, p. 58). $L_{\mathrm{sur}}$ is **$L_{\mathrm{tar}}$-calibrated with respect to $\mathcal Q$** if $\delta_{\max}(\varepsilon,Q,x) > 0$ for all $\varepsilon \in (0,\infty]$, $Q \in \mathcal Q$, $x \in X$ (Definition 3.18, p. 61).
--
--   **Formalization Note.** Identical to the retired module except that the losses range over the corrected bundled `Loss X`.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 58, 61, Definitions 3.13 and 3.18

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **calibration function** `δmax(·,Q,x)` of `(Ltar, Lsur)` (Steinwart & Christmann,
*Support Vector Machines*, Springer 2008, Definition 3.13, p. 58): for `ε ∈ [0,∞]`,
`δmax(ε,Q,x) := inf_{t ∉ M_{Ltar,Q,x}(ε)} C_{Lsur,Q,x}(t) - C*_{Lsur,Q,x}` if `C*_{Lsur,Q,x} < ∞`,
and `δmax(ε,Q,x) := ∞` otherwise. The infimum over the empty set (when `M_{Ltar,Q,x}(ε) = ℝ`) is
`⊤` by the ambient `ENNReal` convention, matching the book's own reading of an empty infimum;
the subtraction is exact since every `C_{Lsur,Q,x}(t) ≥ C*_{Lsur,Q,x}`. -/
noncomputable def calibrationFunction {X : Type*} [MeasurableSpace X] (Ltar Lsur : Loss X)
    (Q : Measure ℝ) (x : X) (ε : ENNReal) : ENNReal :=
  if minInnerRisk Lsur Q x = ⊤ then ⊤
  else (⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Ltar Q x ε}, innerRisk Lsur Q x t) -
    minInnerRisk Lsur Q x

/-- `Lsur` **is `Ltar`-calibrated with respect to `𝒬`** (Definition 3.18, p. 61): for all
`ε ∈ (0,∞]`, `Q ∈ 𝒬`, and `x ∈ X`, `δmax(ε,Q,x) > 0`. -/
def IsCalibrated {X : Type*} [MeasurableSpace X] (Ltar Lsur : Loss X) (𝒬 : Set (Measure ℝ)) :
    Prop :=
  ∀ ε : ENNReal, 0 < ε → ∀ Q ∈ 𝒬, ∀ x : X, 0 < calibrationFunction Ltar Lsur Q x ε

end SupportVectorMachines.Calibration


