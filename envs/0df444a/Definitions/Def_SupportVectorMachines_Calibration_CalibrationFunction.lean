-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction
-- name    : SupportVectorMachines_Calibration_CalibrationFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:27:18.262976+00:00
-- url     : https://prove2.me/theorems/3704a922-83e5-4bb5-8275-761b41c8f575
-- title:
--   The calibration function of a target/surrogate loss pair, and calibration itself
-- statement:
--   This is the chapter's central definition (Steinwart & Christmann, *Support Vector Machines*,
--   Springer 2008, Definition 3.13, p. 58). Given a target loss $L_{\mathrm{tar}}$, a surrogate
--   loss $L_{\mathrm{sur}}$, a distribution $Q$ on the label space, and $x \in X$, the
--   **calibration function** $\delta_{\max}(\cdot, Q, x) : [0,\infty] \to [0,\infty]$ is
--   $$
--   \delta_{\max}(\varepsilon, Q, x) :=
--   \begin{cases}
--   \displaystyle\inf_{t \notin M_{L_{\mathrm{tar}},Q,x}(\varepsilon)} C_{L_{\mathrm{sur}},Q,x}(t) - C^*_{L_{\mathrm{sur}},Q,x} & \text{if } C^*_{L_{\mathrm{sur}},Q,x} < \infty \\
--   \infty & \text{if } C^*_{L_{\mathrm{sur}},Q,x} = \infty.
--   \end{cases}
--   $$
--
--   $L_{\mathrm{sur}}$ **is $L_{\mathrm{tar}}$-calibrated with respect to a set $\mathcal Q$ of
--   distributions on the label space** (Definition 3.18, p. 62) if $\delta_{\max}(\varepsilon, Q,
--   x) > 0$ for every $\varepsilon \in (0,\infty]$, $Q \in \mathcal Q$, $x \in X$ — the qualitative
--   test for whether a surrogate is a reasonable stand-in for the target loss, uniformly over the
--   whole class $\mathcal Q$.
--
--   **Formalization Note** The two cases are an explicit `if minInnerRisk Lsur Q x = ⊤ then ⊤
--   else …`, matching the book's own `if`/`else` on `C*_{Lsur,Q,x}` exactly. In the `else`
--   branch, `⨅ t ∈ S, innerRisk Lsur Q x t` (`S` the constrained-`t` set) uses `ENNReal`'s
--   complete-lattice infimum, which is `⊤` when `S = ∅` — matching the book's own reading of an
--   infimum over no valid `t` — and a genuine finite-or-`⊤` value otherwise, subtracted by
--   `minInnerRisk Lsur Q x` (finite in this branch, so the subtraction is ordinary, never the
--   `⊤ − ⊤` corner).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 58, 62, Definitions 3.13 and 3.18

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **calibration function** `δmax(·,Q,x)` of `(Ltar, Lsur)` (Steinwart & Christmann,
*Support Vector Machines*, Springer 2008, Definition 3.13, p. 58): for `ε ∈ [0,∞]`,
`δmax(ε,Q,x) := inf_{t ∉ M_{Ltar,Q,x}(ε)} C_{Lsur,Q,x}(t) - C*_{Lsur,Q,x}` if `C*_{Lsur,Q,x} < ∞`,
and `δmax(ε,Q,x) := ∞` otherwise. The infimum over the empty set (when `M_{Ltar,Q,x}(ε) = ℝ`) is
`⊤` by the ambient `ENNReal` convention, matching the book's own reading of an empty infimum. -/
noncomputable def calibrationFunction {X : Type*} (Ltar Lsur : Loss X) (Q : Measure ℝ) (x : X)
    (ε : ENNReal) : ENNReal :=
  if minInnerRisk Lsur Q x = ⊤ then ⊤
  else (⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Ltar Q x ε}, innerRisk Lsur Q x t) -
    minInnerRisk Lsur Q x

/-- `Lsur` **is `Ltar`-calibrated with respect to `𝒬`** (Definition 3.18, p. 61): for all
`ε ∈ (0,∞]`, `Q ∈ 𝒬`, and `x ∈ X`, `δmax(ε,Q,x) > 0`. -/
def IsCalibrated {X : Type*} (Ltar Lsur : Loss X) (𝒬 : Set (Measure ℝ)) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∀ Q ∈ 𝒬, ∀ x : X, 0 < calibrationFunction Ltar Lsur Q x ε

end SupportVectorMachines.Calibration


