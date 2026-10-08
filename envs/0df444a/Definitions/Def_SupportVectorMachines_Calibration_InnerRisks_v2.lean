-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2
-- name    : SupportVectorMachines_Calibration_InnerRisks_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:35:00.229071+00:00
-- url     : https://prove2.me/theorems/c319c36f-fa60-4809-97da-87128446b56a
-- title:
--   Inner risks, minimal inner risk and $\varepsilon$-approximate minimizers (Definitions 3.3, 3.5) — over bundled losses
-- statement:
--   For a loss $L$, a distribution $Q$ on the label space, $x \in X$ and $t \in \mathbb R$, the **inner $L$-risk** is $C_{L,Q,x}(t) := \int_Y L(x,y,t)\,dQ(y) \in [0,\infty]$, the **minimal inner risk** is $C^*_{L,Q,x} := \inf_{t \in \mathbb R} C_{L,Q,x}(t)$, and for $\varepsilon \in [0,\infty]$ the set of **$\varepsilon$-approximate minimizers** is $M_{L,Q,x}(\varepsilon) := \{t : C_{L,Q,x}(t) < C^*_{L,Q,x} + \varepsilon\}$ (Definitions 3.3 and 3.5, pp. 52–53).
--
--   **Formalization Note.** Identical to the retired module except that $L$ now ranges over the corrected bundled `Loss X` (measurable and nonnegative), so the lower Lebesgue integral defining $C_{L,Q,x}(t)$ is the book's genuine integral.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 51-53, Definitions 3.3 and 3.5

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **inner `L`-risk** of `Q` at `x` (Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, Definition 3.3, p. 52): for a loss `L`, a distribution `Q` on the label space
`ℝ`, a point `x ∈ X` and `t ∈ ℝ`, `C_{L,Q,x}(t) := ∫_Y L(x,y,t) dQ(y)`, represented as a lower
Lebesgue integral into `[0,∞]`; since `L` is measurable and nonnegative (bundled in `Loss`), this
is the genuine integral of Definition 3.3, finite or not. -/
noncomputable def innerRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (Q : Measure ℝ) (x : X)
    (t : ℝ) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (L x y t) ∂Q

/-- The **minimal inner `L`-risk** of `Q` at `x` (Definition 3.3, p. 52):
`C*_{L,Q,x} := inf_{t∈ℝ} C_{L,Q,x}(t)`. -/
noncomputable def minInnerRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (Q : Measure ℝ)
    (x : X) : ENNReal :=
  ⨅ t : ℝ, innerRisk L Q x t

/-- The set of **`ε`-approximate minimizers** of `C_{L,Q,x}(·)` (Definition 3.5, p. 53):
`M_{L,Q,x}(ε) := {t ∈ ℝ : C_{L,Q,x}(t) < C*_{L,Q,x} + ε}` for `ε ∈ [0,∞]` (so `M(ε) = ∅`
whenever `C*_{L,Q,x} = ∞`, as in the book). -/
def approxMinimizers {X : Type*} [MeasurableSpace X] (L : Loss X) (Q : Measure ℝ) (x : X)
    (ε : ENNReal) : Set ℝ :=
  {t : ℝ | innerRisk L Q x t < minInnerRisk L Q x + ε}

end SupportVectorMachines.Calibration


