-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
-- name    : SupportVectorMachines_Calibration_InnerRisks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:17.371449+00:00
-- url     : https://prove2.me/theorems/02fb3f47-1844-4e56-90ad-e42d829a946f
-- title:
--   The inner $L$-risk of a distribution on the label space, and its minimizer sets
-- statement:
--   This chapter (Steinwart & Christmann, *Support Vector Machines*, Springer 2008, §3.1)
--   reduces the analysis of a full risk to a pointwise analysis, one label distribution at a
--   time.
--
--   For a loss $L$, a distribution $Q$ on the label space $Y \subset \mathbb R$, a point
--   $x \in X$ and $t \in \mathbb R$, the **inner $L$-risk** of $Q$ at $x$ (Definition 3.3, p. 51)
--   is
--   $$
--   C_{L,Q,x}(t) := \int_Y L(x,y,t) \, dQ(y),
--   $$
--   and the **minimal inner $L$-risk** is $C^*_{L,Q,x} := \inf_{t \in \mathbb R} C_{L,Q,x}(t)$.
--
--   For $\varepsilon \in [0,\infty]$, the set of **$\varepsilon$-approximate minimizers**
--   (Definition 3.5, p. 53) is
--   $$
--   M_{L,Q,x}(\varepsilon) := \{ t \in \mathbb R : C_{L,Q,x}(t) < C^*_{L,Q,x} + \varepsilon \}.
--   $$
--
--   **Formalization Note** Because $L \ge 0$, the inner risk is represented as a lower Lebesgue
--   integral into $[0,\infty]$ (Lean `ENNReal`, via `∫⁻` of `ENNReal.ofReal (L x y t)`), which is
--   always well-defined with no integrability hypothesis — unlike the real-valued
--   (junk-at-non-integrable) `risk`/`bayesRisk` convention used in the `01-loss-functions`
--   mission. This chapter's central content (Lemma 3.11, Eq. (3.19)) is precisely about the
--   finite/infinite distinction for these risks, so collapsing infinity to a real junk value
--   would trivialize exactly the statements the chapter is about; `ENNReal` is used throughout
--   this mission for that reason. `minInnerRisk` is `⨅ t : ℝ, innerRisk L Q x t`, the genuine
--   infimum in the complete lattice `ENNReal` (correctly `⊤` when every $t$ gives infinite inner
--   risk).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 51-53, Definitions 3.3 and 3.5

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **inner `L`-risk** of `Q` at `x` (Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, Definition 3.3, p. 52): for a loss `L`, a distribution `Q` on the label space
`ℝ`, a point `x ∈ X` and `t ∈ ℝ`, `C_{L,Q,x}(t) := ∫_Y L(x,y,t) dQ(y)`, represented as a lower
Lebesgue integral into `[0,∞]` (always well-defined for the nonnegative integrand `L`, no
integrability hypothesis needed). -/
noncomputable def innerRisk {X : Type*} (L : Loss X) (Q : Measure ℝ) (x : X) (t : ℝ) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (L x y t) ∂Q

/-- The **minimal inner `L`-risk** of `Q` at `x` (Definition 3.3, p. 52):
`C*_{L,Q,x} := inf_{t∈ℝ} C_{L,Q,x}(t)`. -/
noncomputable def minInnerRisk {X : Type*} (L : Loss X) (Q : Measure ℝ) (x : X) : ENNReal :=
  ⨅ t : ℝ, innerRisk L Q x t

/-- The set of **`ε`-approximate minimizers** of `C_{L,Q,x}(·)` (Definition 3.5, p. 53):
`M_{L,Q,x}(ε) := {t ∈ ℝ : C_{L,Q,x}(t) < C*_{L,Q,x} + ε}`. -/
def approxMinimizers {X : Type*} (L : Loss X) (Q : Measure ℝ) (x : X) (ε : ENNReal) : Set ℝ :=
  {t : ℝ | innerRisk L Q x t < minInnerRisk L Q x + ε}

end SupportVectorMachines.Calibration


