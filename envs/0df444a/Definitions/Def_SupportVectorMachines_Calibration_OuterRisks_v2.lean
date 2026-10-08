-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_OuterRisks_v2
-- name    : SupportVectorMachines_Calibration_OuterRisks_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:49:06.337318+00:00
-- url     : https://prove2.me/theorems/e2b726cd-539f-4c80-aee2-d029893884d7
-- title:
--   Outer risk, Bayes risk and distributions of type $\mathcal Q$ (Definitions 2.2, 2.3, 3.5, Eq. (3.5)) — over bundled losses
-- statement:
--   A distribution $P$ on $X \times Y$ is represented by its marginal $P_X$ and a measurable family $\kappa = P(\cdot\mid x)$ of conditional distributions. The **$L$-risk** of $f : X \to \mathbb R$ is $R_{L,P}(f) := \int_X C_{L,P(\cdot\mid x),x}(f(x))\,dP_X(x) \in [0,\infty]$ (Eq. (3.5)), the **Bayes $L$-risk** is $R^*_{L,P} := \inf\{R_{L,P}(f) : f \text{ measurable}\}$ (Definition 2.3), and $P$ is **of type $\mathcal Q$** if $P(\cdot\mid x) \in \mathcal Q$ for $P_X$-almost all $x$ (Definition 3.5).
--
--   **Formalization Note.** Identical to the retired module except that $L$ ranges over the corrected bundled `Loss X`; with $L$ measurable and $f$ measurable the lower integral is the book's genuine $[0,\infty]$-valued risk.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22-23, 52-53, Definitions 2.2, 2.3, 3.5, Eq. (3.5)

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **outer `L`-risk** of `f` (Steinwart & Christmann, *Support Vector Machines*, Springer
2008, Definition 2.2, p. 22, and Eq. (3.5), p. 52): a distribution `P` on `X × ℝ` is represented
here by its marginal `PX` on `X` together with a measurable family `κ : X → Measure ℝ` of
conditional distributions `P(·|x)` (a regular conditional probability, which exists since the
label space is Polish, Lemma A.3.16), and `R_{L,P}(f) := ∫_X C_{L,P(·|x),x}(f(x)) dPX(x)` is
rendered directly in this `(PX, κ)` form, exactly as Eq. (3.5) rewrites the risk. For a
measurable `f` and a loss `L` (measurable, nonnegative) this is the book's `[0,∞]`-valued risk. -/
noncomputable def outerRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (PX : Measure X)
    (κ : X → Measure ℝ) (f : X → ℝ) : ENNReal :=
  ∫⁻ x, innerRisk L (κ x) x (f x) ∂PX

/-- The **Bayes `L`-risk** with respect to `(PX, κ)` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`, an infimum in `[0,∞]`. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (PX : Measure X)
    (κ : X → Measure ℝ) : ENNReal :=
  ⨅ (f : X → ℝ) (_ : Measurable f), outerRisk L PX κ f

/-- `(PX, κ)` **is of type `𝒬`** (Definition 3.5, p. 53): `κ x ∈ 𝒬` for `PX`-almost every
`x ∈ X`, i.e. `P(·|x) ∈ 𝒬` for `PX`-almost all `x`. -/
def IsOfType {X : Type*} [MeasurableSpace X] (κ : X → Measure ℝ) (PX : Measure X)
    (𝒬 : Set (Measure ℝ)) : Prop :=
  ∀ᵐ x ∂PX, κ x ∈ 𝒬

end SupportVectorMachines.Calibration


