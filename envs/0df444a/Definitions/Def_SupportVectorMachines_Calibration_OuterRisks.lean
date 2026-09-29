-- Prove2me | Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
-- name    : SupportVectorMachines_Calibration_OuterRisks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:26:07.356377+00:00
-- url     : https://prove2.me/theorems/5bd5fa21-1508-4145-b311-4a2c475a3263
-- title:
--   The outer (full) $L$-risk of $f$ and the Bayes risk, via the inner-risk decomposition
-- statement:
--   A distribution $P$ on $X \times Y$ is represented here by its $X$-marginal $P_X$ together
--   with a family $\kappa : X \to \mathcal M(Y)$ of conditional distributions $P(\cdot \mid x)$
--   (a Markov kernel). Eq. (3.5), p. 52, rewrites the $L$-risk of $f$ (Definition 2.2, p. 22) in
--   terms of the inner risks:
--   $$
--   R_{L,P}(f) = \int_X C_{L,P(\cdot\mid x),x}(f(x)) \, dP_X(x),
--   $$
--   and the **Bayes $L$-risk** (Definition 2.3, pp. 22-23) is
--   $R^*_{L,P} := \inf\{R_{L,P}(f) : f : X \to \mathbb R \text{ measurable}\}$.
--
--   A pair $(P_X, \kappa)$ **is of type $\mathcal Q$** (Definition 3.5, p. 53) if
--   $\kappa(x) \in \mathcal Q$ for $P_X$-almost every $x \in X$, i.e. $P(\cdot \mid x) \in
--   \mathcal Q$ for $P_X$-almost all $x$ — the notion used throughout the rest of the chapter to
--   reason about a whole class of data-generating distributions at once rather than a single
--   fixed one.
--
--   **Formalization Note** `outerRisk` is rendered directly in the `(PX, κ)` form of Eq. (3.5)
--   rather than as an integral against a joint measure on $X \times Y$ with a separately-supplied
--   disintegration hypothesis; `bayesRisk` is the `ENNReal` infimum (`⨅ f, ⨅ _ : Measurable f,
--   outerRisk L PX κ f`) over measurable `f`, correctly `⊤` when no measurable `f` exists (never
--   the case here, since `X` is inhabited by `PX` being a probability measure) and otherwise the
--   genuine infimum, with no separate junk-value convention needed since `ENNReal` already has a
--   top element for "no better value found".
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22-23, 52-53, Definitions 2.2, 2.3, 3.5, Eq. (3.5)

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- The **outer `L`-risk** of `f` (Steinwart & Christmann, *Support Vector Machines*, Springer
2008, Definition 2.2, p. 22, and Eq. (3.5), p. 52): a distribution `P` on `X × ℝ` is represented
here by its marginal `PX` on `X` together with a family `κ : X → Measure ℝ` of conditional
distributions `P(·|x)`, and `R_{L,P}(f) := ∫_X C_{L,P(·|x),x}(f(x)) dPX(x)` is rendered directly
in this `(PX, κ)` form, exactly as Eq. (3.5) rewrites the risk. -/
noncomputable def outerRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (PX : Measure X)
    (κ : X → Measure ℝ) (f : X → ℝ) : ENNReal :=
  ∫⁻ x, innerRisk L (κ x) x (f x) ∂PX

/-- The **Bayes `L`-risk** with respect to `(PX, κ)` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (PX : Measure X)
    (κ : X → Measure ℝ) : ENNReal :=
  ⨅ (f : X → ℝ) (_ : Measurable f), outerRisk L PX κ f

/-- `(PX, κ)` **is of type `𝒬`** (Definition 3.5, p. 53): `κ x ∈ 𝒬` for `PX`-almost every
`x ∈ X`, i.e. `P(·|x) ∈ 𝒬` for `PX`-almost all `x`. -/
def IsOfType {X : Type*} [MeasurableSpace X] (κ : X → Measure ℝ) (PX : Measure X)
    (𝒬 : Set (Measure ℝ)) : Prop :=
  ∀ᵐ x ∂PX, κ x ∈ 𝒬

end SupportVectorMachines.Calibration


