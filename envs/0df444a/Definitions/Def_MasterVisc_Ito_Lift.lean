-- Prove2me | Definitions.Def_MasterVisc_Ito_Lift
-- name    : MasterVisc_Ito_Lift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:58.833548+00:00
-- url     : https://prove2.me/theorems/15e656ad-a05e-4bf7-87e6-f788a23eb1b9
-- title:
--   §2.3, (2.8)–(2.11) — the lift F(t, X̃) = f(t, ℙ̃_X̃), its Fréchet derivative DF and the L²-continuity of DF
-- statement:
--   This module records the lifting of §2.3 of Wu and Zhang.
--
--   Let $(\tilde\Omega,\tilde{\mathcal F},\tilde{\mathbb P})$ be a probability space. $\mathbb L^2(\tilde\Omega;\widehat\Omega)$ is the set of measurable $\tilde X:\tilde\Omega\to\widehat\Omega$ with $\mathbb E^{\tilde{\mathbb P}}[\|\tilde X\|^2]<\infty$, and $\mathbb L^2(\tilde\Omega;\mathbb R^d)$ the set of measurable $\xi$ with $\|\xi\|_2^2:=\mathbb E^{\tilde{\mathbb P}}[|\xi|^2]<\infty$. A function $f$ on $\widehat\Theta$ is lifted to (2.8) $F(t,\tilde X):=f(t,\tilde{\mathbb P}_{\tilde X})$.
--
--   1. **Fréchet differentiability** (2.9). $F$ is Fréchet differentiable at every $(t,\tilde X)$, $t\le T$, with derivative $DF(t,\tilde X)\in\mathbb L^2(\tilde\Omega;\mathbb R^d)$:
--   $$
--   F(t,\tilde X+\xi\mathbf 1_{[t,T]})-F(t,\tilde X)=\mathbb E^{\tilde{\mathbb P}}\big[DF(t,\tilde X)\cdot\xi\big]+o(\|\xi\|_2),\qquad\xi\in\mathbb L^2(\tilde\Omega;\mathbb R^d).
--   $$
--   2. **Continuity of $DF$** (2.11):
--   $$
--   \lim_{n\to\infty}\mathbb E^{\tilde{\mathbb P}}\big[|DF(t,\tilde X^n)-DF(t,\tilde X)|^2\big]=0\quad\text{whenever}\quad\lim_{n\to\infty}\mathbb E^{\tilde{\mathbb P}}\big[d_{SK}^2(\tilde X^n,\tilde X)\big]=0.
--   $$
--   3. **Uniform continuity of $DF$** (the hypothesis added in Corollary 2.3): for every $\varepsilon>0$ there is $\eta>0$ such that $\mathbb E[|DF(t,\tilde X')-DF(t,\tilde X)|^2]<\varepsilon$ for all $t\le T$ and all $\tilde X,\tilde X'\in\mathbb L^2(\tilde\Omega;\widehat\Omega)$ with $\mathbb E[d_{SK}^2(\tilde X',\tilde X)]<\eta$.
--
--   These are the hypotheses of Theorem 2.2 and Corollary 2.3, which produce the derivative $\partial_\mu f$.
--
--   **Formalization Note** $o(\|\xi\|_2)$ is written in $\varepsilon$–$\eta$ form. $DF$ is a given function of $(t,\tilde X)$; "Fréchet differentiable" is required at every point $(t,\tilde X)$ with $t\le T$, a quantifier the page leaves implicit. The page does not say in which variables the continuity of Corollary 2.3 is uniform; the reading here (uniform in $t$ and in $\tilde X$) is the one its proof uses ("one can choose a common subsequence … for all $\tilde X$"). The expectations of squares are taken in $[0,\infty]$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), §2.3, (2.8)–(2.11), p. 941; Corollary 2.3, p. 943

import Mathlib
import Definitions.Def_MasterVisc_Ito_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

open EthierKurtz

/-! ### The lift of f to 𝕃²(Ω̃; Ω̂) and its Fréchet derivative (§2.3, (2.8)–(2.11), p. 941) -/

variable {d : ℕ} {T : ℝ≥0} {Ω' : Type} [MeasurableSpace Ω']

/-- X̃ ∈ 𝕃²(Ω̃; Ω̂): a measurable Ω̂-valued random variable with 𝔼[‖X̃‖²] < ∞. -/
noncomputable def IsL2D (P : Measure Ω') (X : Ω' → DPath d T) : Prop :=
  Measurable X ∧ ∫⁻ ω, supD (X ω) ^ 2 ∂P < ⊤

/-- ξ ∈ 𝕃²(Ω̃; ℝ^d): a measurable ℝ^d-valued random variable with 𝔼[|ξ|²] < ∞. -/
noncomputable def IsL2V (P : Measure Ω') (ξ : Ω' → SDEState d) : Prop :=
  Measurable ξ ∧ ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂P < ⊤

/-- ‖ξ‖₂ = (𝔼[|ξ|²])^{1/2}. -/
noncomputable def l2norm (P : Measure Ω') (ξ : Ω' → SDEState d) : ℝ :=
  Real.sqrt (∫ ω, ‖ξ ω‖ ^ 2 ∂P)

/-- The lift F(t, X̃) := f(t, ℙ̃_X̃) of (2.8) is Fréchet differentiable at every (t, X̃) with
derivative DF(t, X̃) ∈ 𝕃²(Ω̃; ℝ^d) in the sense of (2.9):
F(t, X̃ + ξ1_{[t,T]}) − F(t, X̃) = 𝔼[DF(t, X̃) · ξ] + o(‖ξ‖₂) over ξ ∈ 𝕃²(Ω̃; ℝ^d). -/
noncomputable def IsFrechetLift (P : Measure Ω') (f : ℝ≥0 → Measure (DPath d T) → ℝ)
    (DF : ℝ≥0 → (Ω' → DPath d T) → Ω' → SDEState d) : Prop :=
  ∀ t X, t ≤ T → IsL2D P X →
    IsL2V P (DF t X) ∧
    ∀ ε > 0, ∃ η > 0, ∀ ξ : Ω' → SDEState d, IsL2V P ξ → l2norm P ξ < η →
      |f t (P.map (fun ω => bumpD t (X ω) (ξ ω))) - f t (P.map X)
          - ∫ ω, inner ℝ (DF t X ω) (ξ ω) ∂P| ≤ ε * l2norm P ξ

/-- (2.11): DF is continuous: lim 𝔼|DF(t, X̃ⁿ) − DF(t, X̃)|² = 0 whenever lim 𝔼[d²_SK(X̃ⁿ, X̃)] = 0. -/
noncomputable def IsL2ContDF (P : Measure Ω') (DF : ℝ≥0 → (Ω' → DPath d T) → Ω' → SDEState d) : Prop :=
  ∀ t, t ≤ T → ∀ (X : ℕ → Ω' → DPath d T) (Xlim : Ω' → DPath d T),
    (∀ n, IsL2D P (X n)) → IsL2D P Xlim →
    Tendsto (fun n => ∫⁻ ω, dSK (X n ω) (Xlim ω) ^ 2 ∂P) atTop (𝓝 0) →
    Tendsto (fun n => ∫⁻ ω, ‖DF t (X n) ω - DF t Xlim ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)

/-- The continuity (2.11) is uniform (in t and in X̃):
for every ε > 0 there is η > 0 with 𝔼|DF(t, X̃′) − DF(t, X̃)|² < ε whenever 𝔼[d²_SK(X̃′, X̃)] < η. -/
noncomputable def IsUnifL2ContDF (P : Measure Ω') (DF : ℝ≥0 → (Ω' → DPath d T) → Ω' → SDEState d) : Prop :=
  ∀ ε > 0, ∃ η > 0, ∀ t (X X' : Ω' → DPath d T), t ≤ T → IsL2D P X → IsL2D P X' →
    ∫⁻ ω, dSK (X' ω) (X ω) ^ 2 ∂P < ENNReal.ofReal η →
    ∫⁻ ω, ‖DF t X' ω - DF t X ω‖ₑ ^ 2 ∂P < ENNReal.ofReal ε

end MasterVisc.Ito


