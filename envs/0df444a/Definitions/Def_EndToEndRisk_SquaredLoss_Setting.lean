-- Prove2me | Definitions.Def_EndToEndRisk_SquaredLoss_Setting
-- name    : EndToEndRisk_SquaredLoss_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:31.182387+00:00
-- url     : https://prove2.me/theorems/2bcb513f-2b18-41ba-b62a-b6d9191be2c0
-- title:
--   (1)–(6), (11), (13), Definition 5, Theorem 3, pp. 2–22 — end-to-end prediction and optimization: argmin selection, optimality-gap loss, risks, calibration function
-- statement:
--   This file fixes the model of end-to-end prediction and optimization (Ho-Nguyen and Kılınç-Karzan).
--
--   **Optimization problem.** Let $X \subset \mathbb R^m$ be convex, compact and non-empty, and let $f$ be convex and continuous on $X$. For a cost vector $c \in \mathbb R^m$ the decision maker solves
--   $$\min_{x \in X} \{ f(x) + c^\top x \}. \qquad (1)$$
--   A map $x^* : \mathbb R^m \to X$ is an *argmin selection* if $x^*(d)$ minimizes $f(x) + d^\top x$ over $X$ for every $d$ (Notation, p. 7).
--
--   **Losses.** The *true loss* (2) is the optimality gap of the decision $x^*(d)$ under the true cost $c$:
--   $$L(d,c) = f(x^*(d)) + c^\top x^*(d) - \min_{x \in X} \{ f(x) + c^\top x \}.$$
--   The *squared loss* is $\ell_{LS}(d,c) = \|d - c\|_2^2$ (p. 21).
--
--   **Risks.** For a joint law $\mathbb P$ of $(w, c) \in W \times \mathbb R^m$, a predictor $g : W \to \mathbb R^m$ and a loss $\ell$, the risk is $R_\ell(g,\mathbb P) = \mathbb E[\ell(g(w), c)]$ ((3) for $\ell = L$, (5) in general), and the Bayes risk is $R_\ell(\mathbb P) = \inf_g \{ R_\ell(g,\mathbb P) : g \text{ measurable} \}$ ((4), (6)).
--
--   **Conditional quantities.** For a law $\nu$ of $c$ (playing the role of $\mathbb P[\cdot \mid w]$), the conditional risk of a prediction $d$ is $\mathbb E_\nu[\ell(d,c)]$ and its conditional excess risk is $\mathbb E_\nu[\ell(d,c)] - \inf_{d'} \mathbb E_\nu[\ell(d',c)]$.
--
--   **Classes and calibration.** The class $\mathcal P$ of p. 21 is represented by the set of admissible conditional laws: probability measures concentrated on $C$ with $\mathbb E\|c\|_2^2 < \infty$ and mean in $\mathrm{Conv}(C)$. For a class $Q$ of conditional laws, the calibration function (13) is
--   $$\delta_\ell(\epsilon; Q) = \inf_{\nu \in Q,\, d \in \mathbb R^m} \Big\{ \mathbb E_\nu[\ell(d,c)] - \inf_{d'} \mathbb E_\nu[\ell(d',c)] \;:\; \mathbb E_\nu[L(d,c)] - \inf_{d'} \mathbb E_\nu[L(d',c)] \ge \epsilon \Big\},$$
--   and $\ell$ is *$Q$-uniformly calibrated* (Definition 5) if for every $\epsilon > 0$ there is $\delta > 0$ such that, for all $\nu \in Q$ and $d$, a conditional excess $\ell$-risk below $\delta$ forces a conditional excess true risk below $\epsilon$.
--
--   **Constants (11).** $B_X = \max_{x,x' \in X}\|x - x'\|_2$ (the diameter of $X$), $B_f = \max_{x,x' \in X}\{f(x) - f(x')\}$ and $B_C = \max_{c \in C}\|c\|_2$.
--
--   **Biconjugate (Theorem 3).** For $\delta : \mathbb R \to [0,\infty]$ and $B > 0$, $\delta^{**}(\epsilon)$ is the supremum of $h'(\epsilon)$ over convex $h' : \mathbb R \to \mathbb R$ with $h' \le \delta$ on $(0, B]$ and $h'(0) \le 0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Risks and conditional risks are $[0,\infty]$-valued lower Lebesgue integrals of the non-negative losses, and excess risks use truncated subtraction in $[0,\infty]$; theorems add finiteness hypotheses wherever a subtracted Bayes risk could be infinite. A joint law is written $\mu \otimes \kappa$ with $\mu$ the law of $w$ and $\kappa$ a Markov kernel, so $\kappa(w)$ is the conditional law $\mathbb P[\cdot \mid w]$ and $\mathbb E[c \mid w] = \int c \, d\kappa(w)$. The infimum "over $\mathbb P \in \mathcal P$, $w \in W$" in (13) and Definition 5 depends only on $\mathbb P[\cdot \mid w]$, so both are stated over a set of conditional laws; this agrees with the page whenever $W$ is non-empty, since every admissible law is the conditional law of a constant kernel. The conclusion of (12) is read conditionally on $w$ (the page prints it without "$\mid w$"; its proof, p. ec9, uses the conditional form). $\delta^{**}$ carries the constraint $h'(0) \le 0$, which encodes the convention $\delta_\ell(0) = 0$ of p. 19; without it a positive constant $h'$ would be admissible and Theorem 3 would fail at $g = g^*$. Non-emptiness of $X$ is implicit on the page (an argmin over $X$).
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Risk guarantees for end-to-end prediction and optimization processes, arXiv:2012.15046v1, pp. 2–22: (1) p. 2, Notation p. 7, (2)–(6) pp. 9–10, (11) and Assumption 2 p. 19, Definition 5 and (13) p. 20, ℓ_LS and the class 𝒫 p. 21, δ** in Theorem 3 p. 20

import Mathlib

namespace EndToEndRisk.SquaredLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

/-- Standing setting of (1), p. 2, and (11), p. 19: `X ⊂ ℝ^m` is convex, compact and non-empty,
and `f` is convex and continuous on `X`. -/
def Standing {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  Convex ℝ X ∧ IsCompact X ∧ X.Nonempty ∧ ConvexOn ℝ X f ∧ ContinuousOn f X

/-- `x∗` is a selection of the argmin mapping `X∗(d) = argmin_{x ∈ X} {f(x) + dᵀx}`
(Notation, p. 7). -/
def IsArgminSelection {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ d, xstar d ∈ X ∧ ∀ x ∈ X, f (xstar d) + ⟪d, xstar d⟫_ℝ ≤ f x + ⟪d, x⟫_ℝ

/-- The optimal value `min_{x ∈ X} {f(x) + cᵀx}` appearing in (2), p. 9. -/
noncomputable def optVal {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (c : EuclideanSpace ℝ (Fin m)) : ℝ :=
  sInf ((fun x => f x + ⟪c, x⟫_ℝ) '' X)

/-- The true loss (2), p. 9: the optimality gap
`L(d, c) = f(x∗(d)) + cᵀx∗(d) − min_{x ∈ X} {f(x) + cᵀx}`. -/
noncomputable def trueLoss {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (d c : EuclideanSpace ℝ (Fin m)) : ℝ :=
  f (xstar d) + ⟪c, xstar d⟫_ℝ - optVal X f c

/-- The squared loss `ℓ_LS(d, c) = ‖d − c‖₂²`, p. 21. -/
noncomputable def lsLoss {m : ℕ} (d c : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ‖d - c‖ ^ 2

/-- The risk `E[ℓ(g(w), c)]` of a predictor `g : W → ℝ^m` under a joint law `P` on `W × ℝ^m`:
(3) for `ℓ = L`, (5) for a surrogate `ℓ`, pp. 9–10. -/
noncomputable def risk {m : ℕ} {W : Type*} [MeasurableSpace W]
    (ℓ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (P : Measure (W × EuclideanSpace ℝ (Fin m))) (g : W → EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (ℓ (g p.1) p.2) ∂P

/-- The best possible risk `inf_g {E[ℓ(g(w), c)] : g measurable}`: (4) for `ℓ = L`, (6) for a
surrogate `ℓ`, pp. 9–10. -/
noncomputable def bayesRisk {m : ℕ} {W : Type*} [MeasurableSpace W]
    (ℓ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (P : Measure (W × EuclideanSpace ℝ (Fin m))) : ℝ≥0∞ :=
  ⨅ (g : W → EuclideanSpace ℝ (Fin m)) (_ : Measurable g), risk ℓ P g

/-- The conditional risk `E[ℓ(d, c) | w]`, where the law `ν` plays the role of `ℙ[· | w]`. -/
noncomputable def condRisk {m : ℕ}
    (ℓ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (ν : Measure (EuclideanSpace ℝ (Fin m))) (d : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ c, ENNReal.ofReal (ℓ d c) ∂ν

/-- The conditional excess risk `E[ℓ(d, c) | w] − inf_{d′} E[ℓ(d′, c) | w]`, with `ν = ℙ[· | w]`. -/
noncomputable def condExcess {m : ℕ}
    (ℓ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (ν : Measure (EuclideanSpace ℝ (Fin m))) (d : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  condRisk ℓ ν d - ⨅ d', condRisk ℓ ν d'

/-- The class `𝒫` of p. 21, as the set of admissible conditional laws `ℙ[· | w]`: probability
measures on the paper's cost set `C` that are square integrable and whose mean lies in
`Conv(C)`. -/
def lsClass {m : ℕ} (C : Set (EuclideanSpace ℝ (Fin m))) :
    Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {ν | IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
    ∫⁻ c, ‖c‖ₑ ^ 2 ∂ν < ⊤ ∧ (∫ c, c ∂ν) ∈ convexHull ℝ C}

/-- The calibration function `δ_ℓ(ε; 𝒫)` of (13), p. 20, over a class `Q` of conditional laws:
the infimum of the conditional excess surrogate risk over all `ν ∈ Q` and `d ∈ ℝ^m` whose
conditional excess true risk is at least `ε`. -/
noncomputable def deltaL {m : ℕ}
    (ℓ L : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (Q : Set (Measure (EuclideanSpace ℝ (Fin m)))) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ ν ∈ Q, ⨅ (d : EuclideanSpace ℝ (Fin m)),
    ⨅ (_ : ENNReal.ofReal ε ≤ condExcess L ν d), condExcess ℓ ν d

/-- Uniform calibration, Definition 5, p. 20, in its conditional reading (12): for every `ε > 0`
there is `δ > 0` such that for every admissible conditional law `ν ∈ Q` and every `d`, a
conditional excess surrogate risk below `δ` forces a conditional excess true risk below `ε`. -/
def UniformlyCalibrated {m : ℕ}
    (ℓ L : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (Q : Set (Measure (EuclideanSpace ℝ (Fin m)))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ν ∈ Q, ∀ d : EuclideanSpace ℝ (Fin m),
    condExcess ℓ ν d < ENNReal.ofReal δ → condExcess L ν d < ENNReal.ofReal ε

/-- `B_f = max_{x, x′ ∈ X} {f(x) − f(x′)}`, (11), p. 19. -/
noncomputable def Bf {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  sSup ((fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) => f p.1 - f p.2) ''
    (X ×ˢ X))

/-- `B_C = max_{c ∈ C} ‖c‖₂`, (11), p. 19. -/
noncomputable def Bc {m : ℕ} (C : Set (EuclideanSpace ℝ (Fin m))) : ℝ :=
  sSup ((fun c => ‖c‖) '' C)

/-- `δ∗∗` of Theorem 3, p. 20, for a function `δ` and the bound `B = B_f + B_C B_X`: the supremum
of `h′(ε)` over convex `h′ : ℝ → ℝ` with `h′ ≤ δ` on `(0, B]` and `h′(0) ≤ 0` (the convention
`δ_ℓ(0) = 0` of p. 19). -/
noncomputable def deltaBiconj (δ : ℝ → ℝ≥0∞) (B ε : ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ → ℝ) (_ : ConvexOn ℝ Set.univ h) (_ : h 0 ≤ 0)
    (_ : ∀ t ∈ Set.Ioc 0 B, ENNReal.ofReal (h t) ≤ δ t), ENNReal.ofReal (h ε)

end EndToEndRisk.SquaredLoss


