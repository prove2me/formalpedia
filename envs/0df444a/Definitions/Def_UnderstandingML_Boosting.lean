-- Prove2me | Definitions.Def_UnderstandingML_Boosting
-- name    : UnderstandingML_Boosting
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:58:31.078483+00:00
-- url     : https://prove2.me/theorems/1b1a1c77-5cd0-4d18-8a37-257a09abaf25
-- title:
--   Chapter 10: γ-weak learnability (Def. 10.1), weighted error, the AdaBoost distributions, weights and output, the class L(B, T) of (10.4), decision stumps and 3-piece classifiers
-- statement:
--   Chapter 10 of Shalev-Shwartz and Ben-David. **Definition 10.1:** $A$ is a **γ-weak-learner** for $H$ if there is $m_H : (0,1) \to \mathbb{N}$ such that for every $\delta \in (0,1)$, every distribution $D$ over $X$ and every labeling function $f$ realizable by $H$, running $A$ on $m \ge m_H(\delta)$ examples returns $h$ with $L_{(D,f)}(h) \le 1/2 - \gamma$ with probability at least $1-\delta$ (`IsWeakLearnerWith`); $H$ is **γ-weak-learnable** if such an $A$ exists (`WeakLearnable`). **AdaBoost (§10.2):** on $S = (x_1,y_1),\dots,(x_m,y_m)$ with weak hypotheses $h_t$, $D^{(1)} = (1/m,\dots,1/m)$, $\epsilon_t = \sum_i D^{(t)}_i \mathbb{1}[h_t(x_i) \ne y_i]$ (`weightedError`, `adaError`), $w_t = \frac12\log(1/\epsilon_t - 1)$ (`adaWeight`), $D^{(t+1)}_i \propto D^{(t)}_i \exp(-w_t y_i h_t(x_i))$ (`adaDist`, rounds indexed from $0$), and the output $h_s(x) = \operatorname{sign}(\sum_t w_t h_t(x))$ (`adaBoost`). **Equation (10.4):** $L(B,T) = \{x \mapsto \operatorname{sign}(\sum_{t=1}^T w_t h_t(x)) : w \in \mathbb{R}^T, h_t \in B\}$ (`linearCombClass`). Labels and hypotheses are Boolean with `sgn true = 1`, `sgn false = -1`, and $\operatorname{sign}(z)$ is `true` iff $z > 0$. **Example 10.1:** decision stumps $\{x \mapsto \operatorname{sign}(x-\theta)\cdot b\}$ over $\mathbb{R}$ (`decisionStumps`, the thresholds and their negations) and the 3-piece classifiers $h_{\theta_1,\theta_2,b}$ with $\theta_1 < \theta_2$ (`threePiece`, `threePieceClassifiers`).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §10.1 Definition 10.1 (p. 131) and Example 10.1 (p. 132), §10.2 AdaBoost (pp. 134-135), §10.3 Equation (10.4) (p. 137)

import Definitions.Def_UnderstandingML_VC

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 10: boosting

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §10.1–§10.3.

**γ-weak learnability (Definition 10.1).** `A` is a γ-weak-learner for `H` if there is
`m_H : (0,1) → ℕ` such that for every `δ ∈ (0,1)`, every distribution `D` over `X` and every
labeling function `f` realizable by `H`, running `A` on `m ≥ m_H(δ)` examples returns `h` with
`L_{(D,f)}(h) ≤ 1/2 − γ` with probability at least `1 − δ`; `H` is γ-weak-learnable if such an
`A` exists.

**AdaBoost (§10.2).** On a training set `S = (x₁, y₁), …, (x_m, y_m)`, `D⁽¹⁾ = (1/m, …, 1/m)`;
at round `t` the weak learner returns `hₜ`, `εₜ = ∑ᵢ Dᵢ⁽ᵗ⁾ 𝟙[hₜ(xᵢ) ≠ yᵢ]`,
`wₜ = ½ log(1/εₜ − 1)`, `Dᵢ⁽ᵗ⁺¹⁾ ∝ Dᵢ⁽ᵗ⁾ exp(−wₜ yᵢ hₜ(xᵢ))`; the output is
`h_s(x) = sign(∑ₜ wₜ hₜ(x))`.

**Linear combinations of base hypotheses (10.4).** `L(B, T) = {x ↦ sign(∑ₜ wₜ hₜ(x)) : w ∈ ℝᵀ,
hₜ ∈ B}`.

**Conventions.** Labels and hypotheses are `Bool`-valued, with `sgn true = 1`, `sgn false = −1`
as the book's `±1`; `sign(z)` is `true` iff `z > 0`. Rounds are indexed from `0`, so `adaDist S h 0`
is the book's `D⁽¹⁾`. The weak hypotheses are given as a sequence `h : ℕ → X → Bool` (whatever
the weak learner returned), so AdaBoost is a deterministic function of `S` and `h`. The book's
`wₜ` is undefined at `εₜ = 0`; `Real.log` makes it `0` there, so the theorems assume `εₜ > 0`.
-/

open MeasureTheory

namespace UnderstandingML

/-- The `±1` value of a Boolean label: `sgn true = 1`, `sgn false = −1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

section WeakLearning

variable {X : Type*} [MeasurableSpace X]

/-- **Definition 10.1**: `A` is a **γ-weak-learner** for `H` with the function `mH`: for every
`δ ∈ (0,1)`, every distribution `D`, every measurable labeling function `f` realizable by `H` and
every `m ≥ mH(δ)`, the probability that `L_{(D,f)}(A(S)) > 1/2 − γ` is at most `δ`. -/
def IsWeakLearnerWith (H : Set (X → Bool)) (γ : ℝ) (A : Learner (X × Bool) (X → Bool))
    (mH : ℝ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ D : Measure X, IsProbabilityMeasure D →
    ∀ f : X → Bool, Measurable f → Realizable H D f → ∀ m : ℕ, mH δ ≤ m →
      iidLaw (labeledLaw D f) m {S | 1 / 2 - γ < trueError D f (A m S)} ≤ ENNReal.ofReal δ

/-- `H` is **γ-weak-learnable** (Definition 10.1). -/
def WeakLearnable (H : Set (X → Bool)) (γ : ℝ) : Prop :=
  ∃ (A : Learner (X × Bool) (X → Bool)) (mH : ℝ → ℕ), IsWeakLearnerWith H γ A mH

end WeakLearning

section AdaBoost

variable {X : Type*}

/-- The **weighted error** `L_D(h) = ∑ᵢ Dᵢ 𝟙[h(xᵢ) ≠ yᵢ]` of `h` on the sample `S` under the
probability vector `D` (§10.1.1, §10.2). -/
def weightedError {m : ℕ} (D : Fin m → ℝ) (S : Fin m → X × Bool) (h : X → Bool) : ℝ :=
  ∑ i, D i * (if h (S i).1 = (S i).2 then 0 else 1)

/-- The AdaBoost weight `w = ½ log(1/ε − 1)` of a weak hypothesis with weighted error `ε`. -/
noncomputable def adaWeight (ε : ℝ) : ℝ := (1 / 2) * Real.log (1 / ε - 1)

/-- The AdaBoost distributions `D⁽ᵗ⁺¹⁾` over the sample (rounds indexed from `0`):
`adaDist S h 0 = (1/m, …, 1/m)` and
`adaDist S h (t+1) i ∝ adaDist S h t i · exp(−wₜ yᵢ hₜ(xᵢ))` with `wₜ = adaWeight εₜ`. -/
noncomputable def adaDist {m : ℕ} (S : Fin m → X × Bool) (h : ℕ → X → Bool) :
    ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 1 / m
  | t + 1 =>
    let D := adaDist S h t
    let w := adaWeight (weightedError D S (h t))
    fun i ↦ D i * Real.exp (-(w * sgn (S i).2 * sgn (h t (S i).1))) /
      ∑ j, D j * Real.exp (-(w * sgn (S j).2 * sgn (h t (S j).1)))

/-- `εₜ`, the weighted error of the round-`t` weak hypothesis under `D⁽ᵗ⁾`. -/
noncomputable def adaError {m : ℕ} (S : Fin m → X × Bool) (h : ℕ → X → Bool) (t : ℕ) : ℝ :=
  weightedError (adaDist S h t) S (h t)

/-- The **output of AdaBoost** after `T` rounds, `h_s(x) = sign(∑ₜ wₜ hₜ(x))`. -/
noncomputable def adaBoost {m : ℕ} (S : Fin m → X × Bool) (h : ℕ → X → Bool) (T : ℕ) :
    X → Bool :=
  fun x ↦ decide (0 < ∑ t ∈ Finset.range T, adaWeight (adaError S h t) * sgn (h t x))

/-- **Equation (10.4)**: the class `L(B, T)` of halfspaces over `T` base hypotheses from `B`. -/
def linearCombClass (B : Set (X → Bool)) (T : ℕ) : Set (X → Bool) :=
  {h | ∃ (w : Fin T → ℝ) (hs : Fin T → X → Bool), (∀ t, hs t ∈ B) ∧
    h = fun x ↦ decide (0 < ∑ t, w t * sgn (hs t x))}

end AdaBoost

/-! ### Decision stumps and 3-piece classifiers over `ℝ` (Example 10.1, §10.3) -/

section Stumps

/-- The class of **decision stumps** over `ℝ`, `{x ↦ sign(x − θ)·b : θ ∈ ℝ, b ∈ {±1}}`
(Example 10.1): the threshold functions `x ↦ [θ < x]` and their negations `x ↦ [x ≤ θ]`. -/
def decisionStumps : Set (ℝ → Bool) :=
  {h | ∃ θ : ℝ, h = fun x ↦ decide (θ < x)} ∪ {h | ∃ θ : ℝ, h = fun x ↦ decide (x ≤ θ)}

/-- The **3-piece classifier** `h_{θ₁,θ₂,b}` (Example 10.1): `b` on `x < θ₁` and `x > θ₂`, `−b` on
`[θ₁, θ₂]`. -/
noncomputable def threePiece (θ₁ θ₂ : ℝ) (b : Bool) : ℝ → Bool :=
  fun x ↦ if x < θ₁ ∨ θ₂ < x then b else !b

/-- The class of 3-piece classifiers `{h_{θ₁,θ₂,b} : θ₁ < θ₂, b ∈ {±1}}` (Example 10.1). -/
def threePieceClassifiers : Set (ℝ → Bool) :=
  {h | ∃ (θ₁ θ₂ : ℝ) (b : Bool), θ₁ < θ₂ ∧ h = threePiece θ₁ θ₂ b}

end Stumps

end UnderstandingML


