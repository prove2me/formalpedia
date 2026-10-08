-- Prove2me | Definitions.Def_Cohen2019_Tight_Model
-- name    : Cohen2019_Tight_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:52:48.454852+00:00
-- url     : https://prove2.me/theorems/8d3cb953-ec38-46d1-a952-145cf54f1343
-- title:
--   §3 — Gaussian noise 𝒩(x, σ²I), Φ and Φ⁻¹, class probabilities, consistency (6) and the radius R (3)
-- statement:
--   This file fixes the objects of §3 and §3.1 of Cohen, Rosenfeld and Kolter. The input space is $\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$, and $\mathcal Y$ is an arbitrary set of classes.
--
--   1. **Gaussian noise.** For $x\in\mathbb R^d$ and a noise level $\sigma$, $\mathcal N(x,\sigma^2 I)$ is the law of $x+\varepsilon$, where $\varepsilon\sim\mathcal N(0,\sigma^2I)$ is isotropic Gaussian noise.
--   2. **The standard Gaussian CDF and its inverse.** $\Phi(t)=\mathbb P(Z\le t)$ for $Z\sim\mathcal N(0,1)$, and for $p\in(0,1)$, $\Phi^{-1}(p)$ is the unique $t$ with $\Phi(t)=p$.
--   3. **Classifiers and class probabilities.** A (deterministic) base classifier is a map $f:\mathbb R^d\to\mathcal Y$ whose decision regions $\{z: f(z)=c\}$ are Borel sets. Its class probabilities at $x$ are
--   $$\mathbb P(f(x+\varepsilon)=c)=\mathcal N(x,\sigma^2I)\big(\{z: f(z)=c\}\big),\qquad \varepsilon\sim\mathcal N(0,\sigma^2 I).$$
--   The smoothed classifier of (1) is $g(x)=\arg\max_{c\in\mathcal Y}\mathbb P(f(x+\varepsilon)=c)$.
--   4. **Consistency with (6).** Given a class $c_A$ and numbers $\underline{p_A}$, $\overline{p_B}$, the classifier $f$ is consistent with the observed class probabilities if
--   $$\mathbb P(f(x+\varepsilon)=c_A)\ \ge\ \underline{p_A}\qquad\text{and}\qquad \max_{c\ne c_A}\mathbb P(f(x+\varepsilon)=c)\ \le\ \overline{p_B}.$$
--   5. **The certified radius (3).** $R=\dfrac{\sigma}{2}\big(\Phi^{-1}(\underline{p_A})-\Phi^{-1}(\overline{p_B})\big)$.
--
--   These are the objects in which the paper's robustness guarantee (Theorem 1) and its tightness (Theorem 2) are stated.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. $\mathcal N(x,\sigma^2I)$ is the pushforward of Mathlib's standard Gaussian `stdGaussian` under $z\mapsto x+\sigma z$. $\Phi^{-1}(p)$ is the generalized inverse $\inf\{t:p\le\Phi(t)\}$; at $p\le 0$ and $p\ge1$ the paper's value is $\mp\infty$ and Lean's infimum returns the junk value $0$, so every statement using it assumes $0<p<1$. The middle link $\underline{p_A}\ge\overline{p_B}$ of (6) does not involve $f$ and is a separate hypothesis where used. Class probabilities are real numbers (`toReal` of a probability).
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, §3, eq. (1), p. 4; §3.1, eqs. (2), (3), p. 4; Appendix A, eqs. (6), (7), p. 13

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- The input space `ℝᵈ` of Cohen, Rosenfeld, Kolter, *Certified Adversarial Robustness via
Randomized Smoothing*, arXiv:1902.02918v2, §3, p. 3 ("a classification problem from `ℝᵈ` to
classes `𝒴`").

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the ℓ2 norm `‖·‖₂` and
`inner` is `δᵀ z`. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The isotropic Gaussian `𝒩(x, σ²I)` on `ℝᵈ` (arXiv:1902.02918v2, §3, (1), p. 4: the law of
`x + ε` with `ε ∼ 𝒩(0, σ²I)`).

**Formalization Note.** It is the pushforward of Mathlib's standard Gaussian `stdGaussian`
(law `𝒩(0, I)`) under `z ↦ x + σ • z`; for `σ > 0` this is `𝒩(x, σ²I)`. `σ` is the standard
deviation, not the variance. -/
noncomputable def gaussNoise {d : ℕ} (x : Space d) (σ : ℝ) : Measure (Space d) :=
  (stdGaussian (Space d)).map (fun z => x + σ • z)

/-- A deterministic base classifier `f : ℝᵈ → 𝒴` whose decision regions `{z | f z = c}` are
Borel sets, so that the class probabilities below are meaningful (arXiv:1902.02918v2, §3,
p. 3–4). -/
def IsMeasurableClassifier {d : ℕ} {Y : Type*} (f : Space d → Y) : Prop :=
  ∀ c : Y, MeasurableSet (f ⁻¹' {c})

/-- The class probability `ℙ(f(x + ε) = c)` with `ε ∼ 𝒩(0, σ²I)` (arXiv:1902.02918v2, §3,
(1), p. 4), i.e. the `𝒩(x, σ²I)`-measure of the pre-image `{z | f z = c}`. The smoothed
classifier `g(x)` of (1) returns the class maximizing this quantity. -/
noncomputable def classProb {d : ℕ} {Y : Type*} (f : Space d → Y) (σ : ℝ) (x : Space d)
    (c : Y) : ℝ :=
  (gaussNoise x σ (f ⁻¹' {c})).toReal

/-- `f` is consistent with the observed class probabilities (6) (arXiv:1902.02918v2, (2), p. 4;
restated as (6), p. 13): `ℙ(f(x + ε) = c_A) ≥ p̲A` and `max_{c ≠ c_A} ℙ(f(x + ε) = c) ≤ p̄B`.
The middle link `p̲A ≥ p̄B` of the chain (6) does not involve `f` and is carried as a separate
hypothesis wherever it is used. -/
def IsConsistent {d : ℕ} {Y : Type*} (f : Space d → Y) (σ : ℝ) (x : Space d) (cA : Y)
    (pA pB : ℝ) : Prop :=
  pA ≤ classProb f σ x cA ∧ ∀ c : Y, c ≠ cA → classProb f σ x c ≤ pB

/-- The certified radius `R = (σ/2)(Φ⁻¹(p̲A) − Φ⁻¹(p̄B))` of (3) (arXiv:1902.02918v2, (3), p. 4;
restated as (7), p. 13). Meaningful for `p̲A, p̄B ∈ (0, 1)`; see `PhiInvReal`. -/
noncomputable def radius (σ pA pB : ℝ) : ℝ := σ / 2 * (Cohen2019.Robust.PhiInvReal pA - Cohen2019.Robust.PhiInvReal pB)

end Cohen2019.Tight


