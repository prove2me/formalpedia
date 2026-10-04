-- Prove2me | Definitions.Def_Cohen2019_Robust_Model
-- name    : Cohen2019_Robust_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:01.12531+00:00
-- url     : https://prove2.me/theorems/3e9a9d8c-70b1-48b3-9569-73f924ce2f03
-- title:
--   §3 — Gaussian noise $\mathcal N(x,\sigma^2 I)$, class probabilities, the smoothed prediction (1) and the certified radius (3)
-- statement:
--   Fix a dimension $d$, a set of classes $\mathcal Y$ and a noise level $\sigma$. Write $\|\cdot\|$ for the Euclidean norm on $\mathbb R^d$ and $\delta^\top z$ for the standard inner product.
--
--   1. **Gaussian noise.** $\mathcal N(x, \sigma^2 I)$ is the law of $x + \varepsilon$ with $\varepsilon \sim \mathcal N(0,\sigma^2 I)$, i.e. of $x + \sigma u$ with $u$ a standard Gaussian vector in $\mathbb R^d$.
--   2. **Base classifier.** A base classifier is a deterministic or random function $f : \mathbb R^d \to \mathcal Y$. A random $f$ is described by the probabilities $\mathbb P(f(z) = c)$, $c \in \mathcal Y$, which form a probability distribution on $\mathcal Y$ for each $z$; a deterministic $f$ puts mass $1$ on one class.
--   3. **Class probabilities.** For $x \in \mathbb R^d$ and $c \in \mathcal Y$,
--   $$
--   p_c(x) = \mathbb P\big(f(x+\varepsilon) = c\big) = \mathbb E_{u \sim \mathcal N(0,I)}\big[\mathbb P(f(x + \sigma u) = c)\big].
--   $$
--   4. **Smoothed classifier.** The smoothed classifier of eq. (1) is $g(x) = \arg\max_{c \in \mathcal Y} p_c(x)$; the paper leaves $g$ undefined when the argmax is not unique. Accordingly "$g(x) = c$" means that $c$ is the unique maximizer: $p_{c'}(x) < p_c(x)$ for every $c' \ne c$.
--   5. **Certified radius.** For $\underline{p_A}, \overline{p_B} \in [0,1]$,
--   $$
--   R = \frac{\sigma}{2}\Big(\Phi^{-1}(\underline{p_A}) - \Phi^{-1}(\overline{p_B})\Big),
--   $$
--   an extended real number, with $\Phi^{-1}(0) = -\infty$ and $\Phi^{-1}(1) = +\infty$.
--
--   These are the objects of Theorem 1 of Cohen, Rosenfeld and Kolter: $g$ is the Gaussian-smoothed version of an arbitrary classifier $f$, and $R$ is the radius of the $\ell_2$ ball around $x$ on which $g$ is guaranteed to be constant.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. `gaussNoise x σ` is the pushforward of Mathlib's `stdGaussian` under $z \mapsto x + \sigma z$. A random classifier is `f : ℝᵈ → PMF 𝒴`; `classProb f σ x c` is the published Gaussian smoothing `RandomGradFree.Shared.smoothing` of $z \mapsto \mathbb P(f(z) = c)$ at $x$ with parameter $\sigma$; it is meaningful when $z \mapsto \mathbb P(f(z) = c)$ is measurable, which the theorems assume. `IsSmoothedPrediction f σ x c` is the strict unique-maximizer predicate; $g$ itself is not defined. `certRadius σ pA pB` is computed in `EReal`: for $\sigma > 0$ it is $+\infty$ when $\underline{p_A} = 1 > \overline{p_B}$ or $\underline{p_A} > 0 = \overline{p_B}$, and $\bot$ (so that no $\delta$ satisfies $\|\delta\| < R$) in the two corners $\underline{p_A} = \overline{p_B} = 0$ and $\underline{p_A} = \overline{p_B} = 1$, where the formula reads $\infty - \infty$.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, §3, eq. (1), p. 4; §3.1, Theorem 1, eqs. (2)–(3), p. 4; Theorem 1 (restated), eqs. (6)–(7), p. 13; proof of Lemma 3, p. 12 (random h); PDF pages

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_Cohen2019_Robust_Phi

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- The isotropic Gaussian `𝒩(x, σ²I)` on `ℝᵈ`: the law of `x + ε`, `ε ∼ 𝒩(0, σ²I)`.
Cohen–Rosenfeld–Kolter, *Certified Adversarial Robustness via Randomized Smoothing*,
arXiv:1902.02918v2, §3, eq. (1), p. 4; `X := x + ε` and `Y := x + δ + ε`, proof of Theorem 1,
p. 13 (PDF pages).

**Formalization Note.** `ℝᵈ` is `EuclideanSpace ℝ (Fin d)` (so `‖·‖` is the ℓ₂ norm and the inner
product `inner ℝ δ z` is `δᵀz`), with its Borel σ-algebra. `𝒩(x, σ²I)` is the pushforward of Mathlib's
standard Gaussian `stdGaussian` under `z ↦ x + σ • z`; for `σ ≠ 0` it has the density
`(2πσ²)^{-d/2} exp(−‖z − x‖²/(2σ²))`. -/
noncomputable def gaussNoise {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (σ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => x + σ • z)

/-- The class probability `ℙ(f(x + ε) = c)`, `ε ∼ 𝒩(0, σ²I)`, of a deterministic or random base
classifier `f : ℝᵈ → 𝒴`. Cohen–Rosenfeld–Kolter, arXiv:1902.02918v2, §3, eq. (1), p. 4; (2), p. 4;
(6), p. 13 (PDF pages).

**Formalization Note.** A random classifier is a map `f : ℝᵈ → PMF 𝒴` (`f z c` is the probability
that `f(z) = c`, the paper's convention "h(1|x)", proof of Lemma 3, p. 12); a deterministic
`f₀ : ℝᵈ → 𝒴` is `fun z => PMF.pure (f₀ z)`. The class probability is the Gaussian smoothing
`E_u h(x + σu)`, `u ∼ 𝒩(0, I)`, of `h(z) = ℙ(f(z) = c)` (the published
`RandomGradFree.Shared.smoothing`), i.e. `∫ (f z c) d𝒩(x, σ²I)(z)`. It is meaningful when
`z ↦ f z c` is measurable, which every theorem using it assumes. -/
noncomputable def classProb {d : ℕ} {Y : Type*} (f : EuclideanSpace ℝ (Fin d) → PMF Y) (σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (c : Y) : ℝ :=
  RandomGradFree.Shared.smoothing (fun z => (f z c).toReal) σ x

/-- "`g(x) = c`" for the smoothed classifier `g(x) = argmax_c ℙ(f(x + ε) = c)` of eq. (1):
`c` is the **unique** maximizer, i.e. every other class has strictly smaller probability.
Cohen–Rosenfeld–Kolter, arXiv:1902.02918v2, §3, eq. (1), p. 4 ("We leave undefined the behavior of
g when the argmax is not unique"); proof of Theorem 1, p. 13 and (9), p. 14 (PDF pages).

**Formalization Note.** The smoothed classifier `g` is not defined as a function (its value at a
tie is undefined in the paper); only the predicate "`g(x)` is defined and equals `c`" is. -/
def IsSmoothedPrediction {d : ℕ} {Y : Type*} (f : EuclideanSpace ℝ (Fin d) → PMF Y) (σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (c : Y) : Prop :=
  ∀ c' : Y, c' ≠ c → classProb f σ x c' < classProb f σ x c

/-- The certified radius `R = (σ/2)(Φ⁻¹(p̲A) − Φ⁻¹(p̄B))` of eq. (3), p. 4 (restated (7), p. 13),
Cohen–Rosenfeld–Kolter, arXiv:1902.02918v2 (PDF pages).

**Formalization Note.** Computed in `EReal` with `PhiInv`. For `σ > 0` and `0 ≤ p̄B ≤ p̲A ≤ 1`:
`R = +∞` if `p̲A = 1 > p̄B` or `p̲A > 0 = p̄B`; `R = ⊥` (a vacuous radius) in the two corners
`p̲A = p̄B = 0` and `p̲A = p̄B = 1`, where the paper's formula reads `∞ − ∞` (Lean's `EReal`
gives `⊥ − ⊥ = ⊤ − ⊤ = ⊥`); otherwise the real number `(σ/2)(Φ⁻¹(p̲A) − Φ⁻¹(p̄B))`. -/
noncomputable def certRadius (σ pA pB : ℝ) : EReal :=
  ((σ / 2 : ℝ) : EReal) * (PhiInv pA - PhiInv pB)

end Cohen2019.Robust


