-- Prove2me | Definitions.Def_RobustGeneralization_BernLower_Model
-- name    : RobustGeneralization_BernLower_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:19:03.414775+00:00
-- url     : https://prove2.me/theorems/c6ae39c2-05e8-4453-a8b0-14aab3e50d83
-- title:
--   The (θ⋆, τ)-Bernoulli model, linear classifiers, ℓ∞^ε-robust error, expected robust error of a linear learner, and posteriors (Defs. 3, 7)
-- statement:
--   This file fixes the objects of the lower bound for linear classifiers in the Bernoulli model of Schmidt, Santurkar, Tsipras, Talwar and Mądry.
--
--   **Space, labels, perturbations.** Points live in $\mathbb R^d$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$. Labels are $y\in\{\pm1\}$. For $x\in\mathbb R^d$ and $\varepsilon\in\mathbb R$ the $\ell_\infty$ ball is
--   $$\mathcal B_\infty^\varepsilon(x)=\{x'\in\mathbb R^d : |x'_i-x_i|\le\varepsilon\ \text{for all } i\}.$$
--   For $w\in\mathbb R^d$ the **linear classifier** is $f_w(x)=\operatorname{sgn}\langle w,x\rangle\in\{\pm1\}$, with the tie $\langle w,x\rangle=0$ sent to $+1$.
--
--   **Bernoulli model (Definition 7).** Let $\theta\in\{\pm1\}^d$ and $\tau>0$. A sample $(x,y)\in\{\pm1\}^d\times\{\pm1\}$ is drawn by choosing $y$ uniformly in $\{\pm1\}$ and then, independently for each coordinate $i$, setting $x_i=y\theta_i$ with probability $\tfrac12+\tau$ and $x_i=-y\theta_i$ with probability $\tfrac12-\tau$. Thus
--   $$P_{\theta,\tau}(x,y)=\tfrac12\prod_{i=1}^d\Big(\tfrac12+\tau\,y\,\theta_i x_i\Big).$$
--
--   **Robust error (Definition 3).** For a classifier $f:\mathbb R^d\to\{\pm1\}$ the $\ell_\infty^\varepsilon$-robust classification error under the $(\theta,\tau)$-model is
--   $$\beta_{\theta,\tau}(f,\varepsilon)=\Pr_{(x,y)\sim P_{\theta,\tau}}\big[\exists x'\in\mathcal B_\infty^\varepsilon(x):\ f(x')\ne y\big].$$
--
--   **Linear learners and their expected robust error.** A linear-classifier learning algorithm on $n$ samples is any map $g$ from $(\{\pm1\}^d\times\{\pm1\})^n$ to $\mathbb R^d$. If $\theta^\star$ is uniform on $\{\pm1\}^d$ and $S=((x_1,y_1),\dots,(x_n,y_n))$ consists of $n$ independent samples from the $(\theta^\star,\tau)$-model, the joint weight is $J(\theta,S)=2^{-d}\prod_{k=1}^n P_{\theta,\tau}(x_k,y_k)$, and the expected robust error of $g$ is
--   $$\mathbb E_{\theta^\star,S}\big[\beta_{\theta^\star,\tau}(f_{g(S)},\varepsilon)\big]=\sum_{\theta}\sum_S J(\theta,S)\,\beta_{\theta,\tau}(f_{g(S)},\varepsilon).$$
--
--   **Posteriors.** By Bayes' rule, $\Pr[\theta^\star_i=b\mid S]=\sum_{\theta:\theta_i=b}J(\theta,S)\big/\sum_\theta J(\theta,S)$, and $\mathbb E[\theta^\star_i\mid S]=\Pr[\theta^\star_i=+1\mid S]-\Pr[\theta^\star_i=-1\mid S]$. The same objects are also defined for $d=1$ (a single parameter $\theta\in\{\pm1\}$, samples $(x,y)\in\{\pm1\}^2$), where the posterior odds are $\Pr[\theta=+1\mid S]/\Pr[\theta=-1\mid S]$. Finally, for $m\in\mathbb R^d$ the product law $\rho_m(\theta)=\prod_i\frac{1+m_i\theta_i}{2}$ on $\{\pm1\}^d$ has coordinate means $m_i$ (a probability law when all $|m_i|\le1$).
--
--   These are the only objects the lower-bound theorem and its milestones need; every probability is a finite sum.
--
--   **Formalization Note** Points of $\{\pm1\}^d$ are encoded by sign vectors `Fin d → Bool` (`true` ↦ $+1$), labels by `Bool`. "Sampling each coordinate" in Definition 7 is read as independent sampling, the reading the paper's proofs use. The tie rule $\operatorname{sgn}(0)=+1$ is a convention: the paper's $\operatorname{sgn}(0)$ is not in $\{\pm1\}$. The model weights are meaningful for $0<\tau\le\tfrac12$; the theorems assume $0<\tau\le\tfrac14$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 5, Definitions 2–3 and the linear classifier f_w; pp. 6–7, Definition 7; p. 35, Theorem 31 (linear classifier learning algorithm, θ⋆ uniform); p. 33, proof of Lemma 29 (posterior); p. 36, proof of Theorem 31 (E[θ⋆_i|S])

import Mathlib

namespace RobustGeneralization.BernLower

open scoped BigOperators

/-- The ambient space `ℝ^d` with the Euclidean inner product. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Labels `y ∈ {±1}` are encoded as `Bool`: `true ↦ +1`, `false ↦ -1`. -/
def lab (b : Bool) : ℝ := if b then 1 else -1

/-- The ℓ∞ ball `B∞^ε(x) = {x' ∈ ℝ^d | ‖x' - x‖∞ ≤ ε}`, written coordinatewise. -/
def linfBall {d : ℕ} (x : E d) (ε : ℝ) : Set (E d) :=
  {x' | ∀ i, |x' i - x i| ≤ ε}

/-- The linear classifier `f_w(x) = sgn ⟨w, x⟩`, with the tie `⟨w, x⟩ = 0` sent to `+1`. -/
noncomputable def linClf {d : ℕ} (w : E d) (x : E d) : Bool :=
  decide (0 ≤ inner ℝ w x)

/-- The hypercube point `x ∈ {±1}^d ⊂ ℝ^d` encoded by a sign vector `s : Fin d → Bool`. -/
noncomputable def pm {d : ℕ} (s : Fin d → Bool) : E d :=
  WithLp.toLp 2 (fun i => lab (s i))

/-- Probability of one sample `(x, y) = (pm s, y)` under the `(θ, τ)`-Bernoulli model
(Definition 7): `y` uniform on `{±1}`, then independently for each coordinate
`x_i = y θ_i` with probability `1/2 + τ` and `x_i = -y θ_i` with probability `1/2 - τ`.
The condition `s i = (y == θ i)` says exactly `x_i = y θ_i`. -/
noncomputable def bernW {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (p : (Fin d → Bool) × Bool) : ℝ :=
  (1 / 2) * ∏ i, (if p.1 i = (p.2 == θ i) then 1 / 2 + τ else 1 / 2 - τ)

/-- The `ℓ∞^ε`-robust classification error (Definition 3) of a classifier `f : ℝ^d → {±1}`
under the `(θ, τ)`-Bernoulli model: the probability that some `x' ∈ B∞^ε(x)` has `f x' ≠ y`. -/
noncomputable def robErr {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (f : E d → Bool) (ε : ℝ) : ℝ := by
  classical
  exact ∑ p : (Fin d → Bool) × Bool,
    bernW θ τ p * (if ∃ x' ∈ linfBall (pm p.1) ε, f x' ≠ p.2 then 1 else 0)

/-- Joint weight of `(θ⋆, S)` when `θ⋆` is uniform on `{±1}^d` and `S` consists of `n`
independent samples from the `(θ⋆, τ)`-Bernoulli model. -/
noncomputable def joint {d n : ℕ} (τ : ℝ) (θ : Fin d → Bool)
    (S : Fin n → (Fin d → Bool) × Bool) : ℝ :=
  (1 / 2) ^ d * ∏ k, bernW θ τ (S k)

/-- Expected `ℓ∞^ε`-robust classification error of the linear classifier `f_w`, `w = g S`,
output by a linear-classifier learning algorithm `g` on `n` samples, when `θ⋆` is uniform on
`{±1}^d` and the samples are drawn from the `(θ⋆, τ)`-Bernoulli model. -/
noncomputable def expRobErr {d n : ℕ} (g : (Fin n → (Fin d → Bool) × Bool) → E d)
    (τ ε : ℝ) : ℝ :=
  ∑ θ : Fin d → Bool, ∑ S : Fin n → (Fin d → Bool) × Bool,
    joint τ θ S * robErr θ τ (linClf (g S)) ε

/-- Posterior probability `Pr[θ⋆_i = b | S]` (Bayes' rule as a ratio of joint weights). -/
noncomputable def postProb {d n : ℕ} (τ : ℝ) (S : Fin n → (Fin d → Bool) × Bool)
    (i : Fin d) (b : Bool) : ℝ := by
  classical
  exact (∑ θ : Fin d → Bool, if θ i = b then joint τ θ S else 0) /
    (∑ θ : Fin d → Bool, joint τ θ S)

/-- Posterior mean `E[θ⋆_i | S] = Pr[θ⋆_i = +1 | S] - Pr[θ⋆_i = -1 | S]`. -/
noncomputable def postMean {d n : ℕ} (τ : ℝ) (S : Fin n → (Fin d → Bool) × Bool)
    (i : Fin d) : ℝ :=
  postProb τ S i true - postProb τ S i false

/-- One-dimensional `(θ, τ)`-Bernoulli model (`d = 1`, as in Lemma 29): probability of one
sample `(x, y) ∈ {±1} × {±1}`, `x = y θ` with probability `1/2 + τ`. -/
noncomputable def bern1W (θ : Bool) (τ : ℝ) (p : Bool × Bool) : ℝ :=
  (1 / 2) * (if p.1 = (p.2 == θ) then 1 / 2 + τ else 1 / 2 - τ)

/-- Joint weight of `(θ, S)` in the one-dimensional model, `θ` uniform on `{±1}`. -/
noncomputable def joint1 {n : ℕ} (τ : ℝ) (θ : Bool) (S : Fin n → Bool × Bool) : ℝ :=
  (1 / 2) * ∏ k, bern1W θ τ (S k)

/-- Posterior `Pr[θ = b | S]` in the one-dimensional model. -/
noncomputable def post1 {n : ℕ} (τ : ℝ) (S : Fin n → Bool × Bool) (b : Bool) : ℝ :=
  joint1 τ b S / (∑ θ : Bool, joint1 τ θ S)

/-- Posterior odds `Pr[θ = +1 | S] / Pr[θ = -1 | S]` in the one-dimensional model. -/
noncomputable def odds1 {n : ℕ} (τ : ℝ) (S : Fin n → Bool × Bool) : ℝ :=
  post1 τ S true / post1 τ S false

/-- A product law on `{±1}^d` whose `i`-th coordinate has mean `m i`
(requires `|m i| ≤ 1` to be a probability law). -/
noncomputable def prodLaw {d : ℕ} (m : Fin d → ℝ) (θ : Fin d → Bool) : ℝ :=
  ∏ i, (1 + m i * lab (θ i)) / 2

end RobustGeneralization.BernLower


