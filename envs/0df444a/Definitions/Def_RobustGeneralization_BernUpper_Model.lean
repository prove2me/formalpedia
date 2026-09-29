-- Prove2me | Definitions.Def_RobustGeneralization_BernUpper_Model
-- name    : RobustGeneralization_BernUpper_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:28:59.125512+00:00
-- url     : https://prove2.me/theorems/ddac5070-1cfc-4fde-bd6f-5c81d2598ebf
-- title:
--   The (θ⋆, τ)-Bernoulli model, classification and ℓ∞^ε-robust error, the thresholding map T and the one-sample estimator (Defs. 2, 3, 7; p. 7)
-- statement:
--   This file fixes the objects of the Bernoulli-model upper bound of Schmidt, Santurkar, Tsipras, Talwar and Mądry.
--
--   **Space, labels, classifiers.** Points live in $\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$ and inner product $\langle\cdot,\cdot\rangle$. Labels are $y\in\{\pm1\}$, and a binary classifier is any map $f:\mathbb R^d\to\{\pm1\}$. For a vector $w\in\mathbb R^d$ the linear classifier is $f_w(x)=\operatorname{sgn}(\langle w,x\rangle)$, with the convention $f_w(x)=+1$ when $\langle w,x\rangle=0$.
--
--   **The $(\theta^\star,\tau)$-Bernoulli model** (Definition 7). Fix $\theta^\star\in\{\pm1\}^d$ and $\tau\in(0,\tfrac12]$. A sample $(x,y)\in\{\pm1\}^d\times\{\pm1\}$ is drawn by choosing $y$ uniformly in $\{\pm1\}$ and then, independently for each coordinate $i$,
--   $$x_i=\begin{cases} y\,\theta^\star_i & \text{with probability } \tfrac12+\tau,\\ -y\,\theta^\star_i & \text{with probability } \tfrac12-\tau.\end{cases}$$
--   Since every quantity is finite, the probability $\mathbb P[A]$ of an event $A$ of one sample is the finite sum of the weights $\tfrac12\prod_i(\tfrac12\pm\tau)$ of the samples in $A$.
--
--   **Errors** (Definitions 2 and 3). The classification error of $f$ is $\mathbb P_{(x,y)}[f(x)\neq y]$. For $\varepsilon\in\mathbb R$ let $\mathcal B^\varepsilon_\infty(x)=\{x'\in\mathbb R^d : \|x'-x\|_\infty\le\varepsilon\}$; the $\ell_\infty^\varepsilon$-robust classification error of $f$ is
--   $$\mathbb P_{(x,y)}\big[\exists\, x'\in\mathcal B^\varepsilon_\infty(x):\ f(x')\neq y\big].$$
--   The adversary may move $x$ to any point of $\mathbb R^d$ in the ball, not only to points of the hypercube.
--
--   **Thresholding and the one-sample estimator.** The thresholding map $T:\mathbb R^d\to\mathbb R^d$ is $T(x)_i=+1$ if $x_i\ge0$ and $T(x)_i=-1$ otherwise, and $f_w\circ T$ is the classifier $x\mapsto f_w(T(x))$. From one sample $(x,y)$ one forms $z=yx$ and the unit vector $z/\|z\|_2$.
--
--   These objects are shared by every statement of the mission: the standard-generalization bounds (Lemmas 24–26, Theorem 27, Corollary 28) and the robust bound for $f_{\hat w}\circ T$ (Theorem 10).
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; labels and hypercube coordinates are `Bool` (`true` ↦ $+1$, `false` ↦ $-1$), with `pm s` the $\pm1$ vector of a sign pattern `s`. The ball $\mathcal B^\varepsilon_\infty$ is written coordinatewise, $|x'_i-x_i|\le\varepsilon$ for all $i$ (not the Euclidean ball). "Sampling each coordinate" is read as independent coordinates given $y$, which is how the paper's proofs use the model. `bprob θ τ A` is the finite sum of the weights over the event `A`; it is a probability when $0\le\tau\le\tfrac12$, which every theorem of the mission assumes. The tie $\langle w,x\rangle=0$ is sent to $+1$, since $\operatorname{sgn}(0)\notin\{\pm1\}$. `unitZ p` is $z/\|z\|_2$, which is $0$ in the degenerate case $d=0$.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 5 Definitions 2–3 and the linear classifier f_w; pp. 6–7 Definition 7; p. 7 the thresholding operation T

import Mathlib

namespace RobustGeneralization.BernUpper

/-- The ambient space `ℝ^d` with its Euclidean (ℓ2) norm and inner product. -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Labels `y ∈ {±1}` are encoded as `Bool`: `true ↦ +1`, `false ↦ -1`. -/
noncomputable def lab (b : Bool) : ℝ := if b then 1 else -1

/-- The sign vector in `{±1}^d ⊆ ℝ^d` with coordinates `lab (s i)`. -/
noncomputable def pm {d : ℕ} (s : Fin d → Bool) : E d := WithLp.toLp 2 (fun i => lab (s i))

/-- The ℓ∞ ball `B∞^ε(x) = {x' ∈ ℝ^d | ‖x' − x‖∞ ≤ ε}`, written coordinatewise
(Schmidt et al., arXiv:1804.11285v2, p. 5, Definition 3). -/
def linfBall {d : ℕ} (x : E d) (ε : ℝ) : Set (E d) := {x' : E d | ∀ i, |x' i - x i| ≤ ε}

/-- The linear classifier `f_w(x) = sgn(⟨w, x⟩)` (p. 5), with the tie `⟨w, x⟩ = 0` sent to `+1`
(`true`). -/
noncomputable def linClf {d : ℕ} (w : E d) (x : E d) : Bool := decide (0 ≤ inner ℝ w x)

/-- Probability weight of one sample `(x, y) = (pm s, y)` under the `(θ⋆, τ)`-Bernoulli model
(Definition 7, pp. 6–7), with `θ⋆ = pm θ`: the label is uniform on `{±1}` and, given `y`, the
coordinates are independent with `x_i = y θ⋆_i` with probability `1/2 + τ` and `x_i = −y θ⋆_i`
with probability `1/2 − τ`. -/
noncomputable def bernW {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (p : (Fin d → Bool) × Bool) : ℝ :=
  (1 / 2) * ∏ i, (if p.1 i = (p.2 == θ i) then 1 / 2 + τ else 1 / 2 - τ)

open Classical in
/-- The probability, for one sample `p = (s, y)` drawn from the `(θ⋆, τ)`-Bernoulli model, of the
event `A`. -/
noncomputable def bprob {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (A : (Fin d → Bool) × Bool → Prop) : ℝ :=
  ∑ p, bernW θ τ p * (if A p then 1 else 0)

/-- Classification error `P[f(x) ≠ y]` of a classifier `f : ℝ^d → {±1}` (Definition 2, p. 5). -/
noncomputable def clsErr {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (f : E d → Bool) : ℝ :=
  bprob θ τ (fun p => f (pm p.1) ≠ p.2)

/-- ℓ∞^ε-robust classification error `P[∃ x' ∈ B∞^ε(x) : f(x') ≠ y]` (Definition 3, p. 5). -/
noncomputable def robErr {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (f : E d → Bool) (ε : ℝ) : ℝ :=
  bprob θ τ (fun p => ∃ x' ∈ linfBall (pm p.1) ε, f x' ≠ p.2)

/-- The thresholding map `T : ℝ^d → ℝ^d`, `T(x)_i = +1` if `x_i ≥ 0` and `−1` otherwise (p. 7). -/
noncomputable def thr {d : ℕ} (x : E d) : E d := WithLp.toLp 2 (fun i => if 0 ≤ x i then (1 : ℝ) else -1)

/-- The classifier `f_w ∘ T`. -/
noncomputable def thrClf {d : ℕ} (w : E d) (x : E d) : Bool := linClf w (thr x)

/-- The vector `z = yx` built from one sample `p = (s, y)`. -/
noncomputable def zvec {d : ℕ} (p : (Fin d → Bool) × Bool) : E d := lab p.2 • pm p.1

/-- The unit vector `ŵ = z / ‖z‖₂` in the direction of `z = yx` (`0` when `d = 0`). -/
noncomputable def unitZ {d : ℕ} (p : (Fin d → Bool) × Bool) : E d := ‖zvec p‖⁻¹ • zvec p

end RobustGeneralization.BernUpper


