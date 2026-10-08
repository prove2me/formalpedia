-- Prove2me | Definitions.Def_MifflinSemismooth_Extremal_Basic
-- name    : MifflinSemismooth_Extremal_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:40.423553+00:00
-- url     : https://prove2.me/theorems/d32631f1-4901-45ff-8842-63e6c8933e4e
-- title:
--   §2, pp. 2–5 — Lipschitz near a point, generalized gradient ∂F, directional derivative, quasidifferentiability, semismoothness (Definition 1), semiconvexity (Definition 2)
-- statement:
--   These are the basic objects of §2 of Mifflin's report. Throughout, $\mathbb R^n$ is Euclidean space with inner product $\langle\cdot,\cdot\rangle$ and norm $|\cdot|$, and $F:\mathbb R^n\to\mathbb R$.
--
--   1. **Lipschitz on a ball about $x$.** There are $r>0$ and $K\ge 0$ with $|F(y)-F(z)|\le K|y-z|$ for all $y,z$ in the open ball of radius $r$ about $x$.
--   2. **Generalized gradient.** With Clarke's generalized directional derivative
--   $$F^0(x;d)=\limsup_{h\to 0,\ t\downarrow 0}\frac{F(x+h+td)-F(x+h)}{t},$$
--   the generalized gradient of $F$ at $x$ is the support set
--   $$\partial F(x)=\{g\in\mathbb R^n:\ \langle g,d\rangle\le F^0(x;d)\ \text{for all } d\in\mathbb R^n\}.$$
--   3. **Directional derivative.** $F'(x;d)$ exists and equals $L$ when $\lim_{t\downarrow 0}[F(x+td)-F(x)]/t=L$.
--   4. **Quasidifferentiable at $x$.** For every $d$, $F'(x;d)$ exists and equals $F^0(x;d)$.
--   5. **Semismooth at $x$ (Definition 1).** $F$ is Lipschitz on a ball about $x$, and for each $d\in\mathbb R^n$ and all sequences $t_k>0$, $\theta_k\in\mathbb R^n$, $g_k\in\mathbb R^n$ with $t_k\to 0$, $\theta_k/t_k\to 0$ and $g_k\in\partial F(x+t_kd+\theta_k)$, the real sequence $\{\langle g_k,d\rangle\}$ has exactly one accumulation point.
--   6. **Semiconvex at $x$ with respect to $X\subseteq\mathbb R^n$ (Definition 2).** $F$ is Lipschitz on a ball about $x$, quasidifferentiable at $x$, and whenever $x+d\in X$ and $F'(x;d)\ge 0$, then $F(x+d)\ge F(x)$.
--   7. **"On $X$".** $F$ is semismooth (quasidifferentiable, semiconvex) on $X$ if it is so at every $x\in X$.
--
--   Semismoothness is the property that makes the generalized gradients near $x$, sampled along any curve arriving tangentially to $d$, determine a single directional slope; semiconvexity is a nonsmooth analogue of pseudoconvexity. All later statements of the mission are phrased in these terms.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; $F^0$ is the published `ClarkeGradients.Shared.genDirDeriv`, a real `limsup` that is meaningful when $F$ is Lipschitz near $x$, which is why every theorem of the mission carries the paper's Lipschitz hypothesis. $\partial F$ is Mifflin's support-set definition, not Clarke's hull of gradient limits; the two agree for locally Lipschitz $F$ by Proposition 1(c). $F'(x;d)$ is a relation (`HasDirDeriv F x d L`), never a function with a default value, so "$F'(x;d)\ge 0$" in Definition 2 is "$F'(x;d)$ exists and is $\ge 0$". The paper's "$\{t_k\}\downarrow 0$" is read as "positive and tending to $0$", the reading the paper itself uses in the proof of Lemma 2; monotone and non-monotone readings give the same class, since two accumulation points along a non-monotone sequence persist along a decreasing subsequence. "Exactly one accumulation point" is `∃!` of a cluster point (`MapClusterPt`), not convergence. Lipschitz constants are nonnegative reals (`NNReal`); the page's "positive number $K$" is equivalent after enlarging $K$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), pp. 2–5, §2, Definitions 1 and 2

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), §2, p. 2: `F` is Lipschitz on a ball about `x`. -/
def LipschitzNear {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ K : NNReal, LipschitzOnWith K F (Metric.ball x r)

/-- Mifflin (1976), §2, p. 3: the generalized gradient
`∂F(x) = {g ∈ ℝⁿ : ⟨g, d⟩ ≤ F⁰(x; d) for all d ∈ ℝⁿ}`. -/
def genGrad {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {g | ∀ d, inner ℝ g d ≤ ClarkeGradients.Shared.genDirDeriv F x d}

/-- Mifflin (1976), §2, p. 4: `F'(x; d)` exists and equals `L`, i.e.
`lim_{t ↓ 0} [F(x + t d) - F(x)] / t = L`. -/
def HasDirDeriv {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x d : EuclideanSpace ℝ (Fin n))
    (L : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (F (x + t • d) - F x) / t) (𝓝[>] 0) (𝓝 L)

/-- Mifflin (1976), §2, p. 4: `F` is quasidifferentiable at `x`: `F'(x; d)` exists and equals
`F⁰(x; d)` for each `d`. -/
def QuasidiffAt {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∀ d, HasDirDeriv F x d (ClarkeGradients.Shared.genDirDeriv F x d)

/-- Mifflin (1976), Definition 1, p. 4: `F` is semismooth at `x`. -/
def SemismoothAt {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  LipschitzNear F x ∧
  ∀ (d : EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) (θ g : ℕ → EuclideanSpace ℝ (Fin n)),
    (∀ k, 0 < t k) → Tendsto t atTop (𝓝 0) →
    Tendsto (fun k => (t k)⁻¹ • θ k) atTop (𝓝 0) →
    (∀ k, g k ∈ genGrad F (x + t k • d + θ k)) →
    ∃! c : ℝ, MapClusterPt c atTop (fun k => inner ℝ (g k) d)

/-- Mifflin (1976), Definition 2, p. 5: `F` is semiconvex at `x` with respect to `X`
(the condition `x ∈ X` is carried by the caller). -/
def SemiconvexAt {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  LipschitzNear F x ∧ QuasidiffAt F x ∧
  ∀ (d : EuclideanSpace ℝ (Fin n)) (L : ℝ), x + d ∈ X → HasDirDeriv F x d L → 0 ≤ L →
    F x ≤ F (x + d)

/-- Mifflin (1976), p. 5: `F` is semismooth on `X`. -/
def SemismoothOn {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  ∀ x ∈ X, SemismoothAt F x

/-- Mifflin (1976), p. 5: `F` is quasidifferentiable on `X`. -/
def QuasidiffOn {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  ∀ x ∈ X, QuasidiffAt F x

/-- Mifflin (1976), p. 5: `F` is semiconvex on `X` (with respect to `X`). -/
def SemiconvexOn {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    Prop :=
  ∀ x ∈ X, SemiconvexAt X F x

end MifflinSemismooth.Extremal


