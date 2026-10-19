-- Prove2me | Definitions.Def_DROCalibration_Sensitivity_Setting
-- name    : DROCalibration_Sensitivity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:40.878546+00:00
-- url     : https://prove2.me/theorems/6d0419ac-f085-4cff-a018-0a254a20417e
-- title:
--   §2, pp. 7–8 and App. F, p. 48 — Assumption 2.1, the worst-case family (2.7), the conjugate φ* (F.5), mean and variance under ℙ_n
-- statement:
--   This file fixes the objects of the worst-case sensitivity theorem of Gotoh, Kim and Lim.
--
--   Throughout, a decision $x$ is fixed and the data are $n$ points with nominal probabilities $p_1,\dots,p_n$, where $p_i>0$ and $\sum_i p_i=1$; the paper's empirical distribution $\mathbb P_n$ is the case $p_i=1/n$. The reward of the fixed decision at the $i$-th point is $f_i=f(x,Y_i)$, so the decision and the data enter only through the vector $f=(f_1,\dots,f_n)$.
--
--   1. **Assumption 2.1.** A function $\phi:\mathbb R\to\mathbb R\cup\{+\infty\}$ satisfies Assumption 2.1 if it is closed (lower semicontinuous) and convex, $\phi(z)\ge\phi(1)=0$ for $z\ge0$, $\phi(z)=+\infty$ for $z<0$, and $\phi$ is finite and twice continuously differentiable on an open interval around $z=1$ with $\phi''(1)>0$.
--   2. **The penalized objective of (2.7).** For $\delta>0$ and a probability vector $q=(q_1,\dots,q_n)$,
--   $$J_\delta(q)=\sum_{i=1}^n q_i f_i+\frac1\delta\sum_{i=1}^n p_i\,\phi\!\left(\frac{q_i}{p_i}\right)\in\mathbb R\cup\{+\infty\}.$$
--   3. **The worst-case measures $\mathbb Q(\delta)$.** For $\delta>0$, the set of minimizers of $J_\delta$ over the probability simplex $\{q: q_i\ge0,\ \sum_i q_i=1\}$.
--   4. **The convex conjugate (F.5).** $\phi^*(\zeta)=\sup_{z\in\mathbb R}\{\zeta z-\phi(z)\}\in[-\infty,+\infty]$.
--   5. **Mean and variance under $\mathbb P_n$.** $\mathbb E_{\mathbb P_n}[f]=\sum_i p_i f_i$ and $\mathbb V_{\mathbb P_n}[f]=\sum_i p_i\big(f_i-\mathbb E_{\mathbb P_n}[f]\big)^2$.
--
--   The worst-case sensitivity (2.8) of the expected reward is the one-sided limit, as $\delta\downarrow0$, of $-(\mathbb E_{\mathbb Q(\delta)}[f]-\mathbb E_{\mathbb P_n}[f])/\delta$; the theorems of the mission state it as a limit, so the $\delta=0$ branch $\mathbb Q(0)=\mathbb P_n$ of (2.7) needs no separate definition.
--
--   **Formalization Note** $\phi$ takes values in `EReal`, and convexity is written pointwise on $\mathbb R$ (with the `EReal` convention $0\cdot(+\infty)=0$), because `EReal` is not a vector space; since $\phi=+\infty$ off $[0,\infty)$ this is convexity of the extended function. Derivatives of $\phi$ and $\phi^*$ are those of their real parts `phiReal`, `conjReal` (`EReal.toReal`), which agree with $\phi$ and $\phi^*$ wherever these are finite; `phiPP` is $\phi''(1)$. The minimization in (2.7) is over Mathlib's `stdSimplex`. The paper's (2.4) also allows $p_i=0$; the mission takes every $p_i>0$, which covers the empirical distribution of distinct data points. The condition $\phi'(1)=0$ of (2.5) is not part of the assumption: it follows from it, since $1$ is an interior minimum.
-- source:
--   Gotoh, Kim & Lim, Calibration of Distributionally Robust Empirical Optimization Models, arXiv:1711.06565v2, pp. 7–8, (2.4), (2.7), (2.8), Assumption 2.1, variance on p. 7; p. 48, (F.5)

import Mathlib

namespace DROCalibration.Sensitivity

/-- The real-valued function `z ↦ φ(z)`, used for derivatives; it agrees with `φ` near `1`. -/
noncomputable def phiReal (φ : ℝ → EReal) : ℝ → ℝ := fun z => (φ z).toReal

/-- Assumption 2.1, p. 8: `φ : ℝ → ℝ ∪ {+∞}` is a closed (lower semicontinuous) convex function with
`φ(z) ≥ φ(1) = 0` for `z ≥ 0`, `φ(z) = +∞` for `z < 0`, twice continuously differentiable around
`z = 1` with `φ''(1) > 0`. Convexity is written pointwise because `EReal` is not a module. -/
structure Assumption21 (φ : ℝ → EReal) : Prop where
  lsc : LowerSemicontinuous φ
  convex : ∀ z w θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    φ (θ * z + (1 - θ) * w) ≤ ((θ : ℝ) : EReal) * φ z + ((1 - θ : ℝ) : EReal) * φ w
  nonneg : ∀ z : ℝ, 0 ≤ z → 0 ≤ φ z
  map_one : φ 1 = 0
  top_of_neg : ∀ z : ℝ, z < 0 → φ z = ⊤
  smooth : ∃ ε > 0, (∀ z ∈ Set.Ioo (1 - ε) (1 + ε), φ z ≠ ⊤) ∧
    ContDiffOn ℝ 2 (phiReal φ) (Set.Ioo (1 - ε) (1 + ε))
  pp_pos : 0 < deriv (deriv (phiReal φ)) 1

/-- `φ''(1)`. -/
noncomputable def phiPP (φ : ℝ → EReal) : ℝ := deriv (deriv (phiReal φ)) 1

/-- The objective of (2.7) for `δ > 0`: `Σ qᵢ fᵢ + (1/δ) Σ pᵢ φ(qᵢ/pᵢ)`, in `EReal`. -/
noncomputable def objective {n : ℕ} (φ : ℝ → EReal) (p f : Fin n → ℝ) (δ : ℝ) (q : Fin n → ℝ) :
    EReal :=
  ((∑ i, q i * f i : ℝ) : EReal) + ((δ⁻¹ : ℝ) : EReal) * ∑ i, ((p i : ℝ) : EReal) * φ (q i / p i)

/-- The arg min in (2.7): the probability vectors minimizing `objective φ p f δ` over the simplex. -/
def worstCaseSet {n : ℕ} (φ : ℝ → EReal) (p f : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin n) ∧
    ∀ q' ∈ stdSimplex ℝ (Fin n), objective φ p f δ q ≤ objective φ p f δ q'}

/-- The convex conjugate (F.5), p. 48: `φ*(ζ) = sup_z {ζ z − φ(z)}`, in `EReal`. -/
noncomputable def conj (φ : ℝ → EReal) (ζ : ℝ) : EReal := ⨆ z : ℝ, ((ζ * z : ℝ) : EReal) - φ z

/-- The real-valued conjugate `ζ ↦ φ*(ζ)`, used for derivatives. -/
noncomputable def conjReal (φ : ℝ → EReal) : ℝ → ℝ := fun ζ => (conj φ ζ).toReal

/-- `𝔼_{ℙₙ}[f] = Σ pᵢ fᵢ`. -/
def wMean {n : ℕ} (p f : Fin n → ℝ) : ℝ := ∑ i, p i * f i

/-- `𝕍_{ℙₙ}[f] = Σ pᵢ (fᵢ − 𝔼_{ℙₙ}[f])²`. -/
def wVar {n : ℕ} (p f : Fin n → ℝ) : ℝ := ∑ i, p i * (f i - wMean p f) ^ 2

end DROCalibration.Sensitivity


