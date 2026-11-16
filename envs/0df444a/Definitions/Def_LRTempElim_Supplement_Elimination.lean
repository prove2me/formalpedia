-- Prove2me | Definitions.Def_LRTempElim_Supplement_Elimination
-- name    : LRTempElim_Supplement_Elimination
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:36:38.335219+00:00
-- url     : https://prove2.me/theorems/c5a1f993-9926-4460-907c-6b41ce094fce
-- title:
--   Continuous elimination: time score $s^\star_t$, $M(t)$, $b(t)$, $A$, $m$, $\mathcal E$, the objective $J$ and its constrained infimum $F(\theta)$
-- statement:
--   Let $\rho$ be a reference measure on a space $\mathcal X$ and let $(P_t)_{t\in[0,1]}$ be a path of probability laws with densities $p_t$, $Q=P_0$ with density $q=p_0$ and $P=P_1$ with density $p=p_1$. The **time score** and the **absolute log-ratio** are
--   $$
--   s^\star_t(x)=\partial_t\log p_t(x),\qquad \ell^\star(x)=\log\frac{p(x)}{q(x)},
--   $$
--   and $C=\int_0^1\mathbb E_{P_t}[(s^\star_t)^2]\,dt$ is the path-score energy. For a feature map $\phi:\mathcal X\to\mathbb R^k$ put
--   $$
--   M(t)=\mathbb E_{P_t}[\phi\phi^\top],\qquad b(t)=\mathbb E_{P_t}[\phi\,s^\star_t],
--   $$
--   $$
--   A=\int_0^1M(t)^{-1}dt,\qquad m=\int_0^1M(t)^{-1}b(t)\,dt,\qquad \mathcal E=\int_0^1b(t)^\top M(t)^{-1}b(t)\,dt .
--   $$
--   For a head $\theta\in\mathbb R^k$, an **admissible velocity** is $u=a'$ for a path of coefficients $a$ with $a(0)=0$, $a(1)=\theta$: $u$ is integrable on $[0,1]$, $\int_0^1u\,dt=\theta$, and the energy $\int_0^1u^\top Mu\,dt$ is finite. The objective (3) is
--   $$
--   J(a)=\int_0^1\big[a'^\top M a'-2a'^\top b\big]\,dt,
--   $$
--   and $F(\theta)$ is its infimum over the admissible class. Finally, $\phi^\top c$ is the $L^2(P_t)$ **orthogonal projection** $\Pi_ts^\star_t$ of the time score onto $\mathrm{span}\{\phi_1,\dots,\phi_k\}$ when $s^\star_t-\phi^\top c\in L^2(P_t)$ and $\mathbb E_{P_t}[(s^\star_t-\phi^\top c)\phi_j]=0$ for every $j$; $\|s^\star_t-\Pi_ts^\star_t\|^2_{L^2(P_t)}$ is then $\mathbb E_{P_t}[(s^\star_t-\phi^\top c)^2]$.
--
--   These are the objects of Theorem 1, which eliminates the auxiliary temporal coefficients $a$ in closed form.
--
--   **Formalization Note** $\partial_t$ is Mathlib's `deriv` (value $0$ where the derivative does not exist). $b(t)$ is taken in the form $\mathbb E_{P_t}[\phi s^\star_t]$; the paper's equal form $\frac{d}{dt}\mathbb E_{P_t}[\phi]$ needs an interchange of limits that is not assumed. `Matrix.inv` is $0$ on a singular matrix; Theorem 1 assumes $M(t)$ positive definite for almost every $t$. $F(\theta)$ is the real `sInf` of the set of values of $J$; Theorem 1 proves this set has the stated greatest lower bound.
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §2.2 eq. (2), p.4 (pdf p.6); §3.1 eq. (3) and Theorem 1, p.5 (pdf p.7); §A.1.1, p.12 (pdf p.14)

import Mathlib

open MeasureTheory Matrix

namespace LRTempElim

namespace Supplement

/-!
# Continuous analytic elimination: the objects of Theorem 1

W. Chen, Y. Wu, J. Yang, D. Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…),
§2.2 eq. (2), p.4 (pdf p.6); §3.1 eq. (3) and Theorem 1, p.5 (pdf p.7); §A.1.1, p.12 (pdf p.14).

"Let P and Q have densities p and q on X ⊆ ℝᵈ with respect to a common reference measure. The
target is the absolute log-ratio ℓ⋆ = log(p/q) … The time score and its endpoint identity are
s⋆_t(x) = ∂_t log p_t(x), ∫₀¹ s⋆_t(x) dt = ℓ⋆(x). (2)" (p.4). "Write s⋆_t = ∂_t log p_t and assume
C = ∫₀¹ E_{P_t}[(s⋆_t)²] dt < ∞. … For fixed ζ, define M(t) = E_{P_t}[ϕϕ⊤] and
b(t) = d/dt E_{P_t}[ϕ] = E_{P_t}[ϕ s⋆_t] … Introduce H(x, t) = ϕ(x)⊤a(t), with a(0) = 0 and
a(1) = θ. … J(a) = ∫₀¹ [a′⊤Ma′ − 2a′⊤b] dt. (3) The endpoint constraint fixes the integral of a′
to the task head θ." "Define A = ∫₀¹ M(t)⁻¹ dt, m = ∫₀¹ M(t)⁻¹b(t) dt, and
E = ∫₀¹ b(t)⊤M(t)⁻¹b(t) dt" (p.5). "For fixed features, minimize (3) over derivatives u = a′
satisfying ∫₀¹ u dt = θ" (§A.1.1, p.12).

**Formalization Note.**
* The path is a family of densities `pt : ℝ → X → ℝ` with respect to a reference measure `ρ` on a
  measurable space `X` (the paper's `X ⊆ ℝᵈ`); `P_t = pt t · ρ`, `Q = P₀`, `P = P₁`. Only
  `t ∈ [0, 1]` matters.
* `timeScore pt t x = s⋆_t(x) = ∂_t log p_t(x)` is Mathlib's `deriv` in `t` (value `0` where the
  derivative does not exist, a null set of times for an absolutely continuous `t ↦ log p_t(x)`).
* `logRatio pt x = ℓ⋆(x) = log p₁(x) − log p₀(x) = log(p(x)/q(x))` on the common support.
* `b(t)` is the form `E_{P_t}[ϕ s⋆_t]`, not `d/dt E_{P_t}[ϕ]`: their equality is the paper's
  unpinned "differentiation and integration below are valid", which is not assumed.
* Matrix inverses are `Matrix.inv` (value `0` on a singular matrix; Theorem 1 assumes `M(t)` is
  positive definite for almost every `t`). Time integrals are interval integrals over `[0, 1]`.
* The admissible class of (3) is written through `u = a′`: `u` integrable on `[0, 1]` with
  `∫₀¹ u dt = θ` and finite energy `∫₀¹ u⊤Mu dt` (equivalently `a(t) = ∫₀ᵗ u` absolutely
  continuous with `a(0) = 0`, `a(1) = θ`). `reducedF θ` is the infimum of `J` over that class.
* `IsProjCoeff … t c` says that `ϕ⊤c` is the `L²(P_t)` orthogonal projection of `s⋆_t` onto
  `span{ϕ₁, …, ϕ_k}`: the residual is in `L²(P_t)` and orthogonal in `L²(P_t)` to every `ϕ_j`.
-/

variable {X : Type*} [MeasurableSpace X] {k : ℕ}

/-- The time score `s⋆_t(x) = ∂_t log p_t(x)` (eq. (2), p.4). -/
noncomputable def timeScore (pt : ℝ → X → ℝ) (t : ℝ) (x : X) : ℝ :=
  deriv (fun s => Real.log (pt s x)) t

/-- The absolute log-ratio `ℓ⋆(x) = log(p(x)/q(x)) = log p₁(x) − log p₀(x)` (§2.2, p.4). -/
noncomputable def logRatio (pt : ℝ → X → ℝ) (x : X) : ℝ :=
  Real.log (pt 1 x) - Real.log (pt 0 x)

/-- The path-score energy `C = ∫₀¹ E_{P_t}[(s⋆_t)²] dt` (§3.1, p.5). -/
noncomputable def scoreEnergy (ρ : Measure X) (pt : ℝ → X → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ x, pt t x * timeScore pt t x ^ 2 ∂ρ

/-- The feature moment matrix `M(t) = E_{P_t}[ϕϕ⊤]` (§3.1, p.5). -/
noncomputable def momentM (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) (t : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ x, pt t x * (ϕ x i * ϕ x j) ∂ρ

/-- The score–feature vector `b(t) = E_{P_t}[ϕ s⋆_t]` (§3.1, p.5). -/
noncomputable def scoreB (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) (t : ℝ) :
    Fin k → ℝ :=
  fun i => ∫ x, pt t x * (ϕ x i * timeScore pt t x) ∂ρ

/-- `A = ∫₀¹ M(t)⁻¹ dt` (Theorem 1, p.5). -/
noncomputable def elimA (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ t in (0 : ℝ)..1, (momentM ρ pt ϕ t)⁻¹ i j

/-- The continuous analytic readout `m = ∫₀¹ M(t)⁻¹b(t) dt` (Theorem 1, p.5). -/
noncomputable def elimM (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) : Fin k → ℝ :=
  fun i => ∫ t in (0 : ℝ)..1, ((momentM ρ pt ϕ t)⁻¹ *ᵥ scoreB ρ pt ϕ t) i

/-- `E = ∫₀¹ b(t)⊤M(t)⁻¹b(t) dt` (Theorem 1, p.5). -/
noncomputable def elimE (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, scoreB ρ pt ϕ t ⬝ᵥ ((momentM ρ pt ϕ t)⁻¹ *ᵥ scoreB ρ pt ϕ t)

/-- The admissible velocities `u = a′` for head `θ`: integrable on `[0, 1]`, `∫₀¹ u dt = θ`
(that is, `a(0) = 0` and `a(1) = θ`), and finite energy `∫₀¹ u⊤M u dt < ∞` (§3.1, p.5; §A.1.1). -/
def AdmissibleVel (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) (θ : Fin k → ℝ)
    (u : ℝ → Fin k → ℝ) : Prop :=
  IntervalIntegrable u MeasureTheory.volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, u t) = θ ∧
    IntervalIntegrable (fun t => u t ⬝ᵥ (momentM ρ pt ϕ t *ᵥ u t)) MeasureTheory.volume 0 1

/-- The objective (3), `J(a) = ∫₀¹ [a′⊤Ma′ − 2a′⊤b] dt`, written in terms of `u = a′`. -/
noncomputable def objJ (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ)
    (u : ℝ → Fin k → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (u t ⬝ᵥ (momentM ρ pt ϕ t *ᵥ u t) - 2 * (u t ⬝ᵥ scoreB ρ pt ϕ t))

/-- The set of values of (3) over the admissible class with head `θ`. -/
def objJValues (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) (θ : Fin k → ℝ) : Set ℝ :=
  objJ ρ pt ϕ '' {u | AdmissibleVel ρ pt ϕ θ u}

/-- The constrained infimum `F(θ) = inf {J(a) : a admissible, a(0) = 0, a(1) = θ}` (Theorem 1,
eq. (4)). Theorem 1 asserts the infimum exists as a greatest lower bound, so the real `sInf`
takes no junk value there. -/
noncomputable def reducedF (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ)
    (θ : Fin k → ℝ) : ℝ :=
  sInf (objJValues ρ pt ϕ θ)

/-- `ϕ⊤c` is the `L²(P_t)` orthogonal projection `Π_t s⋆_t` of the time score onto the feature
span: the residual `s⋆_t − ϕ⊤c` lies in `L²(P_t)` and is `L²(P_t)`-orthogonal to every
feature `ϕ_j` (Theorem 1, p.5). -/
def IsProjCoeff (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) (t : ℝ)
    (c : Fin k → ℝ) : Prop :=
  Integrable (fun x => pt t x * (timeScore pt t x - ϕ x ⬝ᵥ c) ^ 2) ρ ∧
    ∀ j, ∫ x, pt t x * ((timeScore pt t x - ϕ x ⬝ᵥ c) * ϕ x j) ∂ρ = 0

/-- The squared projection residual `∥s⋆_t − Π_t s⋆_t∥²_{L²(P_t)}` when `Π_t s⋆_t = ϕ⊤c`. -/
noncomputable def projResidualSq (ρ : Measure X) (pt : ℝ → X → ℝ) (ϕ : X → Fin k → ℝ) (t : ℝ)
    (c : Fin k → ℝ) : ℝ :=
  ∫ x, pt t x * (timeScore pt t x - ϕ x ⬝ᵥ c) ^ 2 ∂ρ

end Supplement

end LRTempElim


