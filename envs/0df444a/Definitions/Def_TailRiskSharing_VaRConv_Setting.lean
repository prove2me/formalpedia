-- Prove2me | Definitions.Def_TailRiskSharing_VaRConv_Setting
-- name    : TailRiskSharing_VaRConv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:18:26.978314+00:00
-- url     : https://prove2.me/theorems/4f9e2910-6949-4ffe-9252-b04e810b7d61
-- title:
--   §2.1–2.3, pp. 5–7, and §3, p. 9 — atomless P, F_X, left/right VaR, allocations (4), inf-convolution (5), the allocation (9)
-- statement:
--   This file fixes the basic objects of §2.1–2.3 and §3 of Liu, Mao, Wang and Wei.
--
--   1. **Probability space.** $(\Omega,\mathcal F,\mathbb P)$ is a probability space. It is **atomless** if every measurable set $S$ with $\mathbb P(S)>0$ contains a measurable $T\subseteq S$ with $0<\mathbb P(T)<\mathbb P(S)$.
--   2. **Distribution function and VaRs.** For a random variable $X$, $F_X(x)=\mathbb P(X\le x)$. A positive value of $X$ is a loss, and for a level $\alpha$ (the "small $\alpha$" convention) the **left** and **right Value-at-Risk** are
--   $$\mathrm{VaR}^L_\alpha(X)=\inf\{x\in\mathbb R: F_X(x)\ge 1-\alpha\},\qquad \mathrm{VaR}^R_\alpha(X)=\inf\{x\in\mathbb R: F_X(x)> 1-\alpha\}.$$
--   For $\Lambda\in\{L,R\}$ we write $\mathrm{VaR}^\Lambda_\alpha$; for a family $\Lambda_1,\dots,\Lambda_n$ the **aggregated side** is $\Lambda=L$ if $\Lambda_1=\dots=\Lambda_n=L$ and $\Lambda=R$ otherwise (Theorem 1(i)).
--   3. **Domain.** $L^0$ is the set of all (measurable) random variables. The other objects take the domain $\mathcal X$ as a parameter.
--   4. **Allocations and inf-convolution.** The allocations of $X\in\mathcal X$ among $n$ agents are, display (4),
--   $$\mathbb A_n(X)=\Big\{(X_1,\dots,X_n)\in \mathcal X^n: \sum_{i=1}^n X_i=X\Big\},$$
--   and the **inf-convolution** of real-valued $\rho_1,\dots,\rho_n$ is, display (5),
--   $$\mathop{\square}_{i=1}^n\rho_i(X)=\inf\Big\{\sum_{i=1}^n\rho_i(X_i):(X_1,\dots,X_n)\in\mathbb A_n(X)\Big\}.$$
--   An allocation is **optimal** if it attains this infimum. For a functional $F$ with values in $[-\infty,\infty)$ (such as an inf-convolution of $n-1$ agents) and a real-valued $\rho$, $F\,\square\,\rho\,(X)=\inf\{F(Y)+\rho(Z): Y,Z\in\mathcal X,\ Y+Z=X\}$; this is the iterated inf-convolution of the proof of Theorem 1(i).
--   5. **The allocation (9).** A **partition** $(A_1,\dots,A_n)$ of $\Omega$ consists of measurable, pairwise disjoint sets whose union is $\Omega$ (some $A_i$ may be empty). For a real $v$,
--   $$X_i=(X-v)\mathbb 1_{A_i}+\frac1n v,\qquad i=1,\dots,n.$$
--
--   These objects are shared by every mission of the series.
--
--   **Formalization Note** Random variables are functions $\Omega\to\mathbb R$. The sum constraint of an allocation holds at every $\omega$. The inf-convolution is an infimum in `EReal`, so an empty or unbounded-below set of values gives $+\infty$ or $-\infty$, never a junk real number. The VaRs are real infima (`sInf` on $\mathbb R$): for $\alpha\in(0,1)$ and a probability measure both sets are nonempty and bounded below, so the infimum is the true one. At $\alpha=0$ or $\alpha=1$ the paper's value may be $\pm\infty$ and Lean returns $0$; every statement built on these definitions keeps its levels in $(0,1)$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 5–7, §2.1–2.3, (4)–(5), footnote 2; p. 9, §3, Theorem 1 and (9); p. 10, proof of Theorem 1(i)

import Mathlib

namespace TailRiskSharing.VaRConv

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.1 p. 5: atomless (classical sense; Mathlib's `NoAtoms` is only "singletons are null"). -/
def IsAtomless (P : Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < P s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < P t ∧ P t < P s

/-- §2.1 p. 5: distribution function `F_X(x) = P(X ≤ x)`. -/
noncomputable def distFn (P : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ℝ := P.real {ω | X ω ≤ x}

/-- §2.2 p. 6: left VaR, `VaR^L_α(X) = inf {x | F_X(x) ≥ 1 - α}` (small-α convention). -/
noncomputable def VaRL (P : Measure Ω) (α : ℝ) (X : Ω → ℝ) : ℝ := sInf {x | 1 - α ≤ distFn P X x}

/-- §2.2 p. 6: right VaR, `VaR^R_α(X) = inf {x | F_X(x) > 1 - α}`. -/
noncomputable def VaRR (P : Measure Ω) (α : ℝ) (X : Ω → ℝ) : ℝ := sInf {x | 1 - α < distFn P X x}

/-- §2.1 p. 5: the domain `L⁰` of all (measurable) random variables. -/
def L0 : Set (Ω → ℝ) := {X | Measurable X}

/-- (4), p. 7: the allocations `A_n(X)` of `X` (pointwise sum). -/
def Allocations (dom : Set (Ω → ℝ)) (n : ℕ) (X : Ω → ℝ) : Set (Fin n → Ω → ℝ) :=
  {Xs | (∀ i, Xs i ∈ dom) ∧ ∀ ω, ∑ i, Xs i ω = X ω}

/-- (5), p. 7: the inf-convolution `□ᵢ ρᵢ (X)`, valued in `[-∞, ∞]`. -/
noncomputable def infConv (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) :
    EReal :=
  ⨅ Xs ∈ Allocations dom n X, ((∑ i, ρ i (Xs i) : ℝ) : EReal)

/-- p. 7: `Xs` is an optimal allocation of `X` for `(ρ₁, …, ρₙ)`. -/
def IsOptimalAllocation (dom : Set (Ω → ℝ)) {n : ℕ} (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ)
    (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ Allocations dom n X ∧ ((∑ i, ρ i (Xs i) : ℝ) : EReal) = infConv dom ρ X

/-- (5), p. 7, for two agents of which the first may take the value `-∞` (footnote 2, p. 5):
`(F □ ρ)(X) = inf {F(Y) + ρ(Z) : Y, Z ∈ 𝒳, Y + Z = X}`. It is the iterated inf-convolution
`(ρ₁ □ ⋯ □ ρₙ₋₁) □ ρₙ` of the proof of Theorem 1(i), p. 10. Since `ρ` is real-valued, the sum
`F(Y) + ρ(Z)` never meets the undefined form `-∞ + ∞`. -/
noncomputable def infConv2E (dom : Set (Ω → ℝ)) (F : (Ω → ℝ) → EReal) (ρ : (Ω → ℝ) → ℝ)
    (X : Ω → ℝ) : EReal :=
  ⨅ YZ ∈ {YZ : (Ω → ℝ) × (Ω → ℝ) | YZ.1 ∈ dom ∧ YZ.2 ∈ dom ∧ ∀ ω, YZ.1 ω + YZ.2 ω = X ω},
    F YZ.1 + ((ρ YZ.2 : ℝ) : EReal)

/-- §3 p. 9: the two versions of VaR, `Λ ∈ {L, R}`. -/
inductive Side
  | L
  | R
  deriving DecidableEq

/-- §3 p. 9: `VaR^Λ_α` for `Λ ∈ {L, R}`. -/
noncomputable def VaRS (P : Measure Ω) : Side → ℝ → (Ω → ℝ) → ℝ
  | .L => VaRL P
  | .R => VaRR P

/-- Theorem 1(i), p. 9: `Λ = L` if `Λ₁ = ⋯ = Λₙ = L`, and `Λ = R` otherwise. -/
def aggSide {n : ℕ} (Λs : Fin n → Side) : Side :=
  if ∀ i, Λs i = Side.L then Side.L else Side.R

/-- Theorem 1(ii), p. 9: `(A₁, …, Aₙ)` is a (measurable) partition of `Ω`: measurable, pairwise
disjoint, with union `Ω`. Some `Aᵢ` may be empty. -/
def IsMeasPartition {n : ℕ} (A : Fin n → Set Ω) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧ (⋃ i, A i) = Set.univ

/-- (9), p. 9: the allocation `Xᵢ = (X - v) 1_{Aᵢ} + v / n`, `i = 1, …, n`, where `v` is meant to be
`VaR^Λ_α(X)`. -/
noncomputable def partitionAllocation {n : ℕ} (X : Ω → ℝ) (v : ℝ) (A : Fin n → Set Ω) :
    Fin n → Ω → ℝ :=
  fun i ω => (X ω - v) * (A i).indicator 1 ω + v / n

end TailRiskSharing.VaRConv


