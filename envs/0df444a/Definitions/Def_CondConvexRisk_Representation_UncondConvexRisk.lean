-- Prove2me | Definitions.Def_CondConvexRisk_Representation_UncondConvexRisk
-- name    : CondConvexRisk_Representation_UncondConvexRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:53:47.426016+00:00
-- url     : https://prove2.me/theorems/cb8db29b-e1e1-4f2a-b4e5-13203629a407
-- title:
--   Unconditional convex risk measure on $L^\infty$ and its minimal penalty $\alpha^*_0$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. A map $\rho_0:L^\infty\to\mathbb R$ is an (unconditional) **convex risk measure** if it is
--   1. monotone: $X\le Y$ $P$-a.s. implies $\rho_0(X)\ge\rho_0(Y)$;
--   2. cash invariant: $\rho_0(X+c)=\rho_0(X)-c$ for every constant $c\in\mathbb R$;
--   3. convex: $\rho_0(\lambda X+(1-\lambda)Y)\le\lambda\rho_0(X)+(1-\lambda)\rho_0(Y)$ for $\lambda\in[0,1]$.
--
--   It is **continuous from above** if $X_n,X\in L^\infty$, $X_n\searrow X$ $P$-a.s. imply $\rho_0(X_n)\nearrow\rho_0(X)$. Its **minimal penalty** at a probability measure $Q$ is
--   $$\alpha^*_0(Q)=\sup_{X\in L^\infty}\{-E_Q X-\rho_0(X)\}\in(-\infty,+\infty].$$
--
--   In the proof of Theorem 3.2 these objects are applied to $\rho_0(X)=E_P[\rho(X)]$.
--
--   **Formalization Note** $\rho_0$ acts on real functions and is required to be constant on $P$-a.s. classes of $L^\infty$; it is unconstrained outside $L^\infty$. No normalization $\rho_0(0)=0$ is imposed (Föllmer–Schied's class). $\alpha^*_0$ is a supremum of real numbers in `EReal`.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 5 (eq. (2)) and p. 7 (ρ0 and α*_0); [8] Föllmer–Schied, Stochastic Finance (2002), Definitions 4.1, 4.4

import Mathlib

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- Unconditional convex risk measure on `L∞(Ω, F, P)` (Section 3, p. 5; Föllmer–Schied,
*Stochastic Finance* (2002), Definitions 4.1 and 4.4): `ρ₀ : L∞ → ℝ` is well defined on
`P`-classes, monotone, cash invariant (`ρ₀(X + c) = ρ₀(X) - c` for constants `c`) and convex
(for scalar weights `λ ∈ [0, 1]`).  `ρ₀` is unconstrained outside `L∞`. -/
structure IsConvexRiskMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ₀ : (Ω → ℝ) → ℝ) : Prop where
  ae_congr : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X =ᵐ[P] Y → ρ₀ X = ρ₀ Y
  monotone : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X ≤ᵐ[P] Y → ρ₀ Y ≤ ρ₀ X
  cash : ∀ (X : Ω → ℝ) (c : ℝ), MemLp X ⊤ P → ρ₀ (X + fun _ => c) = ρ₀ X - c
  convex : ∀ (X Y : Ω → ℝ) (t : ℝ), MemLp X ⊤ P → MemLp Y ⊤ P → 0 ≤ t → t ≤ 1 →
    ρ₀ (t • X + (1 - t) • Y) ≤ t * ρ₀ X + (1 - t) * ρ₀ Y

/-- Continuity from above of an unconditional risk measure: `X_n, X ∈ L∞`, `X_n ↘ X` `P`-a.s.
implies `ρ₀(X_n) ↗ ρ₀(X)`. -/
def IsContinuousFromAbove₀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ₀ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (X : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ n, MemLp (X n) ⊤ P) → MemLp Y ⊤ P →
    (∀ᵐ ω ∂P, Antitone (fun n => X n ω) ∧ Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) →
    Monotone (fun n => ρ₀ (X n)) ∧ Tendsto (fun n => ρ₀ (X n)) atTop (𝓝 (ρ₀ Y))

/-- The minimal penalty of an unconditional risk measure (p. 7):
`α*₀(Q) = sup_{X ∈ L∞} {-E_Q X - ρ₀(X)} ∈ (-∞, +∞]`, a supremum of real numbers taken in
`EReal`. -/
noncomputable def minPenalty₀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ₀ : (Ω → ℝ) → ℝ) (Q : Measure Ω) : EReal :=
  ⨆ X : {X : Ω → ℝ // MemLp X ⊤ P}, ((-(∫ ω, X.1 ω ∂Q) - ρ₀ X.1 : ℝ) : EReal)

end CondConvexRisk.Representation


