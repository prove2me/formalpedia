-- Prove2me | Definitions.Def_RobustMultiStop_IsDMU
-- name    : RobustMultiStop_IsDMU
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:26.402745+00:00
-- url     : https://prove2.me/theorems/0d229f24-2999-4795-b666-108ec343ec5d
-- title:
--   Dynamic monetary utility functional (DMU): conditions (C1)–(C4)
-- statement:
--   Let $\mathfrak X$ be a space of positions on a filtered probability space with horizon $N$. A family $\rho=(\rho_t)_{t=0,\dots,N}$ of maps $\rho_t:\mathfrak X\to\mathfrak X\cap L^0(\Omega,\mathcal F_t,P)$ is a **dynamic monetary utility functional (DMU)** if for all $t\le N$ and $X,Y\in\mathfrak X$:
--
--   1. (C1) monotonicity: $X\le Y$ implies $\rho_t(X)\le\rho_t(Y)$;
--   2. (C2) regularity: $\rho_t(1_AX)=1_A\rho_t(X)$ for every $A\in\mathcal F_t$;
--   3. (C3) recursiveness: $\rho_t=\rho_t\circ\rho_{t+1}$ for $t<N$;
--   4. (C4) conditional translation invariance: $\rho_t(X+Y)=\rho_t(X)+Y$ whenever $Y$ is $\mathcal F_t$-measurable.
--
--   Robust (worst-case) conditional expectations, recursive coherent risk measures and $g$-expectations are DMUs; the paper's whole theory is built on these four axioms.
--
--   **Formalization Note** $\rho$ is a total map on $L^0$-classes; only its values at $t\le N$ on $\mathfrak X$ are constrained. Since (C2) evaluates $\rho_t$ at $1_AX$, the clause also records that $1_AX\in\mathfrak X$ for $A\in\mathcal F_t$, $X\in\mathfrak X$. Inequalities are almost sure.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.1, p.4, conditions (C1)–(C4)

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- A dynamic monetary utility functional (DMU), Laeven, Schoenmakers, Schweizer & Stadje,
*Robust Multiple Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, §2.1, p.4: a family
`ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P)`, `t ∈ {0, …, T}`, satisfying

* (C1) `ρ_t(X) ≤ ρ_t(Y)` for `X ≤ Y` (monotonicity);
* (C2) `ρ_t(1_A X) = 1_A ρ_t(X)` for `A ∈ F_t` (regularity);
* (C3) `ρ_t = ρ_t ∘ ρ_{t+1}` for `t ∈ {0, …, T − 1}` (recursiveness);
* (C4) `ρ_t(X + Y) = ρ_t(X) + Y` for `Y ∈ F_t` (conditional translation invariance).

**Formalization Note** `ρ` is a total map `ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)`; only its values at
`t ≤ N` on `𝔛` are constrained. "`∈ L⁰(Ω, F_t, P)`" means the class has an `F t`-measurable
representative. The product `1_A X` is any class a.e. equal to `A.indicator X`; (C2) evaluates `ρ_t`
at `1_A X`, so it presupposes `1_A X ∈ 𝔛`, which is part of the clause here. All (in)equalities are
`P`-a.s. (classes in `Ω →ₘ[P] ℝ`). `N` is the exercise horizon (the paper's `T`). -/
structure IsDMU {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ))
    (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)) : Prop where
  /-- `ρ_t : 𝔛 → 𝔛 ∩ L⁰(Ω, F_t, P)`. -/
  mapsTo : ∀ t ≤ N, ∀ X ∈ 𝔛, ρ t X ∈ 𝔛 ∧ AEStronglyMeasurable[F t] (ρ t X : Ω → ℝ) P
  /-- (C1) monotonicity. -/
  mono : ∀ t ≤ N, ∀ X ∈ 𝔛, ∀ Y ∈ 𝔛, X ≤ Y → ρ t X ≤ ρ t Y
  /-- (C2) regularity, with `1_A X ∈ 𝔛`. -/
  regular : ∀ t ≤ N, ∀ A : Set Ω, MeasurableSet[F t] A → ∀ X ∈ 𝔛, ∀ Z : Ω →ₘ[P] ℝ,
    (Z : Ω → ℝ) =ᵐ[P] A.indicator (X : Ω → ℝ) →
      Z ∈ 𝔛 ∧ (ρ t Z : Ω → ℝ) =ᵐ[P] A.indicator (ρ t X : Ω → ℝ)
  /-- (C3) recursiveness. -/
  recursive : ∀ t < N, ∀ X ∈ 𝔛, ρ t X = ρ t (ρ (t + 1) X)
  /-- (C4) conditional translation invariance. -/
  transl : ∀ t ≤ N, ∀ X ∈ 𝔛, ∀ Y ∈ 𝔛, AEStronglyMeasurable[F t] (Y : Ω → ℝ) P →
    ρ t (X + Y) = ρ t X + Y

end RobustMultiStop


