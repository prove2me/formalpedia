-- Prove2me | Definitions.Def_RobustMultiStop_IsSensitive
-- name    : RobustMultiStop_IsSensitive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:25.7173+00:00
-- url     : https://prove2.me/theorems/cd31d97c-2ce2-4e4a-89b8-2775f410e535
-- title:
--   Sensitivity (P2) of a DMU
-- statement:
--   A DMU $\rho$ on $\mathfrak X$ with horizon $N$ is **sensitive** (P2) if, for all $X\in\mathfrak X$ and $t\le N$,
--
--   $$\big[X\le0\ \text{ and }\ \rho_t(X)\ge0\big]\ \Longrightarrow\ X=0 .$$
--
--   Sensitivity is what turns the dual representation (3.2) into the pathwise (almost sure) representation (3.3).
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.1, p.4, property (P2)

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- Sensitivity (P2), Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A
Pathwise Duality Approach*, arXiv:2006.01802v2, §2.1, p.4: `[X ≤ 0 and ρ_t(X) ≥ 0] ⟹ X = 0`, for
all `X ∈ 𝔛` and `t ∈ {0, …, T}`.

**Formalization Note** (In)equalities are `P`-a.s. (classes in `Ω →ₘ[P] ℝ`); `N` is the horizon. -/
def IsSensitive {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ)) (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ)) : Prop :=
  ∀ t ≤ N, ∀ X ∈ 𝔛, X ≤ 0 → 0 ≤ ρ t X → X = 0

end RobustMultiStop


