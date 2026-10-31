-- Prove2me | Definitions.Def_DynTargetMV_Market_Assumption1
-- name    : DynTargetMV_Market_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:31.581993+00:00
-- url     : https://prove2.me/theorems/ee922a4a-3012-4beb-8d17-5145c1421c8d
-- title:
--   Assumption 1 — $r,b,\sigma$ right-continuous and bounded; $b\neq0$; $\sigma\sigma^\top\succeq\delta I$
-- statement:
--   The standing assumption of the paper on the market: $r$, $b$ and $\sigma$ are right-continuous and bounded on $t\ge0$, and
--
--   1. $b(t)\neq 0$ for every $t\ge 0$;
--   2. there exists $\delta>0$ such that $\sigma(t)\sigma(t)^\top-\delta I$ is positive semi-definite for all $t\ge 0$.
--
--   The non-degeneracy conditions make $\rho(t)$ of (2.1) well defined and positive.
--
--   **Formalization Note** Right-continuity and boundedness are entrywise. The source says "$n$-dimensional identity"; the matrix $\sigma\sigma^\top$ is $m\times m$, so $I$ is the $m\times m$ identity.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 1, p.6

import Definitions.Def_DynTargetMV_Market

open Set Matrix

namespace DynTargetMV

/-- **Assumption 1.** `r`, `b`, `σ` are right-continuous and bounded on `t ≥ 0`; `b(t) ≠ 0` for every
`t ≥ 0`; and there is `δ > 0` with `σ(t)σ(t)⊤ − δI` positive semi-definite for every `t ≥ 0`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Assumption 1, p.6.

**Formalization Note** Right-continuity at `t` is `ContinuousWithinAt · (Ici t) t`, entry by entry;
boundedness is entrywise, which is equivalent to boundedness in any norm. The source writes "the
n-dimensional identity matrix"; `σσ⊤` is `m×m`, so `I` is the `m×m` identity. -/
structure Market.Assumption1 {m d n : ℕ} (M : Market m d n) : Prop where
  /-- `r` is right-continuous on `t ≥ 0`. -/
  r_rightCont : ∀ t, 0 ≤ t → ContinuousWithinAt M.r (Ici t) t
  /-- `b` is right-continuous on `t ≥ 0`. -/
  b_rightCont : ∀ t, 0 ≤ t → ∀ i, ContinuousWithinAt (fun s => M.b s i) (Ici t) t
  /-- `σ` is right-continuous on `t ≥ 0`. -/
  σ_rightCont : ∀ t, 0 ≤ t → ∀ i j, ContinuousWithinAt (fun s => M.σ s i j) (Ici t) t
  /-- `r` is bounded on `t ≥ 0`. -/
  r_bdd : ∃ K : ℝ, ∀ t, 0 ≤ t → |M.r t| ≤ K
  /-- `b` is bounded on `t ≥ 0`. -/
  b_bdd : ∃ K : ℝ, ∀ t, 0 ≤ t → ∀ i, |M.b t i| ≤ K
  /-- `σ` is bounded on `t ≥ 0`. -/
  σ_bdd : ∃ K : ℝ, ∀ t, 0 ≤ t → ∀ i j, |M.σ t i j| ≤ K
  /-- Non-degeneracy (i): `b(t) ≠ 0`. -/
  b_ne_zero : ∀ t, 0 ≤ t → M.b t ≠ 0
  /-- Non-degeneracy (ii): `σ(t)σ(t)⊤ − δI` is positive semi-definite. -/
  nondeg : ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 ≤ t →
    (M.σ t * (M.σ t)ᵀ - δ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef

end DynTargetMV


