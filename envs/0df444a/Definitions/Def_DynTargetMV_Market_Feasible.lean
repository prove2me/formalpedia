-- Prove2me | Definitions.Def_DynTargetMV_Market_Feasible
-- name    : DynTargetMV_Market_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:41.025216+00:00
-- url     : https://prove2.me/theorems/e12feb1c-baf2-4c7a-aff8-3da166eff373
-- title:
--   Feasible feedback strategy for the target $L$
-- statement:
--   A feedback strategy $\pi$, measurable on $[0,T)\times\mathbb R$, is feasible for the target $L$ if
--
--   1. the wealth equation from $(0,x_0)$ has a unique strong solution $X$, with $E[X(T)^2]<+\infty$;
--   2. $E\bigl[\int_0^T\|\pi(s,X(s))\|^2ds\bigr]<+\infty$;
--   3. all constraints of (2.3) are met for any $t\in[0,T)$: $E_t[X(T)]\ge L(t,X(t))$ and $Q\pi(s,X(s))\ge0$ for $s\in[t,T)$.
--
--   An equilibrium strategy is a feasible strategy, and this is the sense in which $\hat\pi$ itself is constrained.
--
--   **Formalization Note** $E_t$ along the path is conditional expectation given $\mathcal F_t$, and the target holds a.s. for each $t$. The portfolio constraint holds a.s. for all $s$ simultaneously.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.3), p.7

import Definitions.Def_DynTargetMV_Market_IsUniqueWealthFrom

open MeasureTheory Set Matrix

namespace DynTargetMV

/-- The feedback strategy `π` is **feasible** for the target `L`: `π` is measurable on `[0,T) × ℝ`, and
(i) the wealth equation from `(0, x₀)` has a unique strong solution `X` with `E[X(T)²] < +∞`;
(ii) `E[∫₀ᵀ ‖π(s,X(s))‖² ds] < +∞`; (iii) the constraints of (2.3) are met for any `t ∈ [0,T)`:
`E_t[X(T)] ≥ L(t,X(t))` and `Qπ(s,X(s)) ≥ 0`, `s ∈ [t,T)`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.7.

**Formalization Note** `E_t` along the agent's own path is `condExp` given `F t`, and the target
holds a.s. for each `t`. The portfolio constraint holds a.s. for all `s` simultaneously. The double
integral in (ii) is a `lintegral`, which has no junk value. -/
def Market.Feasible {m d n : ℕ} (M : Market m d n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ mΩ) (W : Fin d → ℝ → Ω → ℝ) (L : ℝ → ℝ → ℝ)
    (π : ℝ → ℝ → Fin m → ℝ) : Prop :=
  Measurable (fun p : Ico 0 M.T × ℝ => π p.1 p.2) ∧
  ∃ X : ℝ → Ω → ℝ, M.IsUniqueWealthFrom P F W π 0 M.x₀ X ∧
    MemLp (X M.T) 2 P ∧
    (∫⁻ ω, (∫⁻ s in Ico 0 M.T, ENNReal.ofReal (sqNorm (π s (X s ω)))) ∂P) ≠ ⊤ ∧
    (∀ t ∈ Ico 0 M.T, (fun ω => L t (X t ω)) ≤ᵐ[P] P[X M.T | F t]) ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Ico 0 M.T, 0 ≤ M.Q *ᵥ π s (X s ω)

end DynTargetMV


