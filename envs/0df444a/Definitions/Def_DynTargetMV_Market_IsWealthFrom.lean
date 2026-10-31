-- Prove2me | Definitions.Def_DynTargetMV_Market_IsWealthFrom
-- name    : DynTargetMV_Market_IsWealthFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:48.184954+00:00
-- url     : https://prove2.me/theorems/8300f4d5-99a9-4c71-ba77-3dc5ecc8735d
-- title:
--   $X$ solves the wealth equation (2.2) of $\pi$ from $(t,x)$
-- statement:
--   The process $X$ is a strong solution on $[t,T]$ of the wealth equation of the feedback strategy $\pi$ started from $X(t)=x$:
--   $$
--   dX(s)=\bigl(r(s)X(s)+b(s)^\top\pi(s,X(s))\bigr)ds+\pi(s,X(s))^\top\sigma(s)\,dW(s),\quad s\in[t,T].
--   $$
--   That is, $X$ is adapted with a.s. continuous paths, the portfolio has a.s. finite energy, and the equation holds in integral form a.s. for all $s$.
--
--   **Formalization Note** The Itô integral is the sum over $j$ of published `EntropyMFG.Enhanced.HasItoIntegral` integrals against $W_j$. The integrand is set to $0$ at the single time $T$, because a strategy is a function on $[0,T)$.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.2), (2.3), p.7

import Definitions.Def_DynTargetMV_sqNorm
import Definitions.Def_DynTargetMV_Market
import Definitions.Def_EntropyMFG_Enhanced_Stochastic

open MeasureTheory Set Matrix
open scoped BigOperators

namespace DynTargetMV

/-- `X` solves the wealth equation of the feedback strategy `π` on `[t,T]` started from `X(t) = x`:
`dX(s) = (r(s)X(s) + b(s)⊤π(s,X(s)))ds + π(s,X(s))⊤σ(s)dW(s)`, a strong solution on the given
filtered probability space. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.2), p.7 and (2.3), p.7.

**Formalization Note** The Itô integral `∫π⊤σ dW` is the sum over `j` of published
`EntropyMFG.Enhanced.HasItoIntegral` integrals of the `j`-th coordinate of `σ⊤π` against `W j`
(`EntropyMFG.Enhanced.StrongSolution` has one scalar driver). A strategy is a function on `[0,T)`
(p.7), so the integrand is set to `0` at the single time `T`; the value of the Lean function `π` at
`T` is irrelevant. The clause `energy` makes the drift integral meaningful; under Assumption 1 (ii) it
is implied by the a.s. finite energy of `σ⊤π` that any Itô integral needs. -/
structure Market.IsWealthFrom {m d n : ℕ} (M : Market m d n) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration ℝ mΩ) (W : Fin d → ℝ → Ω → ℝ)
    (π : ℝ → ℝ → Fin m → ℝ) (t x : ℝ) (X : ℝ → Ω → ℝ) : Prop where
  /-- `X` is adapted. -/
  adapted : ∀ s ∈ Icc t M.T, Measurable[F s] (X s)
  /-- `X` has a.s. continuous paths on `[t,T]`. -/
  continuous_paths : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Icc t M.T)
  /-- The portfolio has a.s. finite energy on `[t,T)`. -/
  energy : ∀ᵐ ω ∂P, IntegrableOn (fun z => sqNorm (π z (X z ω))) (Ico t M.T)
  /-- The wealth equation in integral form. -/
  equation : ∃ J : Fin d → ℝ → Ω → ℝ,
    (∀ j, EntropyMFG.Enhanced.HasItoIntegral P F (W j) t M.T
      (fun z ω => if z < M.T then ((M.σ z)ᵀ *ᵥ π z (X z ω)) j else 0) (J j)) ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t M.T,
      X s ω = x + (∫ z in t..s, (M.r z * X z ω + M.b z ⬝ᵥ π z (X z ω))) + ∑ j, J j s ω

end DynTargetMV


