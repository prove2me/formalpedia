-- Prove2me | Definitions.Def_RobustMultiStop_IsAdapted
-- name    : RobustMultiStop_IsAdapted
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:24.165884+00:00
-- url     : https://prove2.me/theorems/d5816c44-04c8-44fd-8e05-ca095cdb4453
-- title:
--   The class $\mathcal H$ of adapted processes in $\mathfrak X$
-- statement:
--   A process $U=(U_t)_{t=0,\dots,N}$ belongs to $\mathcal H$ if
--
--   $$U_t\in\mathfrak X\cap L^0(\Omega,\mathcal F_t,P)\qquad\text{for every }t\le N .$$
--
--   Rewards (cash flows) $H$, $\rho$-martingales and the Snell envelopes are all processes of this class.
--
--   **Formalization Note** A process is a sequence $\mathbb N\to L^0$; only the dates $0,\dots,N$ are constrained.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.1, p.5 ("Let ℋ be the set of adapted processes (U_t)_{t∈{0,…,T}} such that U_t ∈ 𝔛 ∩ L⁰(Ω, F_t, P)")

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- The class `ℋ` of adapted processes, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple
Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, §2.1, p.5: "Let ℋ be the set of adapted
processes `(U_t)_{t∈{0,…,T}}` such that `U_t ∈ 𝔛 ∩ L⁰(Ω, F_t, P)`."

**Formalization Note** A process is a sequence `U : ℕ → Ω →ₘ[P] ℝ`; only `U 0, …, U N` are
constrained (`N` is the horizon, the paper's `T`). -/
def IsAdapted {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (F : Filtration ℕ m0) (N : ℕ) (𝔛 : Submodule ℝ (Ω →ₘ[P] ℝ)) (U : ℕ → Ω →ₘ[P] ℝ) : Prop :=
  ∀ t ≤ N, U t ∈ 𝔛 ∧ AEStronglyMeasurable[F t] (U t : Ω → ℝ) P

end RobustMultiStop


