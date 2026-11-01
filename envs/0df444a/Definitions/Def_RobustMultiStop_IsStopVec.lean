-- Prove2me | Definitions.Def_RobustMultiStop_IsStopVec
-- name    : RobustMultiStop_IsStopVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:28.397337+00:00
-- url     : https://prove2.me/theorems/f053a2d2-cb5d-4379-b002-d957e25501ff
-- title:
--   Stopping vectors $t\le\tau_1<\dots<\tau_l\le N$ (almost surely ordered)
-- statement:
--   For a date $t$ and a number of rights $l$, a vector $(\tau_1,\dots,\tau_l)$ of $\mathbb N$-valued stopping times of $(\mathcal F_j)$ is a **stopping vector** from $t$ if, $P$-almost surely,
--
--   $$t\le\tau_1<\tau_2<\dots<\tau_l\le N .$$
--
--   These are the exercise strategies of a holder of $l$ rights that must be exercised at distinct dates (the family $\mathcal T_t(l)$ of p.5, in the almost-sure form used in the proof of Theorem 3.1).
--
--   **Formalization Note** The vector is indexed $0$-based by `Fin l`. Times are $\mathbb N$-valued and coerced to `WithTop ℕ` for Mathlib's `IsStoppingTime`. $N$ is the exercise horizon.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.2, p.5 (𝒯_t(L)), and proof of Theorem 3.1, p.40 ("t ≤ τ_1 < τ_2 < ⋯ < τ_L a.s.")

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- Stopping vectors, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A
Pathwise Duality Approach*, arXiv:2006.01802v2, §2.2, p.5: "`𝒯_t(L)` [is] the family of stopping
vectors `(τ_1, …, τ_L)` such that `τ_1 ≥ t` and `τ_l ≥ τ_{l−1} + 1` for all `l, 1 < l ≤ L`", in
the a.s. form used in the proof of Theorem 3.1, p.40 ("`t ≤ τ_1 < τ_2 < ⋯ < τ_L` a.s.").

`IsStopVec P F N t l τ`: each `τ k` is an `F`-stopping time and, `P`-a.s.,
`t ≤ τ 0 < τ 1 < ⋯ < τ (l-1) ≤ N`.

**Formalization Note** The vector is indexed `0`-based by `Fin l` (the paper's `τ_k` is `τ (k-1)`).
The times are `ℕ`-valued, coerced to `WithTop ℕ` for Mathlib's `IsStoppingTime`. `N` is the
exercise horizon: dates run in `{0, …, N}` (the paper's `{0, …, T}`, or `{0, …, T + L}` after the
paper's extension `H_j ≡ 0`, `F_j ≡ F_T` for `j > T`, p.6). -/
def IsStopVec {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (F : Filtration ℕ m0) (N t l : ℕ) (τ : Fin l → Ω → ℕ) : Prop :=
  (∀ k, IsStoppingTime F (fun ω => ((τ k ω : ℕ) : WithTop ℕ))) ∧
    ∀ᵐ ω ∂P, (∀ k, t ≤ τ k ω ∧ τ k ω ≤ N) ∧ StrictMono (fun k => τ k ω)

end RobustMultiStop


