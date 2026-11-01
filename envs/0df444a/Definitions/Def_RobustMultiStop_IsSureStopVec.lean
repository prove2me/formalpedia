-- Prove2me | Definitions.Def_RobustMultiStop_IsSureStopVec
-- name    : RobustMultiStop_IsSureStopVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:37.021898+00:00
-- url     : https://prove2.me/theorems/390a7c23-ee99-444f-a49c-61365788b024
-- title:
--   Surely ordered stopping vectors $t\le\tau_1<\dots<\tau_l\le N$
-- statement:
--   A vector $(\tau_1,\dots,\tau_l)$ of $\mathbb N$-valued stopping times is a **surely ordered stopping vector** from $t$ if
--
--   $$t\le\tau_1(\omega)<\tau_2(\omega)<\dots<\tau_l(\omega)\le N\qquad\text{for every }\omega\in\Omega .$$
--
--   This is the family $\mathcal T_t(l)$ of p.5 read pointwise; the mission shows that the optimum of (2.2) is attained in this smaller family.
--
--   **Formalization Note** $0$-based indexing by `Fin l`; times coerced to `WithTop ℕ` for `IsStoppingTime`.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, §2.2, p.5 ("𝒯_t(L) be the family of stopping vectors (τ_1, …, τ_L) such that τ_1 ≥ t and τ_l ≥ τ_{l−1} + 1")

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- Surely ordered stopping vectors, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple
Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, §2.2, p.5: the family `𝒯_t(L)` of
stopping vectors `(τ_1, …, τ_L)` with `τ_1 ≥ t` and `τ_l ≥ τ_{l−1} + 1`, here required for every
`ω` (not only almost surely), with values in `{t, …, N}`.

**Formalization Note** `0`-based indexing by `Fin l`; `ℕ`-valued times coerced to `WithTop ℕ` for
`IsStoppingTime`; `N` is the exercise horizon. -/
def IsSureStopVec {Ω : Type*} {m0 : MeasurableSpace Ω}
    (F : Filtration ℕ m0) (N t l : ℕ) (τ : Fin l → Ω → ℕ) : Prop :=
  (∀ k, IsStoppingTime F (fun ω => ((τ k ω : ℕ) : WithTop ℕ))) ∧
    ∀ ω, (∀ k, t ≤ τ k ω ∧ τ k ω ≤ N) ∧ StrictMono (fun k => τ k ω)

end RobustMultiStop


