-- Prove2me | Definitions.Def_TIESharp_IsRApprox
-- name    : TIESharp_IsRApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:45.982692+00:00
-- url     : https://prove2.me/theorems/5cbbb04e-d332-4871-9c3b-cf2606256321
-- title:
--   $R$-approximation (2.2), uniform over all job counts
-- statement:
--   A family is **$R$-approximate** (has approximation ratio at most $R$) if at truthful bids
--   $$\sum_{A\in\mathcal A_{m,n}}y^m_A(t)\,C_{\max}(t,A)\ \le\ R\,\mathrm{OPT}(t)\tag{2.2}$$
--   for every job count $m\ge0$ and every profile $t\in[0,\infty)^{n\times m}$. When $\mathrm{OPT}(t)=0$ this requires zero makespan with probability one.
--
--   **Formalization Note.** $R$ is one real number, the same for every job count; profiles with $\mathrm{OPT}(t)=0$ are included.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, p.4, (2.2)

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_Family
import Definitions.Def_TIESharp_opt

set_option autoImplicit false

namespace TIESharp

/-- A family is **`R`-approximate**, (2.2) (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, §2, p.4): at truthful bids `b = t`,
`Σ_{A ∈ A_{m,n}} y^m_A(t) C_max(t, A) ≤ R · OPT(t)` for every job count `m ≥ 0` and every profile
`t`. "When OPT(t) = 0, this requires zero makespan with probability one."

**Formalization Note.** `R` is one real number, uniform over all job counts `m` (including
`m = 0`) and all nonnegative profiles; `OPT(t) = 0` profiles are included. `C_max` is the published
`MatousekLP.Scheduling.makespan` of `Matrix.of t`. -/
def IsRApprox {n : ℕ} (F : Family n) (R : ℝ) : Prop :=
  ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t →
    ∑ A, F.alloc m t A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ R * opt t

end TIESharp


