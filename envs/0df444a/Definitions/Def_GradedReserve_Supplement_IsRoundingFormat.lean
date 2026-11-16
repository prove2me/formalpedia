-- Prove2me | Definitions.Def_GradedReserve_Supplement_IsRoundingFormat
-- name    : GradedReserve_Supplement_IsRoundingFormat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:49:34.692222+00:00
-- url     : https://prove2.me/theorems/5d010cfa-8cb3-48fb-9b47-9febfc07f11f
-- title:
--   The formats $S(\alpha,r)$, $\mathrm{LP}(d_\lambda,\lambda)$, $\mathrm{EF}((a-r)Q(a),r)$ of Theorem 6.1
-- statement:
--   The first three formats of Theorem 6.1, each with its lowest valid bid $t_0$, for an equilibrium with participation threshold $a$:
--
--   1. $S(\alpha,r)$ with $\alpha\in[0,1]$, $r\in[0,1)$, and $t_0=r$;
--   2. $\mathrm{LP}(d_\lambda,\lambda)$ with $\lambda\in[0,1]$, $a\in(0,1)$, $d_\lambda=aQ(a)/T_\lambda(a)$, and $t_0=d_\lambda$;
--   3. $\mathrm{EF}(e,r)$ with $0\le r\le a$, fee $e=(a-r)Q(a)\ge0$, and $t_0=r$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 6.1, p.11 (PDF 12); proof p.33 (PDF 34)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_Supplement_lpMinBid
import Definitions.Def_GradedReserve_Supplement_stdMech
import Definitions.Def_GradedReserve_Supplement_lpMech
import Definitions.Def_GradedReserve_Supplement_efMech
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The first three formats of Theorem 6.1 with their lowest valid bid `t₀` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 6.1,
p.11, PDF 12: "`S(α, r)`, … `LP(d_λ, λ)`, … `EF(e, r)` with `e = (a − r)Q(a)`"; proof p.33,
PDF 34): `M` is
1. a standard auction `S(α, r)` with `α ∈ [0, 1]`, `r ∈ [0, 1)` and `t₀ = r`; or
2. `LP(d_λ, λ)` with `λ ∈ [0, 1]`, `a ∈ (0, 1)`, `d_λ = aQ(a)/T_λ(a)` and `t₀ = d_λ`; or
3. `EF(e, r)` with `0 ≤ r ≤ a`, fee `e = (a − r)Q(a) ≥ 0` and `t₀ = r`,
where `a` is the participation threshold of the equilibrium considered. -/
def IsRoundingFormat (n : ℕ) (f : ℝ → ℝ) (a : ℝ) (M : Mechanism n) (t₀ : ℝ) : Prop :=
  (∃ α r : ℝ, α ∈ Icc (0:ℝ) 1 ∧ r ∈ Ico (0:ℝ) 1 ∧ M = stdMech n α r ∧ t₀ = r) ∨
  (∃ lam ∈ Icc (0:ℝ) 1, a ∈ Ioo (0:ℝ) 1 ∧ M = lpMech n (lpMinBid f n a lam) lam ∧
    t₀ = lpMinBid f n a lam) ∨
  (∃ r : ℝ, 0 ≤ r ∧ r ≤ a ∧ M = efMech n ((a - r) * oppCdf f n a) r ∧ t₀ = r)

end GradedReserve.Supplement


