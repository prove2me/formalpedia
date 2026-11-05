-- Prove2me | Definitions.Def_OverlapRouting_tripMatrix
-- name    : OverlapRouting_tripMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:06.578509+00:00
-- url     : https://prove2.me/theorems/1989faaa-99a9-46be-bbe8-20aa053353db
-- title:
--   Lemma 7's chain: $p_d$, $P\in\mathbb R^{(Q+1)\times(Q+1)}$, $\pi$, $s^0$
-- statement:
--   Let $\bar D$ be the sum of $N'$ i.i.d. copies of $D$, with values in $\{0,\dots,U\}$, $U=N'u$, and pmf $p_d=\mathbb P[\bar D=d]$. For $m,n\in\{0,\dots,Q\}$ define
--   $$P_{mn}=\sum_{d=0}^{m}p_d\,\mathbb 1[n=0]+\sum_{d=m+1}^{U}p_d\,\mathbb 1\Big[\Big\lceil\frac{d-m}{Q}\Big\rceil Q+m-d=n\Big],\qquad \pi_m=\sum_{d=0}^{U}p_d\Big\lceil\frac{(d-m)^+}{Q}\Big\rceil,$$
--   and the row vector $s^0=[1,0,\dots,0]$. $P$ is the transition matrix of the excess capacity $e_j$ of display (3), and $\pi_m$ the expected trip count when the previous vehicle leaves excess $m$.
--
--   **Formalization Note** Indices are `Fin (Q + 1)`, the paper's size, although $e_j$ only takes the values $0,\dots,Q-1$.
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Appendix A, p.34 (p_d, U, Lemma 7's s⁰, P, π)

import Mathlib
import Definitions.Def_OverlapRouting_DemandLaw

namespace OverlapRouting

/-! The Markov-chain objects of Lemma 7 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022),
Appendix A, p.34). -/

/-- `p_d = ℙ[D̄ = d]`, the probability mass function of `D̄`, the total demand of a primary route,
i.e. the sum of `N′` i.i.d. copies of `D` (p.34). It vanishes for `d > U = N′u`. -/
noncomputable def groupPmf (N' : ℕ) (D : DemandLaw) (d : ℕ) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : Fin N' → Fin (D.u + 1) => ∑ i, ((v i : Fin (D.u + 1)) : ℕ) = d),
    D.prob v

/-- The transition matrix `P ∈ ℝ^{(Q+1)×(Q+1)}` of Lemma 7 (p.34), indices `m, n ∈ {0, …, Q}`:
`P_{mn} = ∑_{d=0}^{m} p_d 1[n = 0] + ∑_{d=m+1}^{U} p_d 1[⌈(d − m)/Q⌉Q + m − d = n]`, with
`U = N′u`.

**Formalization Note.** For `d > m` the natural number `⌈(d−m)/Q⌉·Q − (d − m)` equals
`⌈(d − m)/Q⌉Q + m − d`. The paper's size `Q + 1` is kept, although the excess `eⱼ` only takes the
values `0, …, Q − 1`. -/
noncomputable def tripMatrix (N' Q : ℕ) (D : DemandLaw) : Matrix (Fin (Q + 1)) (Fin (Q + 1)) ℝ :=
  fun m n =>
    (∑ d ∈ Finset.range ((m : ℕ) + 1), groupPmf N' D d * (if (n : ℕ) = 0 then 1 else 0)) +
    ∑ d ∈ Finset.Ioc (m : ℕ) (N' * D.u),
      groupPmf N' D d * (if ((d - m) ⌈/⌉ Q) * Q - (d - m) = (n : ℕ) then 1 else 0)

/-- The column vector `π ∈ ℝ^{Q+1}` of Lemma 7 (p.34): `π_m = ∑_{d=0}^{U} p_d ⌈(d − m)⁺/Q⌉`. -/
noncomputable def tripReward (N' Q : ℕ) (D : DemandLaw) : Fin (Q + 1) → ℝ :=
  fun m => ∑ d ∈ Finset.range (N' * D.u + 1), groupPmf N' D d * (((d - m) ⌈/⌉ Q : ℕ) : ℝ)

/-- The row vector `s⁰ = [1, 0, 0, …, 0] ∈ ℝ^{Q+1}` of Lemma 7 (p.34). -/
noncomputable def startVector (Q : ℕ) : Fin (Q + 1) → ℝ := Pi.single 0 1

end OverlapRouting


