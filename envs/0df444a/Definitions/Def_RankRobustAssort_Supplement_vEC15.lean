-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_vEC15
-- name    : RankRobustAssort_Supplement_vEC15
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:31:44.487662+00:00
-- url     : https://prove2.me/theorems/3633c024-0648-4773-ba75-bc1d56a5bf6a
-- title:
--   Historical data (EC.15) built from an assortment $\bar S$
-- statement:
--   Let the past assortments be the reverse revenue-ordered ones, $S_m=\{0,1,\dots,m-1,n\}$ for $m\in\mathcal M=\{1,\dots,n\}$, and let $\bar S\subseteq\mathcal N_0$. The historical sales data (EC.15) is, for $m\in\mathcal M$ and $i\in S_m$,
--
--   $$
--   v_{m,i}=\begin{cases}\tfrac1n\bigl(1+|\{m,\dots,n-1\}\setminus\bar S|\bigr), & i=n,\\[2pt] \tfrac1n\,|\{m,\dots,n-1\}\cap\bar S|, & i=0,\\[2pt] \tfrac1n, & \text{otherwise,}\end{cases}
--   $$
--
--   and $v_{m,i}=0$ for products $i\notin S_m$. On each $S_m$ the values sum to $\tfrac1n\bigl(1+(n-m)+(m-1)\bigr)=1$. It is the data with which the proof of Theorem 2 makes a given $\bar S\in\widehat{\mathcal S}$ the unique robust optimum.
--
--   **Formalization Note.** Past assortment $m$ has Lean index $m-1$; the product $n$ is the last element of $\{0,\dots,n\}$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Appendix E.2, (EC.15), p.ec27

import Mathlib
import Definitions.Def_RankRobustAssort_Supplement_revPast

namespace RankRobustAssort.Supplement

/-- The historical sales data (EC.15) built from an assortment `S̄`, for the reverse
revenue-ordered past assortments: for each past assortment `m ∈ ℳ = {1,…,n}` and `i ∈ S_m`,

`v_{m,i} ≜ (1/n)(1 + |{m,…,n−1} \ S̄|)` if `i = n`,
`v_{m,i} ≜ (1/n)|{m,…,n−1} ∩ S̄|` if `i = 0`,
`v_{m,i} ≜ 1/n` otherwise,

and `v_{m,i} = 0` for products `i ∉ S_m` (not offered, as for all data in §2).

Sturt, arXiv:2112.05010v4, Appendix E.2, (EC.15), p.ec27.

Formalization Note: past assortment `k : Fin n` is the paper's `m = k + 1`, so
`{m,…,n−1}` is the set of products `j` with `k + 1 ≤ j < n`; the product `n` is `Fin.last n`.
The cases are tested in the paper's order (`i = n` first). The value `0` off `S_m` is the
`Problem` convention `v_off`. -/
noncomputable def vEC15 (n : ℕ) (Sbar : Finset (Fin (n + 1))) : Fin n → Fin (n + 1) → ℝ :=
  fun k i =>
    if i ∈ revPast n k then
      if i = Fin.last n then
        (1 + ((Finset.univ.filter (fun j : Fin (n + 1) =>
            k.val + 1 ≤ j.val ∧ j.val < n ∧ j ∉ Sbar)).card : ℝ)) / n
      else if i = 0 then
        ((Finset.univ.filter (fun j : Fin (n + 1) =>
            k.val + 1 ≤ j.val ∧ j.val < n ∧ j ∈ Sbar)).card : ℝ) / n
      else 1 / n
    else 0

end RankRobustAssort.Supplement


