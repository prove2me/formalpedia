-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_welfare
-- name    : GSRandomOrder_Supplement_welfare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:06:07.003118+00:00
-- url     : https://prove2.me/theorems/e01af511-7c8e-4d4e-9db2-d14213bf4b44
-- title:
--   Optimal welfare $W(S)$ of $m$ bidders, eq. (2)
-- statement:
--   Let $N=\{1,\dots,n\}$ be the items and let bidders $1,\dots,m$ have valuations $v_i:2^N\to\mathbb R\cup\{-\infty\}$ with $v_i(\emptyset)=0$. For $S\subseteq N$ the **optimal welfare** of $S$ is
--   $$
--   W(S)=\max\Bigl\{\sum_{i=1}^m v_i(X_i)\ :\ X_1,\dots,X_m\subseteq S\ \text{pairwise disjoint}\Bigr\},
--   $$
--   and the welfare benchmark is $\mathrm{OPT}=W(N)$. Since the empty allocation is allowed, $W(S)\ge0$, so $W(S)$ is a real number.
--
--   This is the benchmark of the welfare problem, in which every arriving item is given to one bidder or discarded. With one bidder it is $\mathrm{OPT}(v)=\max_S v(S)$.
--
--   **Formalization Note** Bidders are `Fin m`, items `Fin n`, values `WithBot ℝ` with $\bot=-\infty$. The maximum is a `Finset.sup` over all allocations $X:$ `Fin m → Finset (Fin n)` with $X_i\subseteq S$ pairwise disjoint, read as a real with `unbotD 0` (never reached for valuations).
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §1, p.3, eq. (2); §4, p.11 (OPT = W(N))

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Optimal welfare** `W(S)` (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §1, p.3, eq. (2)): for bidders
`1, …, m` with valuations `v_i : 2^N → ℝ ∪ {−∞}`,
`W(S) = max { Σ_{i=1}^m v_i(X_i) : X_1, …, X_m ⊆ S pairwise disjoint }`, and `OPT = W(N)`.

**Formalization Note.** Bidders are `Fin m`, items `Fin n`, values in `WithBot ℝ` (`⊥ = −∞`).
An allocation is a function `X : Fin m → Finset (Fin n)`; the maximum is a `Finset.sup` in
`WithBot ℝ` over the finite set of allocations of `S` (every `X i ⊆ S`, the `X i` pairwise
disjoint), and a sum containing `−∞` is `−∞`. The result is read as a real number with
`unbotD 0`: for valuations (`v_i(∅) = 0`) the empty allocation shows that the maximum is at least
`0`, so the fallback is never used. With `m = 1` this is `GSRandomOrder.opt`. -/
noncomputable def welfare {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ)
    (S : Finset (Fin n)) : ℝ :=
  by classical exact
    (((Finset.univ : Finset (Fin m → Finset (Fin n))).filter
        (fun X => (∀ i, X i ⊆ S) ∧ Pairwise fun i j => Disjoint (X i) (X j))).sup
      (fun X => ∑ i, v i (X i))).unbotD 0

end GSRandomOrder.Supplement


