-- Prove2me | Definitions.Def_ReserveLB_OPTk
-- name    : ReserveLB_OPTk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:08.735495+00:00
-- url     : https://prove2.me/theorems/9b3ce86c-d0fc-4581-b9fe-bb627a4238a7
-- title:
--   Same-budget benchmark $\mathrm{OPT}_k$
-- statement:
--   Let $m$ machines have speeds $s_1, \dots, s_m$, let the sizes $X_1, \dots, X_n$ be independent with listed laws, and let $k \ge 1$. The **same-budget optimum** is
--   $$
--   \mathrm{OPT}_k = \min_{\sigma}\ \mathbb E\, T_\sigma(X),
--   $$
--   over all reservations $\sigma$ that give every job a nonempty set $\sigma(j) \subseteq [m]$ of at most $k$ machines, fixed before the sizes are known.
--
--   Theorem 1.1 compares the algorithm with this benchmark: the comparator has the same per-job cap $k$ and recourses optimally after the sizes are revealed.
--
--   **Formalization Note** Machines are `Fin m`, jobs `Fin n`; the minimum is over a finite set that is nonempty when $m \ge 1$ and $k \ge 1$.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2 (definition of $\mathrm{OPT}_k$)

import Mathlib
import Definitions.Def_ReserveLB_prodExpect
import Definitions.Def_ReserveLB_Tsig

namespace ReserveLB

/-- **The same-budget benchmark `OPT_k`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "OPTk = min_(σ: |σ(j)|≤k) E Tσ(X)", over reservations with nonempty
`σ(j) ⊆ [m]`.

`OPTk k s law` is the minimum, over all reservations `σ` that give every job a nonempty set of at
most `k` machines, of the expected optimal whole-job cost `E T_σ(X)`, where the sizes are
independent with the listed laws.

**Formalization Note.** Machines are `Fin m`, jobs `Fin n`. The minimum is `Finset.inf'` over the
finite set of admissible reservations, which is nonempty when `m ≥ 1` and `k ≥ 1`; the value `0`
otherwise is never used. -/
noncomputable def OPTk {m n : ℕ} (k : ℕ) (s : Fin m → ℝ) (law : Fin n → List (ℚ × ℚ)) : ℝ :=
  if h : (Finset.univ.filter fun σ : Fin n → Finset (Fin m) =>
      ∀ j, (σ j).Nonempty ∧ (σ j).card ≤ k).Nonempty then
    (Finset.univ.filter fun σ : Fin n → Finset (Fin m) =>
      ∀ j, (σ j).Nonempty ∧ (σ j).card ≤ k).inf' h fun σ => prodExpect law (Tsig s σ)
  else 0

end ReserveLB


