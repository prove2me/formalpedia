-- Prove2me | Definitions.Def_DRSub4633_nuInc
-- name    : DRSub4633_nuInc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:07:50.010204+00:00
-- url     : https://prove2.me/theorems/9443445d-db46-44cf-9afb-c1ca8ce1a1bd
-- title:
--   The increment vector $\nu_t$
-- statement:
--   Order the small coordinates $j_1,\dots,j_k$ nonincreasingly by $u_j$, ties broken by index, with prefixes $B_0=\varnothing$, $B_\iota=\{j_1,\dots,j_\iota\}$. Then
--   $$(\nu_t)_{j_\iota}=Q_t(\mathbf 1_{B_\iota})-Q_t(\mathbf 1_{B_{\iota-1}}).$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.11

import Mathlib
import Definitions.Def_DRSub4633_QFace

namespace DRSub4633

/-- **The increment vector `ν_t`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.11: "If `k = |S| > 0`, the
coordinates `j₁, . . . , j_k` are ordered nonincreasingly by `u_j`, with ties broken by index. Their
prefixes are `B₀ = ∅` and `B_ι = {j₁, . . . , j_ι}` … `(ν_t)_(j_ι) = Q_t(1_B_ι) − Q_t(1_B_(ι−1))`."

For a small coordinate `j`, `B_ι` with `j_ι = j` is the set of small `k` with `k ⪯ j`, where `k ≺ j`
means `u_k > u_j`, or `u_k = u_j` and `k < j`.

**Formalization Note.** The indicator vectors are functions on `Fin n`; `Q_t` reads only their small
coordinates, so the condition "`k` small" need not be written. The value at a large `j` is not
used. -/
noncomputable def nuInc {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (j : Fin n) : ℝ :=
  QFace f x t (fun k => if x j < x k ∨ (x k = x j ∧ k ≤ j) then 1 else 0) -
    QFace f x t (fun k => if x j < x k ∨ (x k = x j ∧ k < j) then 1 else 0)

end DRSub4633


