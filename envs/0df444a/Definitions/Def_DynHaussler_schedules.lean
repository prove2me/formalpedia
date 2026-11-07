-- Prove2me | Definitions.Def_DynHaussler_schedules
-- name    : DynHaussler_schedules
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:36.622198+00:00
-- url     : https://prove2.me/theorems/e745d20c-345d-4a79-8420-89b581a4fc2e
-- title:
--   The formal family of correction schedules of depth at most $r$ (Eq. (34))
-- statement:
--   A **correction schedule** of depth $i$ is a list
--   $$
--   J=\bigl((s_1,\sigma_1),\dots,(s_i,\sigma_i)\bigr),\qquad 1\le s_1\le\dots\le s_i\le m,\quad \sigma_j\in\{-,+\}.
--   $$
--   The empty list is the depth-zero schedule, and repeated ordinals are allowed. The **formal family** collects all schedules of depth at most $r$; it includes invalid schedules, schedules that are never born and schedules whose outputs coincide, and has exactly $Q_r(m)$ members.
--
--   **Formalization Note** A schedule is a list of pairs $(s,\sigma)\in\mathbb N\times$ `Bool` (`true` is $+$); "weakly increasing" is pairwise $\le$ on the list of ordinals.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (34), p.19 (PDF p.21); "The formal schedule family", p.20 (PDF p.22)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The **formal schedule family**: all correction schedules
`J = ((s_1, σ_1), …, (s_i, σ_i))` with `1 ≤ s_1 ≤ ⋯ ≤ s_i ≤ m`, `σ_j ∈ {−, +}`, of depth
`i ≤ r` (Eq. (34)); the empty list is the depth-zero schedule. Repeated ordinals are allowed.
The family includes invalid schedules, schedules that are never born, and schedules whose outputs
coincide.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (34), p.19 (PDF p.21), and "The formal schedule family", p.20 (PDF p.22).

**Formalization Note** A schedule is a `List (ℕ × Bool)`; the sign is `true` for `+` and `false`
for `−`; "weakly increasing" is `List.Pairwise (· ≤ ·)` on the list of ordinals. -/
def schedules (m r : ℕ) : Set (List (ℕ × Bool)) :=
  {J | J.length ≤ r ∧ (J.map Prod.fst).Pairwise (· ≤ ·) ∧ ∀ e ∈ J, 1 ≤ e.1 ∧ e.1 ≤ m}

end DynHaussler


