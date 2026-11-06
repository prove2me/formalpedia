-- Prove2me | Definitions.Def_ReserveLB_admissibleRes
-- name    : ReserveLB_admissibleRes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:05.755212+00:00
-- url     : https://prove2.me/theorems/bba9a68b-8598-4be8-95a0-10f052f01416
-- title:
--   Written reservation of at most $k$ distinct machines per job
-- statement:
--   A written reservation for $n$ jobs on $m$ machines with cap $k$ is **admissible** if it has exactly one entry per job and every entry is a nonempty list of machine indices in $\{0, \dots, m-1\}$ containing at most $k$ distinct indices.
--
--   This is the clause "reserves at most $k$ distinct original machines per job" of Theorem 1.1.
--
--   **Formalization Note** Repetitions inside an entry are harmless: only distinct indices count against $k$.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2; Section 4.3, p.9 (deduplicated original-parent set of size at most $k$)

import Mathlib

namespace ReserveLB

/-- **A written reservation of at most `k` distinct machines per job.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: "reserves at most k distinct original machines per job"; p.9: "its
virtual set and deduplicated original-parent set have size at most k under every construction
outcome".

`admissibleRes m n k res` says that `res` has one entry per job (`n` entries), and every entry is a
nonempty list of machine indices `< m` with at most `k` distinct values.

**Formalization Note.** A reservation is a list of 0-based machine indices; repetitions are
harmless, only distinct indices count against `k`. -/
def admissibleRes (m n k : ℕ) (res : List (List ℕ)) : Prop :=
  res.length = n ∧ ∀ l ∈ res, l ≠ [] ∧ (∀ i ∈ l, i < m) ∧ l.toFinset.card ≤ k

end ReserveLB


