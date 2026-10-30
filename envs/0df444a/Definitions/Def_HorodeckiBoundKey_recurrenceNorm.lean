-- Prove2me | Definitions.Def_HorodeckiBoundKey_recurrenceNorm
-- name    : HorodeckiBoundKey_recurrenceNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:18.128497+00:00
-- url     : https://prove2.me/theorems/c57988de-b594-4c79-9deb-1f0bf4f2edf4
-- title:
--   Normalization $N = 2p^n + 2(1/2-p)^n$ of (12)
-- statement:
--   For a real $p$ and $n\in\mathbb N$,
--   $$
--   N = 2p^n + 2\left(\tfrac12 - p\right)^n ,
--   $$
--   the normalization of the state $\rho'$ of (12): the probability that the recurrence step on $n$ copies of the state (11) succeeds (in the branch described by $J^\dagger$). For $0\le p\le \tfrac12$ it is positive, and it equals $1$ at $n=1$.
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3, after eq. (12) ("where N = 2p^n + 2(1/2 − p)^n")

import Mathlib

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3, after (12):
the normalization `N = 2pⁿ + 2(1/2 − p)ⁿ` of the state `ρ′` of (12), the probability of the
successful branch of the recurrence step on `n` copies of the state (11). -/
noncomputable def recurrenceNorm (p : ℝ) (n : ℕ) : ℝ := 2 * p ^ n + 2 * (1 / 2 - p) ^ n

end HorodeckiBoundKey


