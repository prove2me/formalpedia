-- Prove2me | Definitions.Def_GenSort_TieRules
-- name    : GenSort_TieRules
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:45.315514+00:00
-- url     : https://prove2.me/theorems/841e5234-ad3a-4aaa-9a1e-b3a19372e3c5
-- title:
--   The arbitrary choices of an error isolation pass
-- statement:
--   A pass makes two arbitrary choices: how ties are broken when each right vertex selects its $t$ highest-score neighbours (a rule $Q$ depending on the current graph, the sample $S$ and the ordering $\tau$), and which ordering $\tau'$ is chosen among those whose candidate removal set misses the fewest validation edges (a rule $\tau_{\mathrm{sel}}$ depending on the current graph, $S$ and the validation edges).
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 4, p.8 and §3.5 step 3, p.10 (PDF pp.10, 12)

import Mathlib

namespace GenSort

/-- **The arbitrary choices of an error isolation pass**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 4, p.8 and §3.5 step 3,
p.10 (PDF pp.10, 12): `Q E S τ` is the selection of the `t` highest-score neighbours (ties broken
arbitrarily) for the current edge set `E`, sampled multiset `S` and ordering `τ`, and
`τsel E S val` is the ordering `τ'` chosen among those whose candidate removal set misses the
fewest validation edges `val`. Validity is `TieRules.Valid`. -/
structure TieRules (L R : Type*) (s : ℕ) where
  /-- The tie-breaking rule for the top-`t` selection. -/
  Q : Finset (L × R) → (Fin s → R) → Equiv.Perm (Fin s) → R → Finset L
  /-- The choice of a minimizing ordering `τ'`. -/
  τsel : Finset (L × R) → (Fin s → R) → List (L × R) → Equiv.Perm (Fin s)

end GenSort


