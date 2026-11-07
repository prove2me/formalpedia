-- Prove2me | Definitions.Def_GenSort_passesPMF
-- name    : GenSort_passesPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:33:17.661477+00:00
-- url     : https://prove2.me/theorems/d565f8c0-ae31-44ca-ae86-53bdf5d0e934
-- title:
--   $k$ successive error isolation passes
-- statement:
--   The random outcome of $k$ successive passes, each with fresh independent samples, each removing its selected set $C_{\tau'}$ from the current graph: the final edge set and the total number of queries.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.9, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_passPMF

namespace GenSort

/-- **`k` successive error isolation passes**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.9, p.11 (PDF p.13): "We apply the
single error isolation pass `log n` times, removing the selected edge removal set `C_τ'` from `H`
in each iteration." Each pass uses fresh independent samples. The result is the final edge set
and the total number of queries. -/
noncomputable def passesPMF {n : ℕ} {L R : Type*} [DecidableEq L] [DecidableEq R]
    (ℓ : L → Fin n) (r : R → Fin n) (π : Equiv.Perm (Fin n)) (d : ℕ)
    (ρ : TieRules L R (sPar n d)) : ℕ → Finset (L × R) → PMF (Finset (L × R) × ℕ)
  | 0, E => PMF.pure (E, 0)
  | k + 1, E => (passPMF E ℓ r π d ρ).bind fun o =>
      (passesPMF ℓ r π d ρ k o.1).map fun o' => (o'.1, o.2 + o'.2)

end GenSort


