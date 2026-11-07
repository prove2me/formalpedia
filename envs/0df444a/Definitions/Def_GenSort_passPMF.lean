-- Prove2me | Definitions.Def_GenSort_passPMF
-- name    : GenSort_passPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:31:07.787255+00:00
-- url     : https://prove2.me/theorems/56598bef-5955-4d9f-bdcc-a514ef7fa3e7
-- title:
--   Distribution of one error isolation pass
-- statement:
--   The random outcome of one pass: the $M'$ sampled edges are drawn independently and uniformly from the current edge set, with replacement, and the pass of §3.5 is carried out on them. On an empty edge set nothing happens.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, pp.9–10 (PDF pp.11–12)

import Mathlib
import Definitions.Def_GenSort_passSamples
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_passOutcome

namespace GenSort

/-- **The distribution of one error isolation pass**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, pp.9–10 (PDF pp.11–12): the
`passSamples n d` edges are drawn independently and uniformly from the current edge set `E` (with
replacement), and `passOutcome` is applied. On an empty edge set nothing happens. -/
noncomputable def passPMF {n : ℕ} {L R : Type*} [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n) (π : Equiv.Perm (Fin n)) (d : ℕ)
    (ρ : TieRules L R (sPar n d)) : PMF (Finset (L × R) × ℕ) :=
  if h : E.Nonempty then
    haveI : Nonempty E := h.to_subtype
    (PMF.uniformOfFintype (Fin (passSamples n d) → E)).map (passOutcome E ℓ r π d ρ)
  else PMF.pure (E, 0)

end GenSort


