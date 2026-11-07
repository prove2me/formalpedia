-- Prove2me | Definitions.Def_GenSort_FlagGood
-- name    : GenSort_FlagGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:27.331208+00:00
-- url     : https://prove2.me/theorems/de6eb609-d649-4860-9339-4e42989fa3fa
-- title:
--   Good event of Claim 3.3 for the flagged vertices
-- statement:
--   For a set of flagged right vertices, the **good event of Claim 3.3** is:
--   1. every flagged $v \in R$ is incident to at least $\dfrac{d}{2^{24}\log^2 n}$ bad edges;
--   2. every unflagged $v \in R$ is incident to at most $\dfrac{4d}{2^{24}\log^2 n}$ bad edges.
--
--   It is assumed in Claims 3.4 and 3.10.
--
--   **Formalization Note** $\log = \log_2$; the page's "incident to most" is read as "incident to at most".
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.3, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_GenSort_badEdges

namespace GenSort

/-- **The good event of Claim 3.3**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.3, p.7 (PDF p.9), for a set `Fl` of flagged right
vertices: (1) every flagged `v ∈ R` is incident to at least `d / (2^24 log² n)` bad edges, and
(2) every unflagged `v ∈ R` is incident to at most `4d / (2^24 log² n)` bad edges.

**Formalization Note.** `log` is `log₂`; the page's "incident to most" is read as "incident to
at most". -/
def FlagGood {n : ℕ} {L R : Type*} (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n)
    (π : Equiv.Perm (Fin n)) (d : ℕ) (Fl : R → Prop) : Prop :=
  open Classical in
  ∀ v : R,
    (Fl v → (d : ℝ) / (2 ^ 24 * Real.logb 2 n ^ 2) ≤
      (((badEdges E ℓ r π).filter fun p => p.2 = v).card : ℝ)) ∧
    (¬ Fl v → (((badEdges E ℓ r π).filter fun p => p.2 = v).card : ℝ) ≤
      4 * d / (2 ^ 24 * Real.logb 2 n ^ 2))

end GenSort


