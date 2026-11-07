-- Prove2me | Definitions.Def_GenSort_flagged
-- name    : GenSort_flagged
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:55.284924+00:00
-- url     : https://prove2.me/theorems/54017250-b88b-4a97-be13-343904fc1e8c
-- title:
--   Flagged right vertices
-- statement:
--   Given a sample $z$ of edges of $H$ drawn with replacement, a right vertex $v$ is **flagged** if at least $2^9 \log n$ sampled edges incident to $v$ are bad (sampled edges counted with multiplicity).
--
--   **Formalization Note** $\log = \log_2$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.3, p.6 (PDF p.8)

import Mathlib

namespace GenSort

/-- **Flagged right vertices**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.3, p.6 (PDF p.8): "We flag a vertex `v ∈ R` if at least
`2^9 log n` sampled edges incident to `v` are bad." `z` is the sample of `k` edges of `E`
(with replacement); sampled edges are counted with multiplicity.

**Formalization Note.** `log` is `log₂`. -/
noncomputable def flagged {n : ℕ} {L R : Type*} (E : Finset (L × R)) (ℓ : L → Fin n)
    (r : R → Fin n) (π : Equiv.Perm (Fin n)) (k : ℕ) (z : Fin k → E) (v : R) : Prop :=
  open Classical in
  (2 : ℝ) ^ 9 * Real.logb 2 n ≤
    ((Finset.univ.filter fun i =>
      (z i : L × R).2 = v ∧ π.symm (r (z i : L × R).2) < π.symm (ℓ (z i : L × R).1)).card : ℝ)

end GenSort


