-- Prove2me | Definitions.Def_GenSort_Prediction
-- name    : GenSort_Prediction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:24.991488+00:00
-- url     : https://prove2.me/theorems/352664b9-b294-43f1-9b7b-d0af269653e1
-- title:
--   Prediction function: one predicted orientation per edge
-- statement:
--   A **prediction function** $P$ for a graph $G$ maps every edge $\{u, v\}$ of $G$ to an orientation, $u \to v$ or $v \to u$.
--
--   **Formalization Note** A prediction is stored on darts: $P(u, v) = \text{true}$ means the edge is predicted to point from $u$ to $v$. The two darts of an edge carry opposite values, so this is exactly one orientation per edge.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6)

import Mathlib

namespace GenSort

/-- **A prediction function.** Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6): a prediction function maps
every edge `(u, v) ∈ E` to an orientation `u → v` or `v → u`.

**Formalization Note.** Encoded on darts: `orient d = true` means that the prediction orients
the edge of `d` from `d.fst` to `d.snd`. The field `orient_symm` makes the two darts of one edge
carry opposite values, so a prediction is exactly one orientation per edge. -/
structure Prediction {n : ℕ} (G : SimpleGraph (Fin n)) where
  /-- `orient d = true` iff the edge of `d` is predicted to point from `d.fst` to `d.snd`. -/
  orient : G.Dart → Bool
  /-- The two darts of an edge receive opposite orientations. -/
  orient_symm : ∀ d : G.Dart, orient d.symm = !orient d

end GenSort


