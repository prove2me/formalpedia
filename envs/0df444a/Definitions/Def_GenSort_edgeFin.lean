-- Prove2me | Definitions.Def_GenSort_edgeFin
-- name    : GenSort_edgeFin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:49.594197+00:00
-- url     : https://prove2.me/theorems/acc3c4af-161e-4c7f-bc6f-9f907753d875
-- title:
--   The edge set $E$ of $G$
-- statement:
--   The edge set $E$ of the comparison graph $G$, as a finite set of unordered pairs; $\mathrm{dist}_G = \mathrm{dist}_E$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6)

import Mathlib

namespace GenSort

/-- **The edge set `E` of `G` as a finite set**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6)
(`dist_G(π, P) = dist_E(π, P)`). -/
noncomputable def edgeFin {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) :=
  open Classical in Finset.univ.filter (· ∈ G.edgeSet)

end GenSort


