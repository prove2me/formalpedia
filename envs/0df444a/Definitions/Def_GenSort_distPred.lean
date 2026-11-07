-- Prove2me | Definitions.Def_GenSort_distPred
-- name    : GenSort_distPred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:49.759594+00:00
-- url     : https://prove2.me/theorems/83a5846f-8acc-4cf7-a80f-6df941d776dc
-- title:
--   $\mathrm{dist}_F(\pi, P)$: wrong predictions on an edge set
-- statement:
--   For a total ordering $\pi$, a prediction function $P$ and a set $F$ of edges of $G$,
--   $$
--   \mathrm{dist}_F(\pi, P) = \sum_{e = (u,v) \in F} \mathbf 1\big[\mathbf 1[u \prec_\pi v] \ne \mathbf 1[P(e) = u \to v]\big],
--   $$
--   the number of edges of $F$ whose predicted orientation disagrees with $\pi$. One writes $\mathrm{dist}_G(\pi, P) = \mathrm{dist}_E(\pi, P)$.
--
--   **Formalization Note** Each unordered edge is counted once: it counts iff its dart pointing forward in $\pi$ is predicted backward. Pairs of $F$ that are not edges of $G$ never count; all uses assume $F \subseteq E$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_GenSort_Prediction

namespace GenSort

/-- **`dist_F(π, P)`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Definition 2.1, p.4 (PDF p.6):
`dist_F(π, P) = Σ_{e=(u,v)∈F} 1[1[u ≺_π v] ≠ 1[P(e) = u → v]]`, the number of edges of `F` whose
predicted orientation is wrong.

**Formalization Note.** Each unordered edge `e ∈ F` is counted once: it counts iff the dart
`d` of `e` pointing forward in `π` (`d.fst ≺_π d.snd`) is predicted backward
(`P.orient d = false`). Pairs of `F` that are not edges of `G` have no dart and never count; all
uses take `F ⊆ E(G)`. -/
noncomputable def distPred {n : ℕ} {G : SimpleGraph (Fin n)} (F : Finset (Sym2 (Fin n)))
    (π : Equiv.Perm (Fin n)) (P : Prediction G) : ℕ :=
  open Classical in
  (F.filter fun e =>
    ∃ d : G.Dart, d.edge = e ∧ π.symm d.fst < π.symm d.snd ∧ P.orient d = false).card

end GenSort


