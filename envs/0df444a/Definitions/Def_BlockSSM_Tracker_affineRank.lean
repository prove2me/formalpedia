-- Prove2me | Definitions.Def_BlockSSM_Tracker_affineRank
-- name    : BlockSSM_Tracker_affineRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:17.460669+00:00
-- url     : https://prove2.me/theorems/c0fb7339-4050-4044-9c85-aada141714db
-- title:
--   Affine rank of a self-map of $V$
-- statement:
--   The **affine rank** of a map $F:V\to V$ is $\mathrm{rank}\,F=\dim F(V)$, the dimension of its image as an affine set. It is the quantity minimized over idempotents in the group extraction lemma.
--
--   **Formalization Note** The dimension is that of the span of the differences of points of $F(V)$ in $\mathbb C^n$. Since $V$ is nonempty and the elements of $M$ are affine, this is the dimension of the affine subspace $F(V)$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_wordRes

universe u

namespace BlockSSM

variable {G : Type u} {b : ℕ∞}

/-- **Affine rank.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4): "rank F = dim F(V)".

**Formalization Note.** The dimension of the affine set `F(V)` is the dimension of its direction, the
span of the differences of its points inside `ℂⁿ`: `Module.finrank` of the `vectorSpan` of the range.
This is a finite-dimensional space, so `finrank` has no junk value here. -/
noncomputable def Tracker.affineRank (T : Tracker G b) (F : Function.End T.hull) : ℕ :=
  Module.finrank ℂ (vectorSpan ℂ (Set.range fun x : T.hull => ((F x : T.hull) : State T.n)))

end BlockSSM


