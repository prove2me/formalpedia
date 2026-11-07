-- Prove2me | Definitions.Def_LCPlanarSteiner_encPaths
-- name    : LCPlanarSteiner_encPaths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:44.020791+00:00
-- url     : https://prove2.me/theorems/1775dcaf-0982-46ea-821e-5315279f9fbd
-- title:
--   Binary encoding of a list of paths
-- statement:
--   A list of paths, each a list of arc indices, is encoded as its length followed by each path (its length, then its arc indices in binary), with words joined by the separator symbol.
--
--   This is the output format of the forest algorithm and of the rooted rounding algorithms.
--
--   **Formalization Note** Length-prefixed, hence injective.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Theorem 1.2, p.2; Lemma 3.8, p.8

import Mathlib
import Definitions.Def_EulerSparsify_joinW

namespace LCPlanarSteiner

/-- **Binary encoding of a list of arc-index paths.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Theorem 1.2, p.2: "a deterministic
algorithm returns original paths P_i : s_i ⇝ t_i"; Lemma 3.8, p.8: "returns a shared original union
and paths".

`encPaths ps` joins by the separator `3` the length of `ps` and, for each path, its length followed
by its arc indices in binary.

**Formalization Note.** Length-prefixed (published `EulerSparsify.tokNatList`), so injective
(`Solutions/verification/LCPlanarSteiner_sanity.lean`). -/
def encPaths (ps : List (List ℕ)) : List OnlineCRS.Combine.Sym :=
  EulerSparsify.joinW (ReserveLB.tokList EulerSparsify.tokNatList ps)

end LCPlanarSteiner


