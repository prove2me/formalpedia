-- Prove2me | Definitions.Def_NetworkSumSecure_Solvability_Supplement_path_starts
-- name    : NetworkSumSecure_Solvability_Supplement_path_starts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:07:55.270616+00:00
-- url     : https://prove2.me/theorems/f72c6c4f-a3ea-4d26-ac69-52ea3b5b264a
-- title:
--   Theorem 4 notation — users starting a path system
-- statement:
--   Let $N$ be the published finite directed acyclic multigraph network, with user index set $U$, and let $Q=(Q_1,\ldots,Q_n)$ be an indexed family of nonempty user-to-server paths. The starting-user set is
--
--   $$
--   S_Q=\{i\in U:\text{some path in }Q\text{ starts at }\sigma_i\}.
--   $$
--
--   It is the image of the map assigning each path its starting user, so repeated starting users contribute only once. For the edge-disjoint $(r+1)$-path families used in Theorem 4 this is exactly the paper's $S_Q$; equivalently, it contains the users with positive published path count. This definition supplies only the path-start set, with no maximality or feasibility certificate. Total private randomness is the ordinary finite sum $\sum_i z_i$ from Definition 2 and needs no new definition.
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 11, Theorem 4, notation S_Q (PDF p. 13); Definition 2, p. 9 (PDF p. 11).

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_network

namespace NetworkSumSecure.Solvability.Supplement

/-- Theorem 4, printed p.11 (PDF 13): the users at which the paths in Q start.
Indexing paths introduces no multiplicity in this finite set. -/
noncomputable def startSet {V E U : Type} {N : Network V E U} {n : ℕ}
    (Q : Fin n → UserPath N) : Finset U := by
  classical
  exact Finset.univ.image (fun j => (Q j).start)

end NetworkSumSecure.Solvability.Supplement


