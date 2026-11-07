-- Prove2me | Definitions.Def_MinrankTW_interiorRank
-- name    : MinrankTW_interiorRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:52.101348+00:00
-- url     : https://prove2.me/theorems/5a12544a-b60c-4806-9816-7be769f6d538
-- title:
--   Interior rank $\operatorname{rank} M_t[I_t,I_t]$
-- statement:
--   For a partial matrix $M$ and an interior consisting of the rows $I_r$ and columns $I_c$, the **interior rank** is the rank of the submatrix $M[I_r,I_c]$. The dynamic program records it alongside the linear relation, weighting each assignment by $z^{\operatorname{rank}M_t[I_t,I_t]}$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.2–3.3, pp.10–11, Eq. (14)

import Mathlib

namespace MinrankTW

/-- The **interior rank** `rank M_t[I_t, I_t]` of a partial matrix (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.2–3.3,
pp.10–11, Eq. (14)): the rank of the submatrix of `M` on the interior rows `I_r` and the
interior columns `I_c`. -/
noncomputable def interiorRank {F : Type*} [Field F] {m n : ℕ} (M : Matrix (Fin m) (Fin n) F)
    (Ir : Finset (Fin m)) (Ic : Finset (Fin n)) : ℕ :=
  (M.submatrix (fun i : Ir => (i : Fin m)) (fun j : Ic => (j : Fin n))).rank

end MinrankTW


