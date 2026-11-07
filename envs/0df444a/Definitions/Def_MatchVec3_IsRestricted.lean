-- Prove2me | Definitions.Def_MatchVec3_IsRestricted
-- name    : MatchVec3_IsRestricted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:51.730002+00:00
-- url     : https://prove2.me/theorems/f47ed7a2-67ca-4323-b08e-3458411243ac
-- title:
--   $r$-restricted pair of lists
-- statement:
--   An ordered pair $(U,V)$ of lists in $\mathbb Z_m^n$ of length $K$ is **$r$-restricted** if all inner products $\langle u_i,v_j\rangle$, $i,j\in[K]$, including the diagonal values, take at most $r$ different values.
--
--   For a matching vector family with $K\ge1$ the diagonal value is $0$, so a 3-restricted family has at most two off-diagonal values. This is the class that 3-query matching-vector codes are built from.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), §1.2, p.2

import Mathlib

namespace MatchVec3

/-- **`r`-restricted** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…),
§1.2, p.2): all inner products `⟨u_i, v_j⟩`, including the diagonal value, take at most `r` different
values.

**Formalization Note** The pair `(i, j)` ranges over all of `Fin K × Fin K`, so the diagonal is
counted. For a matching vector family with `K ≥ 1` the diagonal value is `0`. -/
def IsRestricted {m n K : ℕ} (r : ℕ) (U V : Fin K → Fin n → ZMod m) : Prop :=
  (Finset.univ.image fun p : Fin K × Fin K => U p.1 ⬝ᵥ V p.2).card ≤ r

end MatchVec3


