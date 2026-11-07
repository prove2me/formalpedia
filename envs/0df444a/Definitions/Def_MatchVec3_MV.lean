-- Prove2me | Definitions.Def_MatchVec3_MV
-- name    : MatchVec3_MV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:30.279691+00:00
-- url     : https://prove2.me/theorems/4ff2ec42-e3aa-4fdc-9500-df4f3bb4a3d5
-- title:
--   $MV(m,n,r)$: the largest size of an $r$-restricted matching vector family
-- statement:
--   $MV(m,n,r)$ is the largest size $K$ of an $r$-restricted matching vector family in $\mathbb Z_m^n$.
--
--   The goal of the mission bounds $MV(m,n,3)$.
--
--   **Formalization Note** The largest size is an `sSup` on $\mathbb N$, whose junk value on an unbounded set is $0$. For $m\ge1$ the set contains $0$ and is bounded by $m^n$, since the $u_i$ of a family are distinct: $u_i=u_j$ with $i\ne j$ would give $\langle u_i,v_j\rangle=\langle u_j,v_j\rangle=0$. So $MV$ is a true maximum.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), §1.2, p.2

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_IsRestricted

namespace MatchVec3

/-- **`MV(m, n, r)`** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…), §1.2,
p.2): the largest size of an `r`-restricted matching vector family in `Z_m^n`.

**Formalization Note** The largest size is written as `sSup` on `ℕ`, whose junk value on an unbounded
set is `0`. For `m ≥ 1` the set contains `0` and is bounded by `m ^ n` (the `u_i` are distinct, since
`u_i = u_j` with `i ≠ j` gives `⟨u_i, v_j⟩ = ⟨u_j, v_j⟩ = 0`), so `MV` is a true maximum. -/
noncomputable def MV (m n r : ℕ) : ℕ :=
  sSup {K | ∃ U V : Fin K → Fin n → ZMod m, IsMVFamily U V ∧ IsRestricted r U V}

end MatchVec3


