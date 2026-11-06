-- Prove2me | Definitions.Def_SpatialSorting_Coloring
-- name    : SpatialSorting_Coloring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:37.747998+00:00
-- url     : https://prove2.me/theorems/6f59ecb2-39f4-42dd-a831-fecd655b731c
-- title:
--   Configurations $\Omega_{D_L}$ with the wired collar
-- statement:
--   A configuration of the model assigns a colour in $\{0,1,\dots,q-1\}$ to every site of $D_L$ with $\sigma|_{B_L}\equiv0$. The set of all of them, with arbitrary interior counts, is $\Omega_{D_L}$. Since the collar is fixed, a configuration is determined by its values on the free sites $I_L$.
--
--   **Formalization Note** The type is the function type $I_L\to\{0,\dots,q-1\}$ (colours `Fin q`); a configuration is read on $D_L$, and on all of $\Lambda^\infty$, through its extension by $0$ (`extendBy 0 (I L)`), which is the paper's convention "always extended by $0$ to $\Lambda^\infty$" (p.19). The collar condition $\sigma|_{B_L}=0$ is therefore built into the type.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, Conventions for the scaffold factorization), p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SpatialSorting_I
open Classical Filter Topology

namespace SpatialSorting

/-- A configuration on `D_L` with `σ|_{B_L} = 0`, stored by its values on the free sites `I_L`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (§3, Conventions for the scaffold factorization), p. 19 (PDF p. 20). -/
abbrev Coloring (q L : ℕ) : Type := {v // v ∈ I L} → Fin q

end SpatialSorting


