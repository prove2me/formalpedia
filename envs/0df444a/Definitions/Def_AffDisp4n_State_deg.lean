-- Prove2me | Definitions.Def_AffDisp4n_State_deg
-- name    : AffDisp4n_State_deg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:56.775147+00:00
-- url     : https://prove2.me/theorems/1c762c4b-b332-4227-b137-5b42332dd912
-- title:
--   Degree of a parameter
-- statement:
--   The **degree** $\deg(x)$ of a parameter $x$ is its number of distinct children: the equations of the affine system that mention $x$ with a nonzero coefficient, plus the gates of the acyclic part that read $x$. A gate reading $x$ twice counts once. The degree is syntactic: an auxiliary variable that depends on $x$ only through the solution of the system does not count. A parameter is **unused** if its degree is $0$ and **isolated** if its degree is $1$.
--
--   **Formalization Note** The output designation is not a child.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.6, pp.17–18

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- The **degree `deg(x)` of a parameter** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.6, pp.17–18): its number of distinct children,
namely the equations that mention `x` (a nonzero entry in the column of `x` in `N`) plus the gates of
the acyclic part that read `x`. A gate reading `x` twice counts once. The degree is syntactic.

**Formalization Note** The output designation is not a child: a parameter whose only occurrence is as
the output literal has degree `0`. -/
noncomputable def State.deg {n : ℕ} (σ : State n) (x : Fin σ.m) : ℕ :=
  Nat.card {i : Fin σ.r // σ.N i x ≠ 0} + Nat.card {g : Fin σ.circ.size // σ.circ.Reads g (.inl x)}

end AffDisp4n


