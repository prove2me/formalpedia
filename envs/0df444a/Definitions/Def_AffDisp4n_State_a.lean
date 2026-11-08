-- Prove2me | Definitions.Def_AffDisp4n_State_a
-- name    : AffDisp4n_State_a
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:52.788748+00:00
-- url     : https://prove2.me/theorems/f1994368-28dd-4ed9-9b7f-48eb91173417
-- title:
--   The difference $a = m - q$
-- statement:
--   The quantity $a = m - q$ of a state, as an integer. Gate elimination runs while $a > d$: by Lemma 2.2, a simple output is constant on an affine subspace of dimension at least $a - 1$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.4, p.16

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_q

namespace AffDisp4n

/-- The **difference `a = m − q`** of a state (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.4, p.16), as an integer. -/
def State.a {n : ℕ} (σ : State n) : ℤ := (σ.m : ℤ) - σ.q

end AffDisp4n


