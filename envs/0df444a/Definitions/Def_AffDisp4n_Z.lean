-- Prove2me | Definitions.Def_AffDisp4n_Z
-- name    : AffDisp4n_Z
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:33.650738+00:00
-- url     : https://prove2.me/theorems/53129176-4e00-4dbc-951f-40c472f72ea1
-- title:
--   The set $Z(P)$
-- statement:
--   For a set $P$ of disjoint pairs of parameters,
--   $$
--   Z(P) := \{\, u \in \mathbb F_2^m : p\, r = 0 \text{ for every } \{p, r\} \in P \,\},
--   $$
--   the parameter assignments in which at least one member of each pair is $0$. The invariant of gate elimination only requires the current circuit to agree with the original one on $Z(P)$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.2, p.13, display (2)

import Mathlib

namespace AffDisp4n

/-- The set **`Z(P)`** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), display (2), p.13): `Z(P) := {u ∈ 𝔽₂ᵐ : p r = 0 for every {p, r} ∈ P}`,
the parameter assignments in which at least one member of each pair of `P` is `0`. -/
def Z {m : ℕ} (P : Finset (Sym2 (Fin m))) : Set (Fin m → ZMod 2) :=
  {u | ∀ p r : Fin m, s(p, r) ∈ P → u p * u r = 0}

end AffDisp4n


