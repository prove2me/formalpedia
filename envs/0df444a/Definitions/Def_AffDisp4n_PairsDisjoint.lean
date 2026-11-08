-- Prove2me | Definitions.Def_AffDisp4n_PairsDisjoint
-- name    : AffDisp4n_PairsDisjoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:30.081995+00:00
-- url     : https://prove2.me/theorems/17e2ca0a-48ba-4f9c-ab66-d97d9052cfe0
-- title:
--   A set of disjoint pairs of parameters
-- statement:
--   A set $P$ of unordered pairs $\{p, r\}$ of parameters **consists of disjoint pairs** if every pair has two distinct members and no parameter belongs to two different pairs. A parameter in a pair is **paired**, the other member is its **partner**, and all other parameters are **unpaired**.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.2, p.13

import Mathlib

namespace AffDisp4n

/-- A set `P` of unordered pairs of parameters **consists of disjoint pairs** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.2, p.13: "a set P
which consists of disjoint pairs of parameters"): every pair has two distinct members, and two
different pairs share no member. -/
def PairsDisjoint {m : ℕ} (P : Finset (Sym2 (Fin m))) : Prop :=
  (∀ e ∈ P, ¬ e.IsDiag) ∧ ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → ∀ x : Fin m, x ∈ e → x ∉ e'

end AffDisp4n


