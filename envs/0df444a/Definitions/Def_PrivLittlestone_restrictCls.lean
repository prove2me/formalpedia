-- Prove2me | Definitions.Def_PrivLittlestone_restrictCls
-- name    : PrivLittlestone_restrictCls
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:36.747184+00:00
-- url     : https://prove2.me/theorems/0b0070f3-64e2-4dcb-b6e9-f483f544be6c
-- title:
--   Restricted class $H[h, A]$
-- statement:
--   For a binary function $h$ and a finite instance set $A$,
--   $$
--   H[h, A] = \{ f \in H : f(x) = h(x) \text{ for every } x \in A \}.
--   $$
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix A.2.1, p.17

import Mathlib

namespace PrivLittlestone

/-- The **restricted class** `H[h, A] = {f ∈ H : f(x) = h(x) for every x ∈ A}` (He–He, *Private
Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript
(sha256 21480556…c562), Appendix A.2.1, p.17), for a binary function `h` and a finite instance
set `A`. -/
def restrictCls {X : Type*} (H : Set (X → Bool)) (h : X → Bool) (A : Finset X) : Set (X → Bool) :=
  {f ∈ H | ∀ x ∈ A, f x = h x}

end PrivLittlestone


