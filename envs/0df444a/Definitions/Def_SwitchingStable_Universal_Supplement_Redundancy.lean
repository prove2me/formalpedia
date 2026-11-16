-- Prove2me | Definitions.Def_SwitchingStable_Universal_Supplement_Redundancy
-- name    : SwitchingStable_Universal_Supplement_Redundancy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:36:09.873492+00:00
-- url     : https://prove2.me/theorems/103b2419-a9cc-48b7-852d-88c14f76ad40
-- title:
--   Appendix I — explicit enhanced and deleted certificate systems
-- statement:
--   Fix $d\ge2$ and $0\le q<d$. Use a distinguished coordinate $i$ of size $d$, and binary coordinates $a_s$ for $1\le s\le q$ and $b_s$ for $1\le s\le d-1-q$. For each $0\le t<d$, set
--
--   $$z^t_i=t,\qquad z^t_{a_s}=\mathbf1[t\ge q-s+1],\qquad z^t_{b_s}=\mathbf1[t<q+s],\qquad F=\{z^0,\ldots,z^{d-1}\}.$$
--
--   Only the witness sets of $z^q$ at $i$ are nonempty. The deleted system has $\{a_s\}$ at boundary $q-s+1$ and $\{b_s\}$ at boundary $q+s$. The enhanced system adds $a_{s-1}$ or $b_{s-1}$ for $s\ge2$. Adjacent boundaries retain their singleton sets. Every other object-coordinate-boundary triple has the empty witness set. These are raw systems; validity and equality of the resulting endpoints are proved by Theorem 4.
--
--   **Formalization Note** Coordinate $i$ has label zero, $a_s$ has label $s$, and $b_s$ has label $q+s$ in $\mathrm{Fin}\,d$. All domains except the distinguished domain are binary. This is a construction of an abstract finite system; it makes no matching-realizability claim.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 38, PDF p. 39, Appendix I, proof of Theorem 4

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Supplement_Certificate

namespace SwitchingStable.Universal.Supplement

/-- Coordinate 0 is distinguished; left coordinates have labels 1,…,q;
right coordinates have labels q+1,…,d-1. All nonzero coordinates are binary. -/
def redundantObject (d q t : ℕ) (i : Fin d) : ℕ :=
  if i.val = 0 then t
  else if i.val ≤ q then (if q - i.val + 1 ≤ t then 1 else 0)
  else (if t < i.val then 1 else 0)

/-- Enhanced and deleted systems differ only at nonadjacent boundaries of z^q at 0. -/
noncomputable def redundantSystem (d q : ℕ) (enhanced : Bool) : Certificate d where
  d i := if i.val = 0 then d else 2
  family := (Finset.range d).image fun t => redundantObject d q t
  witnesses z i j := by
    classical
    exact if z = redundantObject d q q ∧ i.val = 0 ∧ 1 ≤ j ∧ j < d then
      Finset.univ.filter fun p =>
        if j ≤ q then
          p.val = q - j + 1 ∨ (enhanced = true ∧ j < q ∧ p.val = q - j)
        else p.val = j ∨ (enhanced = true ∧ q + 1 < j ∧ p.val = j - 1)
    else ∅

end SwitchingStable.Universal.Supplement


