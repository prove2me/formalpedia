-- Prove2me | Definitions.Def_SendSplit_Existence_Supplement_CircularIntervals
-- name    : SendSplit_Existence_Supplement_CircularIntervals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:46:01.439189+00:00
-- url     : https://prove2.me/theorems/7955a9e7-a431-49e9-a6f9-a81405b1a9d6
-- title:
--   Section 4 — circular subintervals, empty blocks and internal nodes
-- statement:
--   Let $D$ be a finite face set with a circular enumeration $o$. For vertices $a,b$ in $D$, let $d_o(a,b)$ count clockwise steps from $a$ to $b$, modulo $|D|$. The printed endpoint interval is
--   $$[a,b)_o=\begin{cases}D,&a=b,\\\{v\in D:d_o(a,v)<d_o(a,b)\},&a\ne b.\end{cases}$$
--   A circular block is either the empty set or one of these intervals. An internal node of a proper interval is neither its initial vertex nor its final included vertex (the predecessor of $b$). These definitions describe both separation conclusions in Theorem 3 in the original face order.
--
--   **Formalization Note** An enumeration has an arbitrary starting cut; geometric compatibility is specified separately. Equal endpoints always mean the whole face set. The distinguished empty block repairs the missing empty case of the printed convention, supported by the proof on p. 646 and the express empty-piece convention on p. 650. No division or modular distance is used on an inhabited endpoint type with empty $D$.
-- source:
--   Erickson, Monma and Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Mathematics of Operations Research 12(4) (1987), DOI 10.1287/moor.12.4.634, p. 646, Section 4, subinterval definition; p. 650, empty-piece convention (PDF 14, 18)

import Mathlib

set_option autoImplicit false

namespace SendSplit.Existence.Supplement

variable {n : ℕ}

/-- A cyclic enumeration, with an arbitrary starting cut. Geometry determines which
such enumerations are clockwise. A singleton has its unique enumeration. -/
structure CircularOrder (D : Finset (Fin n)) where
  enum : Fin D.card ≃ {v // v ∈ D}

/-- Clockwise distance in numbers of incidences. There are no values `a` or `b`
when `D` is empty, so the modulus cannot be zero on an instantiated call. -/
def circularDistance {D : Finset (Fin n)} (o : CircularOrder D)
    (a b : {v // v ∈ D}) : ℕ :=
  ((o.enum.symm b).val + D.card - (o.enum.symm a).val) % D.card

/-- The printed `[a,b)`: equal endpoints mean the entire face set. For unequal
endpoints the initial endpoint is included and the terminal endpoint is excluded. -/
noncomputable def circularInterval {D : Finset (Fin n)} (o : CircularOrder D)
    (a b : {v // v ∈ D}) : Finset (Fin n) := by
  classical
  exact D.attach.filter (fun v => a = b ∨ circularDistance o a v < circularDistance o a b)
    |>.image Subtype.val

/-- The distinguished empty block completes the printed nonempty intervals.
It does not change the convention `[a,a) = D`. -/
def IsCircularBlock {D : Finset (Fin n)} (o : CircularOrder D)
    (S : Finset (Fin n)) : Prop :=
  S = ∅ ∨ ∃ a b : {v // v ∈ D}, S = circularInterval o a b

/-- Neither end node of a proper interval: its end nodes are `a` and the
clockwise predecessor of `b`, rather than the excluded node `b`. -/
def IsInternal {D : Finset (Fin n)} (o : CircularOrder D)
    (a b i : {v // v ∈ D}) : Prop :=
  a ≠ b ∧ 0 < circularDistance o a i ∧
    circularDistance o a i + 1 < circularDistance o a b

end SendSplit.Existence.Supplement


