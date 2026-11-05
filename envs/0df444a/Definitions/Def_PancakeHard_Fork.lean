-- Prove2me | Definitions.Def_PancakeHard_Fork
-- name    : PancakeHard_Fork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:23.865578+00:00
-- url     : https://prove2.me/theorems/d4034d0b-9f64-4c44-9e87-5c24baf73fa3
-- title:
--   Definition 4 — the fork gadget $Fork(p)=(E,F)$ with $F^1,F^2$
-- statement:
--   For an integer $p$, the **fork** gadget is $Fork(p)=(E,F)$ with
--   $$E=p+\langle 11,8,7,3\rangle,\qquad F=p+\langle 10,9,6,12,13,4,5,15,14,2,1\rangle,$$
--   and the derived sequences
--   $$F^1=p+\langle 10,9,6,7,8,11,12,13,14,15,5,4,3,2,1\rangle,\qquad F^2=p+\langle 3,7,8,11,10,9,6,12,13,4,5,15,14,2,1\rangle .$$
--
--   A fork implements a choice: an efficient path meeting $\langle E,X,F,Y\rangle$ continues with either $X$ or $\star X$ at the head (Property 7).
--
--   **Formalization Note** The components are the values `forkE`, `forkF`, `forkF1`, `forkF2`; $p$ is a natural number.
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.4, p.7, Definition 4

import Mathlib
import Definitions.Def_PancakeHard_Basic

set_option autoImplicit false

namespace PancakeHard

/-- `E` of `Fork(p)` (Definition 4, arXiv:1111.0434v2, §3.1.4, p.7): `E = p + ⟨11, 8, 7, 3⟩`.

**Formalization Note** The paper's `Fork(p) = (E, F)` is `(forkE p, forkF p)`; `p` is a natural
number. -/
def forkE (p : ℕ) : List ℕ := shift p [11, 8, 7, 3]

/-- `F` of `Fork(p)` (Definition 4, p.7): `F = p + ⟨10, 9, 6, 12, 13, 4, 5, 15, 14, 2, 1⟩`. -/
def forkF (p : ℕ) : List ℕ := shift p [10, 9, 6, 12, 13, 4, 5, 15, 14, 2, 1]

/-- `F¹` of `Fork(p)` (p.7): `F¹ = p + ⟨10, 9, 6, 7, 8, 11, 12, 13, 14, 15, 5, 4, 3, 2, 1⟩`. -/
def forkF1 (p : ℕ) : List ℕ := shift p [10, 9, 6, 7, 8, 11, 12, 13, 14, 15, 5, 4, 3, 2, 1]

/-- `F²` of `Fork(p)` (p.7): `F² = p + ⟨3, 7, 8, 11, 10, 9, 6, 12, 13, 4, 5, 15, 14, 2, 1⟩`. -/
def forkF2 (p : ℕ) : List ℕ := shift p [3, 7, 8, 11, 10, 9, 6, 12, 13, 4, 5, 15, 14, 2, 1]

end PancakeHard


