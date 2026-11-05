-- Prove2me | Definitions.Def_PancakeHard_Hook
-- name    : PancakeHard_Hook
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:11.889751+00:00
-- url     : https://prove2.me/theorems/81bd6981-58f0-41d5-b84f-197d23f8e961
-- title:
--   Definition 3 — the hook gadget $Hook(p)=(take,put,G,H)$ with $G',H',G'',H''$
-- statement:
--   For an integer $p$, the **hook** gadget is $Hook(p)=(take,put,G,H)$ with
--   $$take=p+10,\quad put=p+7,\quad G=p+\langle 3,4\rangle,\quad H=p+\langle 12,11,6,5,9,8,2,1\rangle,$$
--   and the derived sequences
--   $$G'=p+\langle 12,11,6,5,4,3\rangle,\quad H'=p+\langle 10,9,8,2,1\rangle,\quad G''=p+\langle 3,4,5,6,7\rangle,\quad H''=p+\langle 12,11,10,9,8,2,1\rangle .$$
--
--   $G$ and $H$ delimit a sequence; $take$ brings the delimited sequence to the head and $put$ stores it back (Property 6).
--
--   **Formalization Note** The components are the separate values `hookTake`, `hookPut`, `hookG`, `hookH`, `hookG'`, `hookH'`, `hookG''`, `hookH''`; $p$ is a natural number.
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.3, p.7, Definition 3

import Mathlib
import Definitions.Def_PancakeHard_Basic

set_option autoImplicit false

namespace PancakeHard

/-- `take` of `Hook(p)` (Definition 3, arXiv:1111.0434v2, §3.1.3, p.7): `take = p + 10`. -/
def hookTake (p : ℕ) : ℕ := p + 10

/-- `put` of `Hook(p)` (Definition 3, p.7): `put = p + 7`. -/
def hookPut (p : ℕ) : ℕ := p + 7

/-- `G` of `Hook(p)` (Definition 3, p.7): `G = p + ⟨3, 4⟩`.

**Formalization Note** The paper's `Hook(p) = (take, put, G, H)` is
`(hookTake p, hookPut p, hookG p, hookH p)`; `p` is a natural number. -/
def hookG (p : ℕ) : List ℕ := shift p [3, 4]

/-- `H` of `Hook(p)` (Definition 3, p.7): `H = p + ⟨12, 11, 6, 5, 9, 8, 2, 1⟩`. -/
def hookH (p : ℕ) : List ℕ := shift p [12, 11, 6, 5, 9, 8, 2, 1]

/-- `G′` of `Hook(p)` (p.7): `G′ = p + ⟨12, 11, 6, 5, 4, 3⟩`. -/
def hookG' (p : ℕ) : List ℕ := shift p [12, 11, 6, 5, 4, 3]

/-- `H′` of `Hook(p)` (p.7): `H′ = p + ⟨10, 9, 8, 2, 1⟩`. -/
def hookH' (p : ℕ) : List ℕ := shift p [10, 9, 8, 2, 1]

/-- `G″` of `Hook(p)` (p.7): `G″ = p + ⟨3, 4, 5, 6, 7⟩`. -/
def hookG'' (p : ℕ) : List ℕ := shift p [3, 4, 5, 6, 7]

/-- `H″` of `Hook(p)` (p.7): `H″ = p + ⟨12, 11, 10, 9, 8, 2, 1⟩`. -/
def hookH'' (p : ℕ) : List ℕ := shift p [12, 11, 10, 9, 8, 2, 1]

end PancakeHard


