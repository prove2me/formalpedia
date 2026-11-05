-- Prove2me | Definitions.Def_PancakeHard_Lock
-- name    : PancakeHard_Lock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:12.626175+00:00
-- url     : https://prove2.me/theorems/fb9bca25-769f-4d05-8b0a-1bf961fd3d42
-- title:
--   Definition 2 — the lock gadget $Lock(p)=(key,test,L)$ and the open lock $L^o$
-- statement:
--   For an integer $p$, the **lock** gadget is $Lock(p)=(key,test,L)$ with
--   $$key=p+10,\qquad test=p+7,\qquad L=p+\langle 1,2,9,8,5,6,4,3,11,12\rangle,$$
--   and the **open lock** is $L^o=p+\langle 1,2,3,4,6,5,8,9,10,11,12\rangle$.
--
--   $L$ and $L^o$ represent the lock when it is closed and open. If a sequence containing a closed lock has $key$ at its head, efficient flips put the lock in open position; if it has $test$ at its head, it is a deadlock if and only if the lock is closed (Property 5). Locks emulate the literals of the formula in the reduction.
--
--   **Formalization Note** The triple is split into the four values `lockKey p`, `lockTest p`, `lockSeq p` ($L$) and `lockOpen p` ($L^o$); $p$ is a natural number.
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.1.2, p.5, Definition 2

import Mathlib
import Definitions.Def_PancakeHard_Basic

set_option autoImplicit false

namespace PancakeHard

/-- `key` of `Lock(p)` (Definition 2, arXiv:1111.0434v2, §3.1.2, p.5): `key = p + 10`. -/
def lockKey (p : ℕ) : ℕ := p + 10

/-- `test` of `Lock(p)` (Definition 2, p.5): `test = p + 7`. -/
def lockTest (p : ℕ) : ℕ := p + 7

/-- The closed lock `L` of `Lock(p)` (Definition 2, p.5): `L = p + ⟨1, 2, 9, 8, 5, 6, 4, 3, 11, 12⟩`.

**Formalization Note** The paper's `Lock(p) = (key, test, L)` is the triple
`(lockKey p, lockTest p, lockSeq p)`; `p` is a natural number (a stack has positive entries, so
`p + 1 ≥ 1` forces `p ≥ 0` anyway). -/
def lockSeq (p : ℕ) : List ℕ := shift p [1, 2, 9, 8, 5, 6, 4, 3, 11, 12]

/-- The open lock `Lᵒ` of `Lock(p)` (Definition 2, p.5):
`Lᵒ = p + ⟨1, 2, 3, 4, 6, 5, 8, 9, 10, 11, 12⟩`. -/
def lockOpen (p : ℕ) : List ℕ := shift p [1, 2, 3, 4, 6, 5, 8, 9, 10, 11, 12]

end PancakeHard


