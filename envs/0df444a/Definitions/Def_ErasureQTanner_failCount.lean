-- Prove2me | Definitions.Def_ErasureQTanner_failCount
-- name    : ErasureQTanner_failCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:55.269481+00:00
-- url     : https://prove2.me/theorems/6d1f3683-29ed-45d2-8325-7a1210692137
-- title:
--   The counts $N_X,N_Z$ and the recovered vectors $u_X,u_Z$
-- statement:
--   For a vertex type and a local code $C$ on $A\times B$, the **failure count** is the number of vertices whose local erasure pattern covers a non-zero word of $C$: $N_X$ is this count for $V_{00}$ with $C=(C_A\otimes C_B)^\perp$, and $N_Z$ for $V_{01}$ with $C=(C_A^\perp\otimes D_B^\perp)^\perp$. The **recovered part** of a vector $e$ keeps $e$ on the squares whose view decodes and is $0$ on the others: it is $u_Z$ for $e_Z$ at $V_{00}$ and $u_X$ for $e_X$ at $V_{01}$.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), proof of Theorem 16, p.28

import Mathlib
import Definitions.Def_ErasureQTanner_LRData
import Definitions.Def_ErasureQTanner_covered

set_option autoImplicit false

namespace ErasureQTanner

variable {Δ : ℕ}

open Classical in
/-- `N_X`, `N_Z`: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript sha256 bf7a84a5…), proof of Theorem 16, p.28:
the vertices of type `t` whose local erasure pattern covers a non-zero word of the local code `C` (`C = (C_A ⊗ C_B)^⊥`,
`t = V00` for `N_X`; `C = (C_A^⊥ ⊗ D_B^⊥)^⊥`, `t = V01` for `N_Z`). -/
noncomputable def failCount (Γ : LRData Δ) (t : VType) (C : Submodule (ZMod 2) (Fin Δ × Fin Δ → ZMod 2))
    (x : Γ.Square → Bool) : ℕ :=
  (Finset.univ.filter fun h : Γ.G => decodeFails C (Γ.localVec t h x)).card

open Classical in
/-- The vectors `u_X`, `u_Z` (p.28): "identical to `e` on the coordinates … that we were able to recover and has zeroes
everywhere else": a square keeps its value exactly when its view of type `t` decodes. -/
noncomputable def recoveredPart (Γ : LRData Δ) (t : VType) (C : Submodule (ZMod 2) (Fin Δ × Fin Δ → ZMod 2))
    (x : Γ.Square → Bool) (e : Γ.Square → ZMod 2) : Γ.Square → ZMod 2 :=
  fun s => if decodeFails C (Γ.localVec t (Γ.vert t s) x) then 0 else e s

end ErasureQTanner


