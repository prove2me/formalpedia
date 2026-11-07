-- Prove2me | Definitions.Def_RobustQSC_canonPath
-- name    : RobustQSC_canonPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:35.886947+00:00
-- url     : https://prove2.me/theorems/718aa70d-9e4d-416f-8d93-1a33e537dbf1
-- title:
--   Canonical $i$-paths $P_i(u,v)$ in the hypercube
-- statement:
--   For $u,v\in\{0,1\}^n$ and $i\in[n]$, the $i$-th canonical path $P_i(u,v)$ is built as follows. Let $D=\{j:u_j\ne v_j\}$. Begin at $u$ and flip coordinate $i$. Scan rightward (cyclically) and flip each bit in $D$. If $i\notin D$, flip $i$ again at the end.
--
--   The paths for different $i$ are internally disjoint, which is what turns the membership of their internal vertices in a random set into independent events.
--
--   **Formalization Note** The path is the list of its vertices, from $u$ to $v$; the scan visits $i+1,\dots,i+n-1$ modulo $n$ and skips $i$, already flipped. `canonPathInternal` is the list without its first and last vertex.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Definition 2, p.48

import Definitions.Def_RobustQSC_fourier

namespace RobustQSC

open QAlgorithms

/-- The `i`-th canonical path `P_i(u, v)` from `u` to `v` in the hypercube, as its list of
vertices: let `D = {j : u_j ≠ v_j}`; begin at `u` and flip coordinate `i`; scan rightward
(cyclically, `i+1, i+2, …` mod `n`) and flip each bit of `D` (other than `i`, already flipped);
if `i ∉ D`, flip `i` again at the end.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), Definition 2, p.48 ("Canonical
i-paths, adapted from [HPS25]").

**Formalization Note.** The scan visits `(i + k) mod n` for `k = 1, …, n − 1`. The list starts
with `u` and ends with `v`; its internal vertices are `canonPathInternal`. -/
def canonPath {n : ℕ} (i : Fin n) (u v : Qubits n) : List (Qubits n) :=
  let scan : List (Fin n) :=
    ((List.range n).tail.map fun k => (⟨(i.val + k) % n, Nat.mod_lt _ i.pos⟩ : Fin n)).filter
      fun j => u j ≠ v j
  let flips : List (Fin n) := i :: scan ++ (if u i = v i then [i] else [])
  flips.scanl flip u

/-- The internal vertices of `P_i(u, v)`: the path without its first and last vertex. -/
def canonPathInternal {n : ℕ} (i : Fin n) (u v : Qubits n) : List (Qubits n) :=
  (canonPath i u v).tail.dropLast

/-! ### Sanity tests -/

/-- `n = 3`, `u = 000`, `v = 110`, `i = 2` (`i ∉ D`): flip 2, then 0 and 1, then 2 again. -/
example : canonPath (2 : Fin 3) ![false, false, false] ![true, true, false] =
    [![false, false, false], ![false, false, true], ![true, false, true], ![true, true, true],
      ![true, true, false]] := by decide

/-- `n = 4`, `u = 0000`, `v = 1011`, `i = 2` (`i ∈ D`): flip 2, then 3 and 0 (cyclic). -/
example : canonPath (2 : Fin 4) ![false, false, false, false] ![true, false, true, true] =
    [![false, false, false, false], ![false, false, true, false], ![false, false, true, true],
      ![true, false, true, true]] := by decide

/-- Fact 5 on an instance: for `u = 000`, `v = 011` the three paths have length at most
`d(u, v) + 2` and end at `v`. -/
example : ∀ i : Fin 3,
    (canonPath i ![false, false, false] ![false, true, true]).length ≤ 2 + 2 + 1 ∧
      (canonPath i ![false, false, false] ![false, true, true]).getLast? =
        some ![false, true, true] := by decide

end RobustQSC


