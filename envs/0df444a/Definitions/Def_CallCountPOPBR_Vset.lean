-- Prove2me | Definitions.Def_CallCountPOPBR_Vset
-- name    : CallCountPOPBR_Vset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:06:26.482697+00:00
-- url     : https://prove2.me/theorems/e7884921-f048-45dc-97cd-5e0cf39cfc9f
-- title:
--   The vertex windows $V(F)$ touched by $F$
-- statement:
--   For a natural number $F$, a graph on $n$ vertices and a radius $R$,
--   $$
--   V(F)=\{\,w : F\text{ has a set bit in }[a_w-R,\,a_w]\,\}.
--   $$
--   In Claim 3, $R=4n^2$ and the vertex windows are pairwise disjoint.
--
--   **Formalization Note** Vertices of the published `NPGraph.Graph` are $0,\dots,n-1$; vertex $v$ stands for the paper's vertex $v+1$. The window uses truncated subtraction; in the reduction $a_w\ge s>R$, so no truncation occurs.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), proof of Theorem 2.8, Claim 3, p.6

import Definitions.Def_CallCountPOPBR_vexp

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The vertex windows touched by `F`** (Claim 3). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), proof of Theorem 2.8, Claim 3, p.6:
"For w ∈ V let V(F) = {w ∈ V : F has a set bit in [a_w − R, a_w]}".

`Vset n R F` is the set of vertices `w < n` such that `F` has a set bit at some position `b` with
`a_w − R ≤ b ≤ a_w`.

**Formalization Note.** Vertices are `0, …, n − 1` with `a_w = vexp n w`; the window is
`[a_w − R, a_w]` with truncated subtraction (in the reduction `R = 4n² < s ≤ a_w`, so no
truncation occurs). -/
def Vset (n R F : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun w =>
    ∃ b ∈ Finset.Icc (vexp n w - R) (vexp n w), F.testBit b = true

end CallCountPOPBR


