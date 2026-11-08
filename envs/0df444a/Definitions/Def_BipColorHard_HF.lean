-- Prove2me | Definitions.Def_BipColorHard_HF
-- name    : BipColorHard_HF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:37.425206+00:00
-- url     : https://prove2.me/theorems/dc141bb6-33df-4f7d-9d92-d29c902f39f7
-- title:
--   The bipartite multigraph $H_F$ of a MAX-CUT instance
-- statement:
--   For a graph $F$, integers $\ell,s,t,L,M$, and the connector $K_L$, the bipartite multigraph $H_F$ is the following.
--
--   1. For each vertex $v$ of $F$: a left group $L_v$ and a right group $R_v$, each of size $\ell\deg_F(v)$, and reference vertices $a_v$ (left) and $b_v$ (right). The edge $\{a_v,b_v\}$, the edges from $a_v$ to $R_v$, from $L_v$ to $b_v$, and all edges between $L_v$ and $R_v$ each have multiplicity $M$.
--   2. For each edge $\{v,w\}$ of $F$: $\ell$ copies of $K_L$ with right terminal in $R_v$ and left terminal in $L_w$, and $\ell$ copies with right terminal in $R_w$ and left terminal in $L_v$, all with distinct terminals. Every copy uses as its reference vertices $a_x,b_x$ of the endpoint $x$ that comes first in the input order.
--   3. For each edge $\{v,w\}$: $t$ paths of length two from $a_v$ to $a_w$ and $t$ from $b_v$ to $b_w$, with distinct new middle vertices.
--
--   Its partition function encodes $\mathrm{MaxCut}(F)$ (Lemma 14).
--
--   **Formalization Note** The manuscript leaves the allocation of terminals free. Here a group vertex of $v$ is a pair of a dart $(v,w)$ and an index in $\{0,\dots,\ell-1\}$; copy $c$ of the connector for the dart $(v,w)$ has right terminal $((v,w),c)\in R_v$ and left terminal $((w,v),c)\in L_w$. So every group vertex is a terminal of exactly one copy, as the manuscript says.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), §4.1, p.15 (PDF p.17)

import Definitions.Def_NSWApxHard_Reduction_CubicVC
import Definitions.Def_BipColorHard_Connector

set_option autoImplicit false

namespace BipColorHard

open NSWApxHard.Reduction (GraphInput)

/-- Adjacency in an input graph is decidable classically. -/
noncomputable scoped instance (F : GraphInput) : DecidableRel F.G.Adj := Classical.decRel _

/-- Darts of an input graph have decidable equality, classically. -/
noncomputable scoped instance (F : GraphInput) : DecidableEq F.G.Dart := Classical.decEq _

/-- The edges `{v, w}` of `F`, each listed once with `v < w` in the input order. -/
abbrev EdgeIdx (F : GraphInput) : Type := {p : Fin F.N × Fin F.N // p.1 < p.2 ∧ F.G.Adj p.1 p.2}

/-- Left vertices of `H_F`, Galanis, Guo, He, Štefankovič, Vigoda, manuscript of Nov. 3, 2026 (sha256
78a66d1f…), §4.1, p.15 (PDF p.17): the reference vertices `a_v`; the left group vertices; the internal left
vertices of each connector copy; the middle vertices of the reference paths between `b_v`, `b_w`.

**Formalization Note.** The manuscript leaves the choice of terminals free ("all with distinct
terminals"). A left group vertex of `v` is `(d, c)` with `d` a dart out of `v` and `c : Fin ℓ`, so `L_v` has
`ℓ deg_F(v)` elements. -/
abbrev HFL (F : GraphInput) (ℓ s t : ℕ) : Type :=
  Fin F.N ⊕ (F.G.Dart × Fin ℓ) ⊕ (F.G.Dart × Fin ℓ × ConnLInt s) ⊕ (EdgeIdx F × Fin t)

/-- Right vertices of `H_F`, mirroring `HFL`: `b_v`, right group vertices, internal right vertices of each
connector copy, the middle vertices of the reference paths between `a_v`, `a_w`. -/
abbrev HFR (F : GraphInput) (ℓ s t : ℕ) : Type :=
  Fin F.N ⊕ (F.G.Dart × Fin ℓ) ⊕ (F.G.Dart × Fin ℓ × ConnRInt s) ⊕ (EdgeIdx F × Fin t)

/-- The vertices of `H_F` have decidable equality, classically. -/
noncomputable scoped instance (F : GraphInput) (ℓ s t : ℕ) : DecidableEq (HFL F ℓ s t) := Classical.decEq _

/-- The vertices of `H_F` have decidable equality, classically. -/
noncomputable scoped instance instDecEqHFR (F : GraphInput) (ℓ s t : ℕ) : DecidableEq (HFR F ℓ s t) := Classical.decEq _

variable {F : GraphInput} {ℓ s t : ℕ}

/-- The reference vertex `a_v`. -/
def aRef (v : Fin F.N) : HFL F ℓ s t := .inl v
/-- The reference vertex `b_v`. -/
def bRef (v : Fin F.N) : HFR F ℓ s t := .inl v
/-- The vertex `(d, c)` of the left group of `d.fst`. -/
def lGroup (d : F.G.Dart) (c : Fin ℓ) : HFL F ℓ s t := .inr (.inl (d, c))
/-- The vertex `(d, c)` of the right group of `d.fst`. -/
def rGroup (d : F.G.Dart) (c : Fin ℓ) : HFR F ℓ s t := .inr (.inl (d, c))

/-- The placement of copy `c` of the connector for the dart `d = (v, w)` on the left side: its left
terminal is a vertex of `L_w` and its left reference vertex is `a` of the endpoint first in the input
order (§4.1, p.15 (PDF p.17)). -/
def embL (d : F.G.Dart) (c : Fin ℓ) : ConnLV s → HFL F ℓ s t
  | .zL => lGroup d.symm c
  | .lRef => aRef (min d.fst d.snd)
  | .int x => .inr (.inr (.inl (d, c, x)))

/-- The placement of copy `c` of the connector for the dart `d = (v, w)` on the right side: its right
terminal is a vertex of `R_v` and its right reference vertex is `b` of the endpoint first in the input
order. -/
def embR (d : F.G.Dart) (c : Fin ℓ) : ConnRV s → HFR F ℓ s t
  | .zR => rGroup d c
  | .rRef => bRef (min d.fst d.snd)
  | .int x => .inr (.inr (.inl (d, c, x)))

variable (F ℓ s t)

/-- The edges of `H_F`, §4.1, p.15 (PDF p.17), each as (left end, right end), with multiplicity.
1. The sets `E_v`, all edges with multiplicity `M`: `{a_v, b_v}`; `a_v` to each vertex of `R_v`; each vertex
   of `L_v` to `b_v`; each vertex of `L_v` to each vertex of `R_v`.
2. For each dart `(v, w)` of `F` and each `c : Fin ℓ`, a copy of `K_L`: right terminal in `R_v`, left terminal
   in `L_w`. An edge `{v, w}` has two darts, so it receives `ℓ` copies in each direction.
3. For each edge `{v, w}`, `t` paths of length two from `a_v` to `a_w` and `t` from `b_v` to `b_w`, with
   distinct new middle vertices. -/
noncomputable def HFEdges (L M : ℕ) : Multiset (HFL F ℓ s t × HFR F ℓ s t) :=
  M • ((∑ v : Fin F.N, ({(aRef v, bRef v)} : Multiset _)) +
      (∑ d : F.G.Dart, ∑ c : Fin ℓ, ({(aRef d.fst, rGroup d c)} : Multiset _)) +
      (∑ d : F.G.Dart, ∑ c : Fin ℓ, ({(lGroup d c, bRef d.fst)} : Multiset _)) +
      (∑ d : F.G.Dart, ∑ c : Fin ℓ, ∑ d' : F.G.Dart, ∑ c' : Fin ℓ,
        if d.fst = d'.fst then ({(lGroup d c, rGroup d' c')} : Multiset _) else 0)) +
    (∑ d : F.G.Dart, ∑ c : Fin ℓ,
      L • ((connEdges s : Multiset (ConnLV s × ConnRV s)).map fun e => (embL d c e.1, embR d c e.2))) +
    (∑ e : EdgeIdx F, ∑ j : Fin t,
      (({(aRef e.1.1, .inr (.inr (.inr (e, j))))} : Multiset _) +
        {(aRef e.1.2, .inr (.inr (.inr (e, j))))} +
        {(.inr (.inr (.inr (e, j))), bRef e.1.1)} +
        {(.inr (.inr (.inr (e, j))), bRef e.1.2)}))

end BipColorHard


