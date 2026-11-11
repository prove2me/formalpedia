-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_SurfaceWalls
-- name    : GMSTFramework_LocalStructure_SurfaceWalls
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:01:05.706983+00:00
-- url     : https://prove2.me/theorems/c632deea-77b4-407e-b7e5-7732fe818271
-- title:
--   Elementary segments, cylindrical closure, extended $n$-surface-walls, base cycles, simple cycle, vertical paths, nests of vortex-segments, pockets, the tangle of a surface-wall (§2.5)
-- statement:
--   For $n\ge2$ the **elementary $n$-wall-segment** is the $(n\times 8n)$-grid without the vertical edges $(i,j)(i+1,j)$, $i\not\equiv j\pmod 2$. Adding the edges $(1,2i)(1,6n+2-2i)$ and $(1,2n+2i)(1,8n+2-2i)$ ($i\in[n]$) gives a **handle-segment**; $(1,2i)(1,4n+2i)$ ($i\in[2n]$) a **crosscap-segment**; the skip edges $(1,2i)(1,4n+2q+2-2i)$ ($i\in[n]$) with a hyperedge $z_1\dots z_q$ and edges $(1,2n+2j)z_j$ a **flap-segment of arity $q\in[3]$**, whose **pocket** is the skip edge $(1,2n)(1,2n+2q+2)$ with the subpath of the first row between its ends; two wall-segments $W_0,W_1$ with their top boundary vertices $(1,2i)$ joined ($i\in[4n]$) and the rows of $W_1$ closed into cycles ($(j,1)(j,8n)$) a **vortex-segment**, whose **nest** is $C_1,\dots,C_n$ (rows $n,\dots,1$ of $W_1$; $C_1$ the inner cycle). The **cylindrical closure** joins $(j,8n)$ of $S_i$ to $(j,1)$ of $S_{i+1}$ cyclically. The **elementary extended $n$-surface-wall** with signature $(h,c,f,b)$ is the cylindrical closure of one wall-, $h$ handle-, $c$ crosscap-, $f$ flap- and $b$ vortex-segments in some cyclic order; an **extended $n$-surface-wall** is a subdivision of it. Its **base cycles** $C_1,\dots,C_n$ are the rows of the bases ($C_n$ the **simple cycle**); the **tangle** of the wall is that of its base wall.
--
--   **Formalization Note.** Rows and columns are 0-based. `SurfaceWall G n` embeds $D^-$ (the wall without hyperedges and the pendant vertices that then have degree 1) as a subdivision in $G$: an injective branch map and, for every elementary edge, a path between the images of its ends; paths of distinct edges meet only in branch vertices of common ends. The hyperedge of flap-segment $i$ is a set `zs i` of $q$ further vertices of $G$, disjoint from $V(D^-)$ and from the other flap-segments' (p. 24: "$D\subseteq G$ implicitly means $D^-\subseteq G$"; the pendant paths to the base are not required in $G$). `tangle` consists of the separations of order $<n$ whose big side contains a base cycle and a vertical path of the base wall (the cylindrical-mesh tangle of p. 21 for the base wall).
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 21–24 (PDF 24–27), §2.5

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Graphs

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# Extended surface-walls

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), §2.5 p. 21–24
(PDF 24–27).

The elementary `n`-segments (`n ≥ 2`) live on `[n] × [8n]` (a vortex-segment on two copies
`W₀`, `W₁`). Here rows and columns are `0`-based: the paper's vertex `(i, j)` is
`row = i - 1`, `col = j - 1`.

* Wall-segment `W₀`: the `(n × 8n)`-grid minus the vertical edges `(i,j)(i+1,j)` with
  `i ≢ j (mod 2)`.
* Handle edges `(1,2i)(1,6n+2-2i)`, `(1,2n+2i)(1,8n+2-2i)` (`i ∈ [n]`); crosscap edges
  `(1,2i)(1,4n+2i)` (`i ∈ [2n]`); skip edges of a flap-segment of arity `q ∈ [3]`
  `(1,2i)(1,4n+2q+2-2i)` (`i ∈ [n]`); a vortex-segment joins the `i`-th top boundary vertex
  `(1,2i)` of `W₀` to that of `W₁` (`i ∈ [4n]`) and the `j`-th left boundary vertex `(j,1)` of
  `W₁` to its `j`-th right boundary vertex `(j,8n)` (`j ∈ [n]`).
* The cylindrical closure of `S₁, …, S_ℓ` joins `(j, 8n)` of the base of `Sᵢ` to `(j, 1)` of the
  base of `S_{i+1}` (indices mod `ℓ`).
* The elementary extended `n`-surface-wall with signature `(h, c, f, b)`: the cylindrical closure of
  one wall-, `h` handle-, `c` crosscap-, `f` flap- and `b` vortex-segments in some cyclic order
  (`kinds`).
* `SurfaceWall G n`: an extended `n`-surface-wall `D` in `G`. Following p. 24 ("`D ⊆ G` implicitly
  means `D⁻ ⊆ G`"), `D⁻` (`D` without its hyperedges and, iteratively, the degree-1 vertices that
  arise, i.e. without the hyperedge ends `z_j` and their pendant edges) is a subdivision of the
  elementary graph without the `z_j`, embedded in `G`: an injective branch map `ι` and, for every
  elementary edge `xy`, a path of `G` from `ι x` to `ι y`; distinct such paths meet only in the
  branch vertices of common ends and contain no other branch vertex. The hyperedge of the flap-segment
  `i` (arity `q`) is the set `zs i` of `q` further vertices of `G`, distinct from `V(D⁻)` and from
  the other flap-segments' (its pendant paths to the base need not lie in `G`; nothing uses them).
* Derived subgraphs: the base cycles `C₁, …, Cₙ` of the base wall (`C₁` through the top boundary,
  `Cₙ` the simple cycle), the vertical paths of a segment's base (the subgraph induced by columns
  `2j - 1, 2j`), the nest `C₁, …, Cₙ` of a vortex-segment (rows `n, …, 1` of `W₁`; `C₁` the inner
  cycle), and the pocket of a flap-segment (the skip edge `(1,2n)(1,2n+2q+2)` with the subpath of the
  first row between its ends).
* `tangle D`: the tangle induced by `D`, i.e. by its base wall: the separations of order `< n` whose
  big side `B \ A` contains a base cycle and a vertical path of the base wall (the cylindrical-mesh
  tangle of p. 21 for the base wall).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The five kinds of elementary segments (a flap-segment carries its arity). -/
inductive SegKind
  | wall
  | handle
  | crosscap
  | flap (q : ℕ)
  | vortex
  deriving DecidableEq

/-- A vertex of an elementary surface-wall without hyperedge ends: segment, copy (`1` only in a
vortex-segment), row and column (`0`-based). -/
structure EVert (ℓ n : ℕ) where
  seg : Fin ℓ
  copy : Fin 2
  row : Fin n
  col : Fin (8 * n)
  deriving DecidableEq

/-- The special edges on the first row of a segment of the given kind (columns `0`-based). -/
def specialEdge (n : ℕ) : SegKind → ℕ → ℕ → Prop
  | .handle, a, b => ∃ i, 1 ≤ i ∧ i ≤ n ∧
      ((a = 2 * i - 1 ∧ b = 6 * n + 1 - 2 * i) ∨ (a = 2 * n + 2 * i - 1 ∧ b = 8 * n + 1 - 2 * i))
  | .crosscap, a, b => ∃ i, 1 ≤ i ∧ i ≤ 2 * n ∧ a = 2 * i - 1 ∧ b = 4 * n + 2 * i - 1
  | .flap q, a, b => ∃ i, 1 ≤ i ∧ i ≤ n ∧ a = 2 * i - 1 ∧ b = 4 * n + 2 * q + 1 - 2 * i
  | _, _, _ => False

/-- A horizontal edge (within a row of one copy) or a cylindrical-closure edge, oriented. -/
def IsHorizEdge {ℓ n : ℕ} (x y : EVert ℓ n) : Prop :=
  (x.seg = y.seg ∧ x.copy = y.copy ∧ x.row = y.row ∧ y.col.val = x.col.val + 1) ∨
  (x.copy = 0 ∧ y.copy = 0 ∧ x.row = y.row ∧ x.col.val = 8 * n - 1 ∧ y.col.val = 0 ∧
    y.seg.val = (x.seg.val + 1) % ℓ)

/-- The oriented edge relation of the elementary extended surface-wall (without hyperedge ends). -/
def EEdge (ks : List SegKind) (n : ℕ) (x y : EVert ks.length n) : Prop :=
  IsHorizEdge x y ∨
  (x.seg = y.seg ∧ x.copy = y.copy ∧ x.col = y.col ∧ y.row.val = x.row.val + 1 ∧
    x.row.val % 2 = x.col.val % 2) ∨
  (x.seg = y.seg ∧ x.copy = 0 ∧ y.copy = 0 ∧ x.row.val = 0 ∧ y.row.val = 0 ∧
    specialEdge n (ks.get x.seg) x.col.val y.col.val) ∨
  (x.seg = y.seg ∧ ks.get x.seg = .vortex ∧ x.copy = 0 ∧ y.copy = 1 ∧ x.row.val = 0 ∧
    y.row.val = 0 ∧ x.col = y.col ∧ x.col.val % 2 = 1) ∨
  (x.seg = y.seg ∧ ks.get x.seg = .vortex ∧ x.copy = 1 ∧ y.copy = 1 ∧ x.row = y.row ∧
    x.col.val = 0 ∧ y.col.val = 8 * n - 1)

/-- The vertex exists in the elementary graph (copy `1` only in vortex-segments). -/
def EPresent (ks : List SegKind) {n : ℕ} (x : EVert ks.length n) : Prop :=
  x.copy = 0 ∨ ks.get x.seg = .vortex

/-- Adjacency of the elementary extended surface-wall without hyperedge ends. -/
def EAdj (ks : List SegKind) (n : ℕ) (x y : EVert ks.length n) : Prop :=
  x ≠ y ∧ EPresent ks x ∧ EPresent ks y ∧ (EEdge ks n x y ∨ EEdge ks n y x)

/-- The arity of a segment kind as a flap (`0` for the other kinds). -/
def SegKind.flapArity : SegKind → ℕ
  | .flap q => q
  | _ => 0

/-- `ks` has signature `(h, c, f, b)`: exactly one wall-segment, `h` handle-, `c` crosscap-,
`f` flap- (each of arity in `[3]`) and `b` vortex-segments. -/
def KindsSignature (ks : List SegKind) (h c f b : ℕ) : Prop :=
  ks.count .wall = 1 ∧ ks.count .handle = h ∧ ks.count .crosscap = c ∧
    (ks.filter fun k => decide (∃ q, k = .flap q)).length = f ∧ ks.count .vortex = b ∧
    ∀ q, SegKind.flap q ∈ ks → 1 ≤ q ∧ q ≤ 3

/-- An extended `n`-surface-wall in `G` (see the module docstring). -/
structure SurfaceWall (G : SimpleGraph V) (n : ℕ) where
  /-- the cyclic order of the segment kinds -/
  kinds : List SegKind
  two_le : 2 ≤ n
  /-- branch vertices -/
  ι : EVert kinds.length n → V
  ι_inj : Set.InjOn ι {x | EPresent kinds x}
  /-- subdivision paths -/
  pth : EVert kinds.length n → EVert kinds.length n → GPath G
  pth_ends : ∀ x y, EAdj kinds n x y → (pth x y).s = ι x ∧ (pth x y).t = ι y
  pth_branch : ∀ x y, EAdj kinds n x y → ∀ z, EPresent kinds z → ι z ∈ (pth x y).verts →
    z = x ∨ z = y
  pth_symm : ∀ x y, EAdj kinds n x y → (pth y x).sub = (pth x y).sub
  pth_disj : ∀ x y x' y', EAdj kinds n x y → EAdj kinds n x' y' → s(x, y) ≠ s(x', y') →
    ∀ v ∈ (pth x y).verts, v ∈ (pth x' y').verts →
      ∃ z, (z = x ∨ z = y) ∧ (z = x' ∨ z = y') ∧ v = ι z
  /-- the hyperedge ends of each flap-segment -/
  zs : Fin kinds.length → Finset V
  zs_card : ∀ i, (zs i).card = (kinds.get i).flapArity
  zs_disj : Pairwise fun i j => Disjoint (zs i) (zs j)
  zs_out : ∀ i, ∀ v ∈ zs i, ∀ x y, EAdj kinds n x y → v ∉ (pth x y).verts

namespace SurfaceWall

variable {G : SimpleGraph V} {n : ℕ} (D : SurfaceWall G n)

/-- The union of the subdivision paths of the elementary edges satisfying `P`. -/
def subOf (P : EVert D.kinds.length n → EVert D.kinds.length n → Prop) : G.Subgraph :=
  ⨆ x, ⨆ y, ⨆ (_ : EAdj D.kinds n x y ∧ P x y), (D.pth x y).sub

/-- `D⁻` as a subgraph of `G`. -/
def sub : G.Subgraph := D.subOf fun _ _ => True

/-- All vertices of `D`: those of `D⁻` and the hyperedge ends. -/
def verts : Set V := D.sub.verts ∪ ⋃ i, (D.zs i : Set V)

/-- `D` has signature `(h, c, f, b)`. -/
def HasSignature (h c f b : ℕ) : Prop := KindsSignature D.kinds h c f b

/-- The base cycle `C_{r+1}` (`r` `0`-based): row `r` of the bases with the closure edges. -/
def baseCycle (r : Fin n) : G.Subgraph :=
  D.subOf fun x y => x.copy = 0 ∧ y.copy = 0 ∧ x.row = r ∧ y.row = r ∧
    (IsHorizEdge x y ∨ IsHorizEdge y x)

/-- The simple cycle `Cₙ`. -/
def simpleCycle : G.Subgraph := D.baseCycle ⟨n - 1, by have := D.two_le; omega⟩

/-- The `(j+1)`-th vertical path (`j < 4n`) of the base of segment `i`: induced by the columns
`2j, 2j+1` (`0`-based). -/
def verticalPath (i : Fin D.kinds.length) (j : ℕ) : G.Subgraph :=
  D.subOf fun x y => x.seg = i ∧ y.seg = i ∧ x.copy = 0 ∧ y.copy = 0 ∧
    x.col.val / 2 = j ∧ y.col.val / 2 = j

/-- The cycle `C_{k+1}` (`k` `0`-based, `C₁` the inner cycle) of the nest of the vortex-segment `i`:
row `n - 1 - k` of its copy `W₁`, closed by its left–right edge. -/
def nestCycle (i : Fin D.kinds.length) (k : Fin n) : G.Subgraph :=
  D.subOf fun x y => x.seg = i ∧ y.seg = i ∧ x.copy = 1 ∧ y.copy = 1 ∧
    x.row.val = n - 1 - k.val ∧ y.row.val = n - 1 - k.val ∧
    (x.row = y.row ∧ (x.col.val + 1 = y.col.val ∨ y.col.val + 1 = x.col.val ∨
      (x.col.val = 0 ∧ y.col.val = 8 * n - 1) ∨ (y.col.val = 0 ∧ x.col.val = 8 * n - 1)))

/-- The pocket of the flap-segment `i` of arity `q`: the skip edge between columns `2n - 1` and
`2n + 2q + 1` (`0`-based) with the part of the first row between them. -/
def pocket (i : Fin D.kinds.length) : G.Subgraph :=
  D.subOf fun x y => x.seg = i ∧ y.seg = i ∧ x.copy = 0 ∧ y.copy = 0 ∧ x.row.val = 0 ∧
    y.row.val = 0 ∧
    ((x.col.val = 2 * n - 1 ∧ y.col.val = 2 * n + 2 * (D.kinds.get i).flapArity + 1) ∨
      (y.col.val = 2 * n - 1 ∧ x.col.val = 2 * n + 2 * (D.kinds.get i).flapArity + 1) ∨
      (2 * n - 1 ≤ x.col.val ∧ x.col.val ≤ 2 * n + 2 * (D.kinds.get i).flapArity + 1 ∧
        2 * n - 1 ≤ y.col.val ∧ y.col.val ≤ 2 * n + 2 * (D.kinds.get i).flapArity + 1 ∧
        (x.col.val + 1 = y.col.val ∨ y.col.val + 1 = x.col.val)))

/-- The flap-segments. -/
def IsFlapSeg (i : Fin D.kinds.length) : Prop := ∃ q, D.kinds.get i = .flap q

/-- The vortex-segments. -/
def IsVortexSeg (i : Fin D.kinds.length) : Prop := D.kinds.get i = .vortex

/-- The wall-segment. -/
def IsWallSeg (i : Fin D.kinds.length) : Prop := D.kinds.get i = .wall

/-- The tangle induced by `D` (by its base wall). -/
def tangle : Set (Finset V × Finset V) :=
  {S | S ∈ SepLt G n ∧ (∃ r, ((D.baseCycle r).verts : Set V) ⊆ ↑(S.2 \ S.1)) ∧
    ∃ i, ∃ j < 4 * n, ((D.verticalPath i j).verts : Set V) ⊆ ↑(S.2 \ S.1)}

end SurfaceWall

end GMSTFramework.LocalStructure


