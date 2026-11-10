-- Prove2me | Definitions.Def_ChengCapClustering_Soft_Network
-- name    : ChengCapClustering_Soft_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:14.611479+00:00
-- url     : https://prove2.me/theorems/c816408a-7cd7-4da0-aab6-06ec39b14391
-- title:
--   Hierarchical decompositions, $\Lambda$-bad pairs, portals, the network $N_D$ and network solutions
-- statement:
--   §4.2–§4.3 (printed pp. 14–18), Definitions 4.2, 4.7, 4.9. The point set $X=P\cup F$ is an injective list $x:\mathrm{Fin}\,N\to V$.
--
--   - `MinDistTwo`: distinct points are at distance $\ge2$ and some pair at exactly $2$ (the normalization of §§4.2–4.3). `topLevel`: the least $H$ with all distances $\le 2^H$.
--   - **Hierarchical decomposition** (Definition 4.2): partitions $\mathcal P_0,\dots,\mathcal P_H$ of $X$ (as cell labels per level and point) with $H$ the top level, $\mathcal P_H=\{X\}$, cells of level $h$ of diameter $\le 2^h$, and $\mathcal P_h$ refining $\mathcal P_{h+1}$. A cell is a (level, label) pair. The cut level $\mathrm{lev}(x,y)$ is the least level with a common cell; a pair of distinct points is **$\Lambda$-bad** if $2^{\mathrm{lev}(x,y)}>\Lambda\,\mathrm{dist}(x,y)$.
--   - **Portal system**: in every cell $C$ of level $h$ a maximal subset $\Pi_C$ whose points are pairwise more than $\lambda2^h$ apart, and for $h<H$ a parent portal $\mathrm{par}(x')\in\Pi_{C^+}$ with $\mathrm{dist}(x',\mathrm{par}(x'))\le\lambda2^{h+1}$.
--   - **Network $N_D$** (Definition 4.7): ascending and descending copies of every portal of every cell, and $x_{src}$, $x_{snk}$ for every point; ascending arcs $x'^\uparrow_C\to\mathrm{par}(x')^\uparrow_{C^+}$ and descending arcs $\mathrm{par}(x')^\downarrow_{C^+}\to x'^\downarrow_C$ of cost $0$; crossing arcs $x'^\uparrow_C\to y'^\downarrow_C$ ($x',y'\in\Pi_C$, level $h$) of cost $(\mathrm{dist}(x',y')+4\lambda2^h)^z$; arcs $x_{src}\to x^\uparrow_{\{x\}}$, $x^\downarrow_{\{x\}}\to x_{snk}$, $x_{src}\to x_{snk}$ of cost $0$. A path is a vertex list joined by arcs; its cost is the sum of its arc costs.
--   - **Network solution** (Definition 4.9): rescued blocks $R$ and an integral flow $f\ge0$ on the arcs, conserved at every portal vertex, with outflow $s_x=\sum_{i\notin R,\,a_i=x}w_i$ at $x_{src}$ and inflow $\ell_y=0$ at $y_{snk}$ for $y\notin F$; its number of centers is $|R|+\sum_{y\in F}\lceil\ell_y/U\rceil$ (feasible if $\le K$), and its cost is $\Phi(R,f)=\sum_{i\notin R}(u-1)A_i+v\sum_e\mathrm{cost}(e)f(e)$.
--   - Input/output layouts of decompositions, portal systems, vertices (codes `[kind, level, cell, point]`), flows (lists of arc entries) and the point-indexed instance.
--
--   The ambient vertex type also contains inactive (level, label, point) triples. On valid inputs these vertices are isolated, and the requirement that flow vanish off arcs forces all their incident flows to zero; they add no routes or feasible solutions. The flow-cost term is outside the sum over normal blocks.
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), §4.2, Definition 4.2, printed p. 14 / PDF p. 16; §4.3.1, eq. (8), Definition 4.7, printed p. 17 / PDF p. 19; Definition 4.9, printed p. 18 / PDF p. 20

import Mathlib
import Definitions.Def_ChengCapClustering_Soft_Clustering

namespace ChengCapClustering.Soft

/-!
# Hierarchical decompositions, bad pairs, the portal network and network solutions

Cheng, Mo, Ding, arXiv:2610.40625 (held manuscript SHA-256 9d298191…): §4.2 and Definition 4.2
(printed p. 14 / PDF p. 16), §4.3.1, eq. (8) and Definition 4.7 (printed p. 17 / PDF p. 19),
Definition 4.9 (printed p. 18 / PDF p. 20).

**Formalization Note.**
* The finite point set `X` is an injective list `x : Fin N → V`; a point is named by its index.
* A hierarchical decomposition stores, for every level `h ∈ {0, …, H}` and point `i`, the label
  `lab h i : Fin N` of the cell of level `h` containing `i`; the cells of level `h` are the classes
  of equal label. A cell is the pair (level, label), so cells of different levels are different
  objects even if they contain the same points. `topLevel x` is the least `H : ℕ` with
  `dist ≤ 2^H` for all pairs (the least integer with `2^H ≥ diam X`; it is `≥ 1` under the
  standing assumption of §4.2 that the minimum distance is `2`).
* The portals of cell `(h, ℓ)` are `portals h ℓ`; `parent h ℓ p` is the fixed portal `par(p)` of the
  parent cell. A portal system is valid when every portal set is a maximal `λ2^h`-separated subset
  of its cell (pairwise distance `> λ2^h`, and every point of the cell within `λ2^h` of a portal)
  and every parent portal is a portal of the parent cell within `λ2^{h+1}`.
* The network has vertex type `NetVertex N H` (finite); `IsArc` lists exactly the arcs of
  Definition 4.7 and `arcCost` their costs (crossing arcs `(dist(x′, y′) + 4λ2^h)^z`, all others `0`).
  A flow is a function on ordered vertex pairs that vanishes off the arcs.
-/

open scoped BigOperators

variable {V : Type*} [PseudoMetricSpace V]

/-- `H`: the least natural number with `dist(x_i, x_j) ≤ 2^H` for all `i, j` (§4.2). -/
noncomputable def topLevel {N : ℕ} (x : Fin N → V) : ℕ :=
  sInf {H : ℕ | ∀ i j, dist (x i) (x j) ≤ (2 : ℝ) ^ H}

/-- The standing normalization of §§4.2–4.3: distinct points are at distance at least `2`, and
some two distinct points are at distance exactly `2` (the minimum distance is `2`). -/
def MinDistTwo {N : ℕ} (x : Fin N → V) : Prop :=
  (∀ i j, i ≠ j → 2 ≤ dist (x i) (x j)) ∧ ∃ i j, i ≠ j ∧ dist (x i) (x j) = 2

/-- A hierarchical decomposition with levels `0, …, H`: the cell label of every point at every
level. -/
structure HierDecomp (N : ℕ) where
  H : ℕ
  lab : Fin (H + 1) → Fin N → Fin N

/-- Definition 4.2: `D` is a hierarchical decomposition of `X = {x_0, …, x_{N-1}}`: `H` is the top
level of §4.2, the level-`H` partition is `{X}`, every cell of level `h` has diameter at most `2^h`,
and the partition of level `h` refines that of level `h + 1`. -/
def HierDecomp.IsValid {N : ℕ} (x : Fin N → V) (D : HierDecomp N) : Prop :=
  D.H = topLevel x ∧
    (∀ i j, D.lab (Fin.last D.H) i = D.lab (Fin.last D.H) j) ∧
    (∀ h i j, D.lab h i = D.lab h j → dist (x i) (x j) ≤ (2 : ℝ) ^ (h : ℕ)) ∧
    ∀ h : Fin D.H, ∀ i j, D.lab h.castSucc i = D.lab h.castSucc j →
      D.lab h.succ i = D.lab h.succ j

/-- The cut level `lev(x, y)`: the least level at which `i` and `j` lie in a common cell. -/
noncomputable def HierDecomp.cutLevel {N : ℕ} (D : HierDecomp N) (i j : Fin N) : ℕ :=
  sInf {h : ℕ | ∃ hh : h < D.H + 1, D.lab ⟨h, hh⟩ i = D.lab ⟨h, hh⟩ j}

/-- Definition 4.2: the pair `(x_i, x_j)` is `Λ`-bad in `D`: the points are distinct and
`2^{lev} > Λ · dist`. A pair `(x, x)` is never bad. -/
def HierDecomp.IsBad {N : ℕ} (x : Fin N → V) (D : HierDecomp N) (Λ : ℝ) (i j : Fin N) : Prop :=
  x i ≠ x j ∧ Λ * dist (x i) (x j) < (2 : ℝ) ^ D.cutLevel i j

/-- Portals of every cell `(h, ℓ)` and the fixed parent portal `par` of every portal. -/
structure PortalSystem (N H : ℕ) where
  portals : Fin (H + 1) → Fin N → Finset (Fin N)
  parent : Fin (H + 1) → Fin N → Fin N → Fin N

/-- §4.3.1: every portal set `Π_C` is a maximal subset of its cell `C` (level `h`) whose points are
pairwise more than `λ2^h` apart, and for a cell `C` of level `h < H` and `x′ ∈ Π_C` the portal
`par(x′)` lies in `Π_{C+}` for the parent cell `C+` with `dist(x′, par(x′)) ≤ λ2^{h+1}`. -/
def PortalSystem.IsValid {N : ℕ} (x : Fin N → V) (D : HierDecomp N) (lam : ℝ)
    (P : PortalSystem N D.H) : Prop :=
  (∀ h ℓ p, p ∈ P.portals h ℓ → D.lab h p = ℓ) ∧
    (∀ h ℓ p q, p ∈ P.portals h ℓ → q ∈ P.portals h ℓ → p ≠ q →
      lam * (2 : ℝ) ^ (h : ℕ) < dist (x p) (x q)) ∧
    (∀ h i, ∃ p ∈ P.portals h (D.lab h i), dist (x i) (x p) ≤ lam * (2 : ℝ) ^ (h : ℕ)) ∧
    ∀ h : Fin D.H, ∀ ℓ p, p ∈ P.portals h.castSucc ℓ →
      P.parent h.castSucc ℓ p ∈ P.portals h.succ (D.lab h.succ p) ∧
        dist (x p) (x (P.parent h.castSucc ℓ p)) ≤ lam * (2 : ℝ) ^ ((h : ℕ) + 1)

/-- The vertices of the network `N_D`: the ascending copy `up h ℓ p` and the descending copy
`down h ℓ p` of portal `p` of cell `(h, ℓ)`, and `src i`, `snk i` for every point. -/
inductive NetVertex (N H : ℕ) where
  | up (h : Fin (H + 1)) (cell portal : Fin N)
  | down (h : Fin (H + 1)) (cell portal : Fin N)
  | src (point : Fin N)
  | snk (point : Fin N)
  deriving DecidableEq, Fintype

/-- The portal vertices (ascending and descending copies). -/
def NetVertex.IsPortal {N H : ℕ} : NetVertex N H → Prop
  | .up _ _ _ => True
  | .down _ _ _ => True
  | _ => False

/-- Definition 4.7: the arcs of `N_D`. Ascending arcs `x′↑_C → par(x′)↑_{C+}` and descending arcs
`par(x′)↓_{C+} → x′↓_C` for a cell `C` of level `h < H` and `x′ ∈ Π_C`; crossing arcs
`x′↑_C → y′↓_C` for `x′, y′ ∈ Π_C`; and `x_src → x↑_{x}`, `x↓_{x} → x_snk`, `x_src → x_snk`, where
`{x}` is the level-0 cell of `x`. -/
def IsArc {N : ℕ} (D : HierDecomp N) (P : PortalSystem N D.H) :
    NetVertex N D.H → NetVertex N D.H → Prop
  | .up h ℓ p, .up h' ℓ' p' =>
      (h : ℕ) + 1 = h' ∧ p ∈ P.portals h ℓ ∧ ℓ' = D.lab h' p ∧ p' = P.parent h ℓ p
  | .down h' ℓ' p', .down h ℓ p =>
      (h : ℕ) + 1 = h' ∧ p ∈ P.portals h ℓ ∧ ℓ' = D.lab h' p ∧ p' = P.parent h ℓ p
  | .up h ℓ p, .down h' ℓ' q => h = h' ∧ ℓ = ℓ' ∧ p ∈ P.portals h ℓ ∧ q ∈ P.portals h ℓ
  | .src i, .up h ℓ p => h = 0 ∧ ℓ = D.lab 0 i ∧ p = i
  | .down h ℓ p, .snk i => h = 0 ∧ ℓ = D.lab 0 i ∧ p = i
  | .src i, .snk j => i = j
  | _, _ => False

/-- Arc costs: a crossing arc `x′↑_C → y′↓_C` at level `h` costs `(dist(x′, y′) + 4λ2^h)^z`; every
other arc costs `0`. -/
noncomputable def arcCost {N H : ℕ} (x : Fin N → V) (z lam : ℝ) :
    NetVertex N H → NetVertex N H → ℝ
  | .up h _ p, .down _ _ q => (dist (x p) (x q) + 4 * lam * (2 : ℝ) ^ (h : ℕ)) ^ z
  | _, _ => 0

/-- `path` is a path of `N_D` from `a` to `b`: a nonempty vertex list starting at `a`, ending at
`b`, with an arc between consecutive vertices. -/
def IsNetPath {N : ℕ} (D : HierDecomp N) (P : PortalSystem N D.H)
    (path : List (NetVertex N D.H)) (a b : NetVertex N D.H) : Prop :=
  path.head? = some a ∧ path.getLast? = some b ∧ path.IsChain (IsArc D P)

/-- The cost of a path: the sum of its arc costs. -/
noncomputable def pathCost {N H : ℕ} (x : Fin N → V) (z lam : ℝ) (path : List (NetVertex N H)) :
    ℝ :=
  ((path.zip path.tail).map fun e => arcCost x z lam e.1 e.2).sum

/-- A network solution: a set of rescued blocks and an integral flow on ordered vertex pairs. -/
structure NetSolution (N H m : ℕ) where
  rescued : Finset (Fin m)
  flow : NetVertex N H → NetVertex N H → ℕ

/-- Total inflow of a vertex. -/
def inflow {N H : ℕ} (f : NetVertex N H → NetVertex N H → ℕ) (b : NetVertex N H) : ℕ :=
  ∑ a, f a b

/-- Total outflow of a vertex. -/
def outflow {N H : ℕ} (f : NetVertex N H → NetVertex N H → ℕ) (a : NetVertex N H) : ℕ :=
  ∑ b, f a b

open Classical in
/-- `s_x = ∑_{i ∉ R, a_i = x} w_i`: the clients of the normal blocks with representative `x_i`. -/
noncomputable def srcAmount {N n H : ℕ} (x : Fin N → V) (B : BlockPartition V n)
    (S : NetSolution N H B.numBlocks) (i : Fin N) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ∉ S.rescued ∧ B.rep j = x i), B.size j

/-- Definition 4.9: `S = (R, f)` is a network solution of `N_D` for the block partition `B` and
locations `F`: `f` vanishes off the arcs, every portal vertex has equal inflow and outflow, every
`x_src` has outflow `s_x`, and every `y_snk` with `y ∉ F` has inflow `0`. -/
def IsNetSolution {N n : ℕ} (x : Fin N → V) (F : Set V) (D : HierDecomp N)
    (P : PortalSystem N D.H) (B : BlockPartition V n) (S : NetSolution N D.H B.numBlocks) :
    Prop :=
  (∀ a b, ¬ IsArc D P a b → S.flow a b = 0) ∧
    (∀ a, a.IsPortal → inflow S.flow a = outflow S.flow a) ∧
    (∀ i, outflow S.flow (.src i) = srcAmount x B S i) ∧
    ∀ y, x y ∉ F → inflow S.flow (.snk y) = 0

open Classical in
/-- Definition 4.9: the number of centers `|R| + ∑_{y ∈ F} ⌈ℓ_y / U⌉` of a network solution. -/
noncomputable def NetSolution.numCenters {N H m : ℕ} (x : Fin N → V) (F : Set V) (U : ℕ)
    (S : NetSolution N H m) : ℕ :=
  S.rescued.card +
    ∑ y ∈ Finset.univ.filter (fun y => x y ∈ F), ⌈(inflow S.flow (.snk y) : ℝ) / (U : ℝ)⌉₊

/-- Definition 4.9: a feasible network solution has at most `K` centers. -/
def IsFeasibleNetSolution {N n : ℕ} (x : Fin N → V) (F : Set V) (U K : ℕ) (D : HierDecomp N)
    (P : PortalSystem N D.H) (B : BlockPartition V n) (S : NetSolution N D.H B.numBlocks) :
    Prop :=
  IsNetSolution x F D P B S ∧ S.numCenters x F U ≤ K

/-- Definition 4.9: `Φ(R, f) = ∑_{i ∉ R} (u − 1) A_i + v · cost(f)`, `cost(f) = ∑_e cost(e) f(e)`. -/
noncomputable def netCost {N n : ℕ} (x : Fin N → V) (p : Fin n → V) (z u v lam : ℝ)
    (D : HierDecomp N) (B : BlockPartition V n) (S : NetSolution N D.H B.numBlocks) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j => j ∉ S.rescued), (u - 1) * B.internalCost z p j) +
    v * (∑ a, ∑ b, arcCost x z lam a b * (S.flow a b : ℝ))

/-! ### Input and output layouts for the algorithms of §4 -/

/-- A two-index table in row-major order. -/
def table2 {α : Type*} {a b : ℕ} (g : Fin a → Fin b → α) : List α :=
  List.ofFn fun ij : Fin (a * b) => g (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2

/-- The integer layout of a hierarchical decomposition: `[H]` followed by the labels, level by
level. -/
def HierDecomp.encode {N : ℕ} (D : HierDecomp N) : List ℤ :=
  (D.H : ℤ) :: table2 fun (h : Fin (D.H + 1)) (i : Fin N) => ((D.lab h i : ℕ) : ℤ)

/-- The integer layout of a portal system: the portal indicator of `(h, ℓ, p)`, then the parent
portal of `(h, ℓ, p)`, both in row-major order over `(h, (ℓ, p))`. -/
def PortalSystem.encode {N H : ℕ} (P : PortalSystem N H) : List ℤ :=
  (table2 fun (h : Fin (H + 1)) (ℓp : Fin (N * N)) =>
      if (finProdFinEquiv.symm ℓp).2 ∈ P.portals h (finProdFinEquiv.symm ℓp).1 then (1 : ℤ)
      else 0) ++
    table2 fun (h : Fin (H + 1)) (ℓp : Fin (N * N)) =>
      ((P.parent h (finProdFinEquiv.symm ℓp).1 (finProdFinEquiv.symm ℓp).2 : ℕ) : ℤ)

/-- The code of a vertex: `[0, h, ℓ, p]` (ascending), `[1, h, ℓ, p]` (descending), `[2, 0, 0, i]`
(source), `[3, 0, 0, i]` (sink). -/
def NetVertex.code {N H : ℕ} : NetVertex N H → List ℤ
  | .up h ℓ p => [0, ((h : ℕ) : ℤ), ((ℓ : ℕ) : ℤ), ((p : ℕ) : ℤ)]
  | .down h ℓ p => [1, ((h : ℕ) : ℤ), ((ℓ : ℕ) : ℤ), ((p : ℕ) : ℤ)]
  | .src i => [2, 0, 0, ((i : ℕ) : ℤ)]
  | .snk i => [3, 0, 0, ((i : ℕ) : ℤ)]

/-- The flow described by a list of entries `(a, b, value)`: the sum of the values listed for
`(a, b)`. -/
def flowOfList {N H : ℕ} (L : List (NetVertex N H × NetVertex N H × ℕ))
    (a b : NetVertex N H) : ℕ :=
  ((L.filter fun e => decide (e.1 = a ∧ e.2.1 = b)).map fun e => e.2.2).sum

/-- The integer layout of a network solution given by a rescued set and a flow list: the
indicator of `R` over the `m` blocks, the number of entries, then every entry as
`code a ++ code b ++ [value]`. -/
def encodeNetSolution {N H m : ℕ} (R : Finset (Fin m))
    (L : List (NetVertex N H × NetVertex N H × ℕ)) : List ℤ :=
  List.ofFn (fun j : Fin m => if j ∈ R then (1 : ℤ) else 0) ++ (L.length : ℤ) ::
    L.flatMap fun e => e.1.code ++ e.2.1.code ++ [(e.2.2 : ℤ)]

/-- The point-indexed instance of §4: points `x : Fin N → V` (the set `X = P ∪ F`), the point of
every client `cl : Fin n → Fin N`, the locations `Floc ⊆ {0, …, N-1}`, parameters `k`, `U`, and a
block partition given by block labels and representative indices. Integer layout:
`[N, n, k, U] ++ cl ++ (indicator of Floc) ++ [m] ++ blk ++ repIdx`. -/
def encodePointInstance {N n m : ℕ} (k U : ℕ) (cl : Fin n → Fin N) (Floc : Finset (Fin N))
    (blk : Fin n → Fin m) (repIdx : Fin m → Fin N) : List ℤ :=
  [(N : ℤ), (n : ℤ), (k : ℤ), (U : ℤ)] ++ List.ofFn (fun q => ((cl q : ℕ) : ℤ)) ++
    List.ofFn (fun i => if i ∈ Floc then (1 : ℤ) else 0) ++ (m : ℤ) ::
    (List.ofFn (fun q => ((blk q : ℕ) : ℤ)) ++ List.ofFn fun j => ((repIdx j : ℕ) : ℤ))

end ChengCapClustering.Soft


