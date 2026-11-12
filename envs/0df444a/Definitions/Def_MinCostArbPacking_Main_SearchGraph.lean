-- Prove2me | Definitions.Def_MinCostArbPacking_Main_SearchGraph
-- name    : MinCostArbPacking_Main_SearchGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:23.083177+00:00
-- url     : https://prove2.me/theorems/4d3ef541-f543-4d93-a2cd-d8f859c84c72
-- title:
--   Forest swaps and the search graphs $D_{\mathrm{fine}}$ and $D_{\mathrm{cmp}}$ with the potential (5.6)
-- statement:
--   Fix a forest decomposition $I=F_1\,\dot\cup\cdots\dot\cup\,F_k$.
--
--   1. **Forest swaps (Definition 4.11).** $e\to f$ is a forest swap in $F_i$ if $e\notin F_i$, the ends of $e$ are connected in $F_i$ and $f$ lies on the $F_i$-path between them; $e$ reaches $f$ if there is a sequence of forest swaps (in possibly different forests) from $e$ to $f$; $e$ is **joining** if its ends lie in different components of some $F_i$ with $e\notin F_i$. Executing a swap path $e_0\to\cdots\to e_s$ replaces, simultaneously for all $j\ge1$, $e_j$ by $e_{j-1}$ in the forest containing $e_j$.
--   2. **$D_{\mathrm{fine}}$.** Vertices: the elements, a sink $z$ and head vertices $v^\star$. Arcs with (weight, length): $e\to z$ $(0,0)$ for free $e$; every forest swap $(0,0)$; $f\to\mathrm{head}(f)^\star$ $(-c(f),1)$ for $f\in I$; $\mathrm{head}(e)^\star\to e$ $(c(e),0)$ for $e\notin I$.
--   3. **Jump structure.** Every component of every $F_i$ is rooted; $p_i^d(x)$ is the ancestor $d$ edges above $x$ and $f_i(x)$ the edge to the parent. For $2^j\le\mathrm{depth}_i(x)$ there is a jump vertex $x_{i,j}$ with arcs $x_{i,0}\to f_i(x)$, $x_{i,j}\to x_{i,j-1}$ and $x_{i,j}\to(p_i^{2^{j-1}}(x))_{i,j-1}$, all of weight $0$. A scan of $e=(u,v)$ into $F_i$ is represented, for each nonempty branch of length $d$ from $x\in\{u,v\}$ to the lowest common ancestor, by the jump vertices $x_{i,j}$ and $(p_i^{d-2^j}(x))_{i,j}$ with $j=\lfloor\log_2 d\rfloor$ (4.3).
--   4. **$D_{\mathrm{cmp}}$.** Vertices: elements of $I$, head vertices, jump vertices and $z$. Arcs: $f\to\mathrm{head}(f)^\star$ $(-c(f),1)$; $\mathrm{head}(e)^\star\to x$ $(c(e),0)$ labelled $e$, for $e\notin I$ and $x\in J(e)$; $f\to x$ $(0,0)$ for $f\in I$, $x\in J(f)$; the jump arcs; and $\mathrm{head}(e)^\star\to z$ $(c(e),0)$ labelled $e$ for free $e$. In the **full** version every element scans every forest not containing it; in the **cyclic** version elements of $E\setminus I$ scan only $F_1$ and elements of $F_i$ scan only $F_{i+1}$ (indices mod $k$).
--   5. The **projection** of a search path lists the labels and the elements of $I$ immediately followed by a head vertex, in order.
--   6. **Potential (5.6).** $p(v^\star)=h(v)$, $p(z)=0$, and $p(x)=\min\{-a(f): f\in I,\ x\leadsto f \text{ in } Q\}$, where $Q$ consists of the forest-swap arcs; reduced weights are $w_p(x,y)=w(x,y)-p(x)+p(y)$. Distances are infima of walk weights.
--
--   **Formalization Note** Search graphs are given by arc types with a validity predicate; vertices that carry no valid arc (suppressed elements $e\notin I$, nonexistent jump vertices) do not affect paths. The minimum in (5.6) is taken with `sInf` over a set that is nonempty and finite for every vertex of $Q$.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Definition 4.11, p.15; §4.3, pp.15–19; §5.3, p.24; App. A–B, pp.32–34

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange

set_option autoImplicit false

/-!
# Forest swaps and the search graphs `D_fine` and `D_cmp`

Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Definition 4.11 and §4.3 (pp.15–19),
§5.3 (p.24), Appendices A–B (pp.32–34).

Throughout, `F : Fin k → Finset E` is a fixed forest decomposition of `I`. Weighted search graphs
are given by an arc type with `src`, `tgt`, a validity predicate (which arcs exist), a primary weight
`w` and a secondary length `q`; walks are lists of valid arcs.
-/

noncomputable section
open Classical

namespace MinCostArbPacking.Main

/-! ### Walks in a weighted digraph given by an arc type -/

section Walks
variable {A W : Type}

/-- `as` is a walk from `x` to `y`: consecutive valid arcs. -/
def IsWalk (src tgt : A → W) (valid : A → Prop) : List A → W → W → Prop
  | [], x, y => x = y
  | a :: as, x, y => valid a ∧ src a = x ∧ IsWalk src tgt valid as (tgt a) y

/-- A simple path: a walk whose vertices `x, tgt a₁, tgt a₂, …` are distinct. -/
def IsSimpleWalk (src tgt : A → W) (valid : A → Prop) (as : List A) (x y : W) : Prop :=
  IsWalk src tgt valid as x y ∧ (x :: as.map tgt).Nodup

/-- A directed cycle through `x`: a nonempty closed walk whose vertices are distinct. -/
def IsCycleWalk (src tgt : A → W) (valid : A → Prop) (as : List A) (x : W) : Prop :=
  as ≠ [] ∧ IsWalk src tgt valid as x x ∧ (as.map tgt).Nodup

/-- The total primary weight of a list of arcs. -/
def walkWeight (w : A → ℝ) (as : List A) : ℝ := (as.map w).sum

/-- The total secondary length of a list of arcs. -/
def walkQ (q : A → ℕ) (as : List A) : ℕ := (as.map q).sum

/-- The graph has a negative cycle. -/
def HasNegCycle (src tgt : A → W) (valid : A → Prop) (w : A → ℝ) : Prop :=
  ∃ as x, IsCycleWalk src tgt valid as x ∧ walkWeight w as < 0

/-- The shortest-path distance from `x` to `y` (infimum of walk weights; `+∞` if `y` is not
reachable). -/
def walkDist (src tgt : A → W) (valid : A → Prop) (w : A → ℝ) (x y : W) : EReal :=
  sInf {z : EReal | ∃ as, IsWalk src tgt valid as x y ∧ z = (walkWeight w as : EReal)}

end Walks

variable {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]

namespace Digraph

/-! ### Forest swaps (Definition 4.11) -/

/-- `e → f` is a forest swap in `F i`: `e ∉ F i`, the ends of `e` are connected in `F i`, and `f`
lies on the `F i`-path between them. -/
def IsForestSwap (G : Digraph V E) {k : ℕ} (F : Fin k → Finset E) (e f : E) (i : Fin k) : Prop :=
  e ∉ F i ∧ G.OnPath (F i) e f

/-- `e → f` is a forest swap in some forest. -/
def SwapStep (G : Digraph V E) {k : ℕ} (F : Fin k → Finset E) (e f : E) : Prop :=
  ∃ i, G.IsForestSwap F e f i

/-- `e` reaches `f` by forest swaps (`t ≥ 0` swaps). -/
def SwapReach (G : Digraph V E) {k : ℕ} (F : Fin k → Finset E) (e f : E) : Prop :=
  Relation.ReflTransGen (G.SwapStep F) e f

/-- `e` is joining: its ends lie in different components of `F i` for some `i` with `e ∉ F i`. -/
def IsJoining (G : Digraph V E) {k : ℕ} (F : Fin k → Finset E) (e : E) : Prop :=
  ∃ i, e ∉ F i ∧ ¬ G.Conn (F i) (G.tail e) (G.head e)

/-- A path of forest swaps `e = e₀ → e₁ → ⋯ → e_s = f`, given as the list `[e₀, …, e_s]`. -/
def IsSwapPath (G : Digraph V E) {k : ℕ} (F : Fin k → Finset E) (e f : E) (es : List E) : Prop :=
  es.head? = some e ∧ es.getLast? = some f ∧ es.IsChain (G.SwapStep F)

/-- Executing a swap path `[e₀, …, e_s]`: simultaneously, for every `j ≥ 1`, remove `e_j` from its
forest and insert `e_{j-1}` into that forest. -/
def execSwaps {k : ℕ} (F : Fin k → Finset E) (es : List E) : Fin k → Finset E := fun i =>
  let pairs := (es.zip es.tail).filter (fun p => decide (p.2 ∈ F i))
  (F i \ (pairs.map Prod.snd).toFinset) ∪ (pairs.map Prod.fst).toFinset

/-- The successor index `i + 1 mod k`. -/
def cycNext {k : ℕ} (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-! ### The fine-grained search graph `D_fine` (p.15) -/

/-- Vertices of `D_fine`: elements, the sink `z`, and head vertices `v⋆`. -/
inductive FineV (V E : Type)
  | elem (e : E)
  | sink
  | hd (v : V)

/-- Arcs of `D_fine`. -/
inductive FineArc (V E : Type) (k : ℕ)
  /-- `e → z`, for free `e`, `(w, q) = (0, 0)`. -/
  | toSink (e : E)
  /-- the forest swap `e → f` in `F i`, `(0, 0)`. -/
  | swap (i : Fin k) (e f : E)
  /-- `f → head(f)⋆` for `f ∈ I`, `(-c(f), 1)`. -/
  | up (f : E)
  /-- `head(e)⋆ → e` for `e ∉ I`, `(c(e), 0)`. -/
  | down (e : E)

/-- Source vertex of an arc of `D_fine`. -/
def fineSrc (G : Digraph V E) {k : ℕ} : FineArc V E k → FineV V E
  | .toSink e => .elem e
  | .swap _ e _ => .elem e
  | .up f => .elem f
  | .down e => .hd (G.head e)

/-- Target vertex of an arc of `D_fine`. -/
def fineTgt (G : Digraph V E) {k : ℕ} : FineArc V E k → FineV V E
  | .toSink _ => .sink
  | .swap _ _ f => .elem f
  | .up f => .hd (G.head f)
  | .down e => .elem e

/-- Which arcs of `D_fine` exist (all forest swaps are present). -/
def fineValid (G : Digraph V E) (k : ℕ) (I : Finset E) (F : Fin k → Finset E) :
    FineArc V E k → Prop
  | .toSink e => G.Free k I e
  | .swap i e f => G.IsForestSwap F e f i
  | .up f => f ∈ I
  | .down e => e ∉ I

/-- Primary weight `w` on `D_fine`. -/
def fineW {k : ℕ} (c : E → ℝ) : FineArc V E k → ℝ
  | .toSink _ => 0
  | .swap _ _ _ => 0
  | .up f => -c f
  | .down e => c e

/-- Secondary length `q` on `D_fine`. -/
def fineQ {k : ℕ} : FineArc V E k → ℕ
  | .up _ => 1
  | _ => 0

/-- Projection of a `D_fine` walk to `D`: keep the element entered from a head vertex and every
element of `I` immediately followed by a head vertex, in order. -/
def projFine {k : ℕ} (as : List (FineArc V E k)) : List E :=
  as.filterMap fun a => match a with
    | .down e => some e
    | .up f => some f
    | _ => none

/-! ### Rooted forests and the jump structure (p.16) -/

/-- The other end of `e` seen from `x`. -/
def otherEnd (G : Digraph V E) (e : E) (x : V) : V := if G.tail e = x then G.head e else G.tail e

/-- One step towards the root (`ρ x` is the arc joining `x` to its parent, `none` at a root). -/
def upV (G : Digraph V E) (ρ : V → Option E) (x : V) : V :=
  match ρ x with
  | none => x
  | some f => G.otherEnd f x

/-- `p^d(x)`: the ancestor `d` edges above `x`. -/
def anc (G : Digraph V E) (ρ : V → Option E) (d : ℕ) (x : V) : V := (G.upV ρ)^[d] x

/-- The depth of `x`: the number of edges from `x` to the root of its component. -/
def depth (G : Digraph V E) (ρ : V → Option E) (x : V) : ℕ :=
  sInf {d | ρ (G.anc ρ d x) = none}

/-- `ρ` roots every component of the forest `F`: parent arcs belong to `F` and are incident to their
child (and are not loops), every arc of `F` is the parent arc of exactly one vertex, and every
vertex reaches a root. -/
def IsRooting (G : Digraph V E) (F : Finset E) (ρ : V → Option E) : Prop :=
  (∀ x f, ρ x = some f → f ∈ F ∧ (G.tail f = x ∨ G.head f = x) ∧ G.tail f ≠ G.head f) ∧
    (∀ f ∈ F, ∃! x, ρ x = some f) ∧ (∀ x, ∃ d, ρ (G.anc ρ d x) = none)

/-! ### The compressed search graph `D_cmp` (pp.16–19) -/

/-- Vertices of `D_cmp`: elements, head vertices, jump vertices `x_{i,j}`, and the sink. Element
vertices `e ∉ I` and jump vertices with `2^j > depth_i(x)` carry no arcs. -/
inductive CmpV (V E : Type) (k : ℕ)
  | elem (e : E)
  | hd (v : V)
  | jump (i : Fin k) (x : V) (j : ℕ)
  | sink

/-- The (at most two) jump vertices covering a branch of length `d` from `x` towards the LCA (4.3):
`x_{i,j}` and `(p_i^{d-2^j}(x))_{i,j}` with `j = ⌊log₂ d⌋`; empty for `d = 0`. -/
def coverOf (G : Digraph V E) {k : ℕ} (ρ : Fin k → V → Option E) (i : Fin k) (x : V) (d : ℕ) :
    Finset (CmpV V E k) :=
  if d = 0 then ∅ else
    {CmpV.jump i x (Nat.log 2 d), CmpV.jump i (G.anc (ρ i) (d - 2 ^ Nat.log 2 d) x) (Nat.log 2 d)}

/-- Length of the branch from `tail e` up to the lowest common ancestor of the ends of `e` in `F i`. -/
def branchTail (G : Digraph V E) {k : ℕ} (ρ : Fin k → V → Option E) (i : Fin k) (e : E) : ℕ :=
  sInf {d | ∃ d', G.anc (ρ i) d (G.tail e) = G.anc (ρ i) d' (G.head e)}

/-- The lowest common ancestor of the ends of `e` in `F i`. -/
def lcaOf (G : Digraph V E) {k : ℕ} (ρ : Fin k → V → Option E) (i : Fin k) (e : E) : V :=
  G.anc (ρ i) (G.branchTail ρ i e) (G.tail e)

/-- Length of the branch from `head e` up to the lowest common ancestor. -/
def branchHead (G : Digraph V E) {k : ℕ} (ρ : Fin k → V → Option E) (i : Fin k) (e : E) : ℕ :=
  sInf {d | G.anc (ρ i) d (G.head e) = G.lcaOf ρ i e}

/-- The jump vertices representing the scan of `e` into `F i` (at most four; none if the ends of
`e` are not connected in `F i`). -/
def scanCover (G : Digraph V E) {k : ℕ} (F : Fin k → Finset E) (ρ : Fin k → V → Option E)
    (i : Fin k) (e : E) : Finset (CmpV V E k) :=
  if G.Conn (F i) (G.tail e) (G.head e) then
    G.coverOf ρ i (G.tail e) (G.branchTail ρ i e) ∪ G.coverOf ρ i (G.head e) (G.branchHead ρ i e)
  else ∅

/-- Which forests an element scans: all forests not containing it (`full`, p.17), or the cyclic
restriction (p.18): elements of `E ∖ I` scan only `F₁` (index `0`), elements of `F_i` scan only
`F_{i+1}` (indices mod `k`; for `k = 1` elements of `I` do not scan). -/
inductive ScanPolicy
  | full
  | cyclic

/-- `e` scans `F i` under the policy. -/
def Scans {k : ℕ} (pol : ScanPolicy) (F : Fin k → Finset E) (I : Finset E) (e : E) (i : Fin k) :
    Prop :=
  match pol with
  | .full => e ∉ F i
  | .cyclic => e ∉ F i ∧ ((e ∉ I ∧ i.val = 0) ∨ ∃ j, e ∈ F j ∧ i = cycNext j)

/-- `J(e)`: the jump vertices covering all scanned tree paths of `e`. -/
def Jset (G : Digraph V E) {k : ℕ} (pol : ScanPolicy) (F : Fin k → Finset E) (I : Finset E)
    (ρ : Fin k → V → Option E) (e : E) : Set (CmpV V E k) :=
  {x | ∃ i, Scans pol F I e i ∧ x ∈ G.scanCover F ρ i e}

/-- Arcs of `D_cmp` (table on p.18). -/
inductive CmpArc (V E : Type) (k : ℕ)
  /-- `f → head(f)⋆`, `f ∈ I`, `(-c(f), 1)`. -/
  | up (f : E)
  /-- `head(e)⋆ → x`, `e ∉ I`, `x ∈ J(e)`, `(c(e), 0)`, label `e`. -/
  | enter (e : E) (x : CmpV V E k)
  /-- `f → x`, `f ∈ I`, `x ∈ J(f)`, `(0, 0)`. -/
  | scan (f : E) (x : CmpV V E k)
  /-- `x_{i,j} → x_{i,j-1}`, `(0, 0)`. -/
  | jdown (i : Fin k) (x : V) (j : ℕ)
  /-- `x_{i,j} → (p_i^{2^{j-1}}(x))_{i,j-1}`, `(0, 0)`. -/
  | jskip (i : Fin k) (x : V) (j : ℕ)
  /-- `x_{i,0} → f_i(x)`, `(0, 0)`. -/
  | leaf (i : Fin k) (x : V)
  /-- `head(e)⋆ → z`, `e` free, `(c(e), 0)`, label `e`. -/
  | toSink (e : E)

/-- Source of an arc of `D_cmp`. -/
def cmpSrc (G : Digraph V E) {k : ℕ} : CmpArc V E k → CmpV V E k
  | .up f => .elem f
  | .enter e _ => .hd (G.head e)
  | .scan f _ => .elem f
  | .jdown i x j => .jump i x j
  | .jskip i x j => .jump i x j
  | .leaf i x => .jump i x 0
  | .toSink e => .hd (G.head e)

/-- Target of an arc of `D_cmp`. -/
def cmpTgt (G : Digraph V E) {k : ℕ} (ρ : Fin k → V → Option E) : CmpArc V E k → CmpV V E k
  | .up f => .hd (G.head f)
  | .enter _ x => x
  | .scan _ x => x
  | .jdown i x j => .jump i x (j - 1)
  | .jskip i x j => .jump i (G.anc (ρ i) (2 ^ (j - 1)) x) (j - 1)
  | .leaf i x => match ρ i x with
    | some f => .elem f
    | none => .sink
  | .toSink _ => .sink

/-- Which arcs of `D_cmp` exist, for the scan policy `pol` and the rooting `ρ`. -/
def cmpValid (G : Digraph V E) (k : ℕ) (pol : ScanPolicy) (I : Finset E) (F : Fin k → Finset E)
    (ρ : Fin k → V → Option E) : CmpArc V E k → Prop
  | .up f => f ∈ I
  | .enter e x => e ∉ I ∧ x ∈ G.Jset pol F I ρ e
  | .scan f x => f ∈ I ∧ x ∈ G.Jset pol F I ρ f
  | .jdown i x j => 0 < j ∧ 2 ^ j ≤ G.depth (ρ i) x
  | .jskip i x j => 0 < j ∧ 2 ^ j ≤ G.depth (ρ i) x
  | .leaf i x => 1 ≤ G.depth (ρ i) x ∧ ρ i x ≠ none
  | .toSink e => G.Free k I e

/-- Primary weight `w` on `D_cmp`. -/
def cmpW {k : ℕ} (c : E → ℝ) : CmpArc V E k → ℝ
  | .up f => -c f
  | .enter e _ => c e
  | .toSink e => c e
  | _ => 0

/-- Secondary length `q` on `D_cmp`. -/
def cmpQ {k : ℕ} : CmpArc V E k → ℕ
  | .up _ => 1
  | _ => 0

/-- Projection of a `D_cmp` walk to `D`: the labels `e ∉ I` (inserted after their head vertex) and
the elements of `I` immediately followed by a head vertex, in order. -/
def projCmp {k : ℕ} (as : List (CmpArc V E k)) : List E :=
  as.filterMap fun a => match a with
    | .enter e _ => some e
    | .toSink e => some e
    | .up f => some f
    | _ => none

/-! ### The potential on `D_cmp` (5.6) -/

/-- The forest-swap arcs of `D_cmp` (the arcs of the subgraph `Q`). -/
def IsQArc {k : ℕ} : CmpArc V E k → Prop
  | .scan _ _ => True
  | .jdown _ _ _ => True
  | .jskip _ _ _ => True
  | .leaf _ _ => True
  | _ => False

/-- Reachability in `Q` (paths of length zero included). -/
def QReach (G : Digraph V E) (k : ℕ) (pol : ScanPolicy) (I : Finset E) (F : Fin k → Finset E)
    (ρ : Fin k → V → Option E) (x y : CmpV V E k) : Prop :=
  ∃ as, IsWalk (G.cmpSrc) (G.cmpTgt ρ) (fun a => G.cmpValid k pol I F ρ a ∧ IsQArc a) as x y

/-- The potential (5.6): `p(v⋆) = h(v)`, `p(z) = 0`, and
`p(x) = min{-a(f) : f ∈ I, x ⇝ f in Q}` for element and jump vertices (every vertex of `Q` reaches
an element of `I`, so the minimum is over a nonempty finite set). -/
def pot (G : Digraph V E) (k : ℕ) (pol : ScanPolicy) (c : E → ℝ) (h : V → ℝ) (I : Finset E)
    (F : Fin k → Finset E) (ρ : Fin k → V → Option E) : CmpV V E k → ℝ
  | .hd v => h v
  | .sink => 0
  | x => sInf {z : ℝ | ∃ f ∈ I, G.QReach k pol I F ρ x (.elem f) ∧ z = -(G.adj c h f)}

/-- Reduced weights `w_p(x, y) = w(x, y) - p(x) + p(y)`. -/
def cmpWp (G : Digraph V E) (k : ℕ) (pol : ScanPolicy) (c : E → ℝ) (h : V → ℝ) (I : Finset E)
    (F : Fin k → Finset E) (ρ : Fin k → V → Option E) (a : CmpArc V E k) : ℝ :=
  cmpW c a - G.pot k pol c h I F ρ (G.cmpSrc a) + G.pot k pol c h I F ρ (G.cmpTgt ρ a)

end Digraph

end MinCostArbPacking.Main


