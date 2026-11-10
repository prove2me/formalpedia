-- Prove2me | Definitions.Def_SunMinCut_Cactus_Intervals
-- name    : SunMinCut_Cactus_Intervals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:23:52.447106+00:00
-- url     : https://prove2.me/theorems/72109b7f-1ba2-4207-b039-558c47a3c5cf
-- title:
--   Interval objective, Euler unfolding of a cactus, compact interval descriptions, tree labels and inverse Ackermann function
-- statement:
--   **Interval objective (App. G.1).** An objective graph on ordered vertices $0,\dots,k$ has $M$ records $(u,v,w)$; `Valid` requires $u<v\le k$ and $w\ge0$. $d_i=\sum_{u<i\le v}w_{uv}$ ($=w(\delta\{i,\dots,k\})$), $h_{ij}=\sum_{u<i,\ j\le v}w_{uv}$, $F(i,j)=d_i+d_j-2h_{ij}$ (42). Keys are compared lexicographically: $(d_a,a)<(d_b,b)$. `IsCandidate a b` ($1\le a<b\le k$): $a$ is the nearest smaller key to the left of $b$ (its key is smaller and every key strictly between is larger than $b$'s), or $b$ is the nearest smaller key to the right of $a$.
--
--   **Euler unfolding (App. G.2).** $K^+$ is $K$ with each bridge doubled. An `Unfolding K π r k` is an Euler circuit of $K^+$ starting at $\pi(r)$: positions $0,\dots,k$ with vertices `occ p`, a bijection between positions and edges of $K^+$ with edge $p$ joining positions $p$ and $p+1 \bmod (k+1)$, and representatives $\iota(x)$ with `occ (ι x) = x`, $\iota(\pi(r))=0$. `interval k a b` is $\{a,\dots,b\}$; a position set is **coherent** if it contains all or none of the occurrences of each cactus vertex; `posShore` is $\pi^{-1}$ of the vertices occurring in it. $W=\sum_e w_e$, $P=W+1$. The objective graph $J$ (`objJ`) on the positions maps each record $xy$ of $G$ to $\iota(\pi(x))\iota(\pi(y))$ with weight $w_{xy}$ and joins every position $p$ to $\iota(\mathrm{occ}\,p)$ by a copy link of weight $P$ (a loop, which lies in no cut, for representatives and for records inside a bag).
--
--   **Compact descriptions (App. G.1, p. 46).** An `IntervalDesc` lists a ring `occ` of cactus vertices at positions $0,\dots,k$, explicit pairs $(i,j)$ denoting $[i,j-1]$, suffixes $i$ denoting $[i,k]$, and increasing lists $p_1<\dots<p_a$ denoting every $[p_x,p_y-1]$, $x<y$. `D.shores π` is the set of original shores $\pi^{-1}(\mathrm{occ}[a..b])$ of its intervals with $1\le a\le b\le k$. `code`, `optIntervalCode` give flat real encodings.
--
--   **Minimal shores and labels (App. G.3).** For a family $\mathcal F$ of shores, `feasible 𝓕 r Z` is the set of members avoiding the root $r$ and containing the object $Z$ (a vertex $\{v\}$ or a record's endpoint set, `IsObject`); `IsLeast'` means a member contained in every member. A `TreeLabel` $(\text{type},x,y,j)$ denotes the subtree $T_{j,x}$ (vertices whose path from $r$ in $T_j$ passes through $x$) for type 1, and $T_{j,x}\triangle T_{j,y}$ for type 2. `CanonicalLabels`: each object gets the absence label iff it has no feasible minimum-cut shore, otherwise a well-formed label of its smallest one, and labels denoting the same shore are identical.
--
--   **Inverse Ackermann.** `ackT i j` is Tarjan's $A(i+1,j)$: $A(1,j)=2^j$, $A(i,1)=A(i-1,2)$, $A(i,j)=A(i-1,A(i,j-1))$; $\alpha_{UF}(s,n)=\min\{i\ge1: A(i,\max(1,\lfloor s/n\rfloor))>\log_2 n\}$.
--
--   **Formalization Note** $\alpha_{UF}$ is an `sInf` over a set that is always nonempty. Other inverse-Ackermann conventions differ by additive constants.
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, App. G.1 pp. 45–46, App. G.2 p. 48, App. G.3 pp. 49–50

import Mathlib
import Definitions.Def_SunMinCut_Cactus_CactusGraph

namespace SunMinCut.Cactus

/-! ### Minimum interval cuts (App. G.1, p. 45) -/

/-- An objective graph on the ordered vertices `0, 1, …, k` with `M` weighted records, each
oriented `u < v` (App. G.1, p. 45). -/
structure ObjGraph (k M : ℕ) where
  /-- The smaller endpoint of each record. -/
  u : Fin M → ℕ
  /-- The larger endpoint of each record. -/
  v : Fin M → ℕ
  /-- The weight of each record. -/
  w : Fin M → ℝ

variable {k M : ℕ}

/-- The records are oriented `u < v ≤ k` and their weights are nonnegative. -/
def ObjGraph.Valid (J : ObjGraph k M) : Prop := ∀ r, J.u r < J.v r ∧ J.v r ≤ k ∧ 0 ≤ J.w r

open Classical in
/-- `d_i = w(δ{i, …, k}) = Σ_{u < i ≤ v} w_uv`. -/
noncomputable def ObjGraph.d (J : ObjGraph k M) (i : ℕ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => J.u r < i ∧ i ≤ J.v r), J.w r

open Classical in
/-- `h_ij = Σ_{u < i < j ≤ v} w_uv`. -/
noncomputable def ObjGraph.h (J : ObjGraph k M) (i j : ℕ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => J.u r < i ∧ j ≤ J.v r), J.w r

/-- `F(i, j) = d_i + d_j − 2 h_ij` (42), the weight of the cut of `{i, …, j − 1}`. -/
noncomputable def ObjGraph.F (J : ObjGraph k M) (i j : ℕ) : ℝ := J.d i + J.d j - 2 * J.h i j

/-- The lexicographic key order `(d_a, a) < (d_b, b)`. -/
def ObjGraph.KeyLt (J : ObjGraph k M) (a b : ℕ) : Prop := J.d a < J.d b ∨ (J.d a = J.d b ∧ a < b)

/-- `(a, b)` with `1 ≤ a < b ≤ k` is a candidate pair: `a` is the nearest smaller key to the left
of `b`, or `b` the nearest smaller key to the right of `a`. -/
def ObjGraph.IsCandidate (J : ObjGraph k M) (a b : ℕ) : Prop :=
  1 ≤ a ∧ a < b ∧ b ≤ k ∧
    ((J.KeyLt a b ∧ ∀ c, a < c → c < b → J.KeyLt b c) ∨
     (J.KeyLt b a ∧ ∀ c, a < c → c < b → J.KeyLt a c))

/-! ### The Euler unfolding of a cactus (App. G.2, p. 48) -/

/-- The edges of `K⁺`: the edges of `K`, plus a second copy of each bridge. -/
abbrev PlusEdge {q e : ℕ} (K : MGraph q e) := Fin e ⊕ {i : Fin e // K.IsBridge i}

/-- The ends of an edge of `K⁺`. -/
def plusEnds {q e : ℕ} (K : MGraph q e) : PlusEdge K → Sym2 (Fin q)
  | .inl i => K.ends i
  | .inr i => K.ends i.1

/-- An Euler unfolding of `(K, π)` from the root `r` (App. G.2, p. 48): an Euler circuit of `K⁺`
that starts at `π(r)`, its vertex occurrences numbered `0, …, k` (`occ p` is the cactus vertex at
position `p`, and the `p`-th circuit edge joins positions `p` and `p + 1 mod (k + 1)`), and a
representative occurrence `ι(x)` of every cactus vertex with `ι(π(r)) = 0`. -/
structure Unfolding {n q e : ℕ} (K : MGraph q e) (π : Fin n → Fin q) (r : Fin n) (k : ℕ) where
  /-- The vertex at each position. -/
  occ : Fin (k + 1) → Fin q
  /-- The circuit: each edge of `K⁺` is used exactly once. -/
  circ : Fin (k + 1) ≃ PlusEdge K
  /-- Consecutive positions are joined by the circuit edges. -/
  circ_ends : ∀ p : Fin (k + 1), plusEnds K (circ p) = s(occ p, occ (p + 1))
  /-- The circuit starts at `π(r)`. -/
  occ_zero : occ 0 = π r
  /-- The representative occurrences. -/
  ι : Fin q → Fin (k + 1)
  /-- A representative is an occurrence of its vertex. -/
  occ_ι : ∀ x, occ (ι x) = x
  /-- The root's representative is position `0`. -/
  ι_root : ι (π r) = 0

/-- The interval `{a, …, b}` of positions. -/
def interval (k a b : ℕ) : Finset (Fin (k + 1)) := Finset.univ.filter fun p => a ≤ p.1 ∧ p.1 ≤ b

/-- A set of positions is coherent: it separates the copies of no cactus vertex. -/
def Coherent {n q e k : ℕ} {K : MGraph q e} {π : Fin n → Fin q} {r : Fin n}
    (U : Unfolding K π r k) (I : Finset (Fin (k + 1))) : Prop :=
  ∀ x, (∀ p, U.occ p = x → p ∈ I) ∨ (∀ p, U.occ p = x → p ∉ I)

open Classical in
/-- The original shore of a set of positions: `π⁻¹` of the cactus vertices occurring there. -/
noncomputable def posShore {n q k : ℕ} (occ : Fin (k + 1) → Fin q) (π : Fin n → Fin q)
    (I : Finset (Fin (k + 1))) : Finset (Fin n) :=
  lift π (I.image occ)

/-- `W = Σ_e w_e` (App. G.2, p. 48). -/
noncomputable def totalWeight {n m : ℕ} (G : Graph n m) : ℝ := ∑ e, G.u e

/-- The objective graph `J` on the positions (App. G.2, p. 48): each record `xy` of `G` mapped to
`ι(π(x)) ι(π(y))` with its weight (a resulting loop lies in no cut, which is dropping it), and a
copy link of weight `P = W + 1` joining every position to its vertex's representative (a loop
for the representative itself). -/
noncomputable def objJ {n m q e k : ℕ} (G : Graph n m) {K : MGraph q e} {π : Fin n → Fin q}
    {r : Fin n} (U : Unfolding K π r k) : CombOpt.MinCut.CapGraph (Fin (k + 1)) (Fin m ⊕ Fin (k + 1)) where
  ends := fun x => match x with
    | .inl x => Sym2.map (fun v => U.ι (π v)) (G.ends x)
    | .inr p => s(p, U.ι (U.occ p))
  u := fun x => match x with
    | .inl x => G.u x
    | .inr _ => totalWeight G + 1

/-! ### Compact descriptions of interval families (App. G.1, pp. 46–47) -/

/-- A compact description over a ring of positions `0, …, k` (App. G.1, p. 46): the vertex at
each position, explicit pairs `(i, j)` denoting `[i, j − 1]`, suffixes `i` denoting `[i, k]`, and
increasing lists `p₁ < ⋯ < p_a` denoting every `[p_x, p_y − 1]` with `x < y`. -/
structure IntervalDesc where
  /-- The cactus vertex at each position `0, …, k`. -/
  occ : List ℕ
  /-- Explicit pairs. -/
  pairs : List (ℕ × ℕ)
  /-- Suffixes. -/
  suffixes : List ℕ
  /-- Boundary lists. -/
  lists : List (List ℕ)

/-- The closed intervals `[a, b]` denoted by a description. -/
def IntervalDesc.intervals (D : IntervalDesc) : Set (ℕ × ℕ) :=
  {ab | (∃ ij ∈ D.pairs, ab = (ij.1, ij.2 - 1) ∧ ij.1 < ij.2) ∨
        (∃ i ∈ D.suffixes, ab = (i, D.occ.length - 1)) ∨
        (∃ L ∈ D.lists, L.Pairwise (· < ·) ∧ ∃ x y : ℕ, ∃ hx : x < L.length, ∃ hy : y < L.length,
          x < y ∧ ab = (L[x], L[y] - 1))}

open Classical in
/-- The original shore of the interval `[a, b]` of the ring `occ`: the vertices `v` with `π(v)`
occurring at some position in `[a, b]`. -/
noncomputable def ringShore {n q : ℕ} (occ : List ℕ) (π : Fin n → Fin q) (a b : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ p, a ≤ p ∧ p ≤ b ∧ occ[p]? = some (π v : ℕ)

/-- The original shores denoted by a description: those of its intervals `[a, b]` with
`1 ≤ a ≤ b ≤ k`. -/
noncomputable def IntervalDesc.shores {n q : ℕ} (D : IntervalDesc) (π : Fin n → Fin q) :
    Set (Finset (Fin n)) :=
  {S | ∃ ab ∈ D.intervals, 1 ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < D.occ.length ∧
    S = ringShore D.occ π ab.1 ab.2}

/-- The flat real encoding of a list of naturals, preceded by its length. -/
def natsList (L : List ℕ) : List ℝ := ((L.length : ℕ) : ℝ) :: L.map fun x => ((x : ℕ) : ℝ)

/-- The flat real encoding of a description: `occ`, the pairs, the suffixes, the lists, each
preceded by its length. -/
def IntervalDesc.code (D : IntervalDesc) : List ℝ :=
  natsList D.occ ++ ((D.pairs.length : ℕ) : ℝ) ::
    (D.pairs.map fun ij => [((ij.1 : ℕ) : ℝ), ((ij.2 : ℕ) : ℝ)]).flatten ++
  natsList D.suffixes ++ ((D.lists.length : ℕ) : ℝ) :: (D.lists.map natsList).flatten

/-- The flat real encoding of an optional interval: `[0, 0, 0]` for absence, `[1, a, b]` for
`[a, b]`. -/
def optIntervalCode : Option (ℕ × ℕ) → List ℝ
  | none => [0, 0, 0]
  | some ab => [1, ((ab.1 : ℕ) : ℝ), ((ab.2 : ℕ) : ℝ)]

/-! ### Minimal shores of vertices and edges (App. G.3, p. 49) -/

/-- The feasible shores for the object `Z` (a vertex `{v}` or the endpoint set of a record) among
a family `𝓕` of shores: the members avoiding the root `r` and containing `Z`. -/
def feasible {n : ℕ} (𝓕 : Set (Finset (Fin n))) (r : Fin n) (Z : Finset (Fin n)) :
    Set (Finset (Fin n)) :=
  {S | S ∈ 𝓕 ∧ r ∉ S ∧ Z ⊆ S}

/-- `S` is the smallest member of the family `𝓐`: it belongs to `𝓐` and is contained in every
member. -/
def IsLeast' {n : ℕ} (𝓐 : Set (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  S ∈ 𝓐 ∧ ∀ S' ∈ 𝓐, S ⊆ S'

open Classical in
/-- The endpoint set of a record. -/
noncomputable def recordEnds {n m : ℕ} (G : Graph n m) (e : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun v => v ∈ G.ends e

/-- A canonical tree label `(type, x, y, j)` (App. G.3, p. 49): `type = 1` labels the subtree
`T_{j,x}`, `type = 2` labels `T_{j,x} △ T_{j,y}`. -/
structure TreeLabel where
  /-- `1` or `2`: one or two tree edges. -/
  type : ℕ
  /-- The child endpoint of the first tree edge. -/
  x : ℕ
  /-- The child endpoint of the second tree edge (unused for type `1`). -/
  y : ℕ
  /-- The index of the source tree. -/
  j : ℕ

open Classical in
/-- `T_x`, the vertices of the subtree of `x` when the tree `T` is rooted at `r`: those whose tree
path from `r` passes through `x`. -/
noncomputable def subtree {n : ℕ} (T : SimpleGraph (Fin n)) (r x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ p : T.Walk r v, p.IsPath ∧ x ∈ p.support

/-- A label is well formed for the trees `T₀, …, T_{L-1}` rooted at `r`: its type is `1` or `2`,
its tree index is `< L` and its vertices are non-root vertices (children of tree edges). -/
def TreeLabel.Valid {n : ℕ} (L : ℕ) (r : Fin n) (τ : TreeLabel) : Prop :=
  (τ.type = 1 ∨ τ.type = 2) ∧ τ.j < L ∧ τ.x < n ∧ τ.y < n ∧ τ.x ≠ r ∧ (τ.type = 2 → τ.y ≠ r)

open Classical in
/-- The shore denoted by a label: `T_{j,x}` or `T_{j,x} △ T_{j,y}`. -/
noncomputable def TreeLabel.shore {n L : ℕ} (T : Fin L → SimpleGraph (Fin n)) (r : Fin n)
    (τ : TreeLabel) : Finset (Fin n) :=
  if h : τ.j < L ∧ τ.x < n ∧ τ.y < n then
    if τ.type = 1 then subtree (T ⟨τ.j, h.1⟩) r ⟨τ.x, h.2.1⟩
    else symmDiff (subtree (T ⟨τ.j, h.1⟩) r ⟨τ.x, h.2.1⟩) (subtree (T ⟨τ.j, h.1⟩) r ⟨τ.y, h.2.2⟩)
  else ∅

/-- The flat real encoding of an optional label; absence (the common label `V`) is `[0, 0, 0, 0]`. -/
def labelCode : Option TreeLabel → List ℝ
  | none => [0, 0, 0, 0]
  | some τ => [((τ.type : ℕ) : ℝ), ((τ.x : ℕ) : ℝ), ((τ.y : ℕ) : ℝ), ((τ.j : ℕ) : ℝ)]

/-- The objects of App. G.3: a vertex `{v}` or the endpoint set of a record. -/
def IsObject {n m : ℕ} (G : Graph n m) (Z : Finset (Fin n)) : Prop :=
  (∃ v, Z = {v}) ∨ ∃ e, Z = recordEnds G e

/-- The labels are the canonical labels of App. G.3 (p. 49) for the trees `T` rooted at `r`: each
vertex `{v}` and each record's endpoint set `Z` gets the absence label iff no root-avoiding
minimum-cut shore contains `Z`, and otherwise a well-formed label of the smallest such shore;
two objects whose labels denote the same shore have identical labels. -/
def CanonicalLabels {n m L : ℕ} (G : Graph n m) (r : Fin n) (T : Fin L → SimpleGraph (Fin n))
    (lv : Fin n → Option TreeLabel) (le : Fin m → Option TreeLabel) : Prop :=
  let ok : Finset (Fin n) → Option TreeLabel → Prop := fun Z o =>
    (o = none ↔ feasible {S | IsMinCut G S} r Z = ∅) ∧
    ∀ τ, o = some τ → τ.Valid L r ∧ IsLeast' (feasible {S | IsMinCut G S} r Z) (τ.shore T r)
  let all : List (Option TreeLabel) := List.ofFn lv ++ List.ofFn le
  (∀ v, ok {v} (lv v)) ∧ (∀ e, ok (recordEnds G e) (le e)) ∧
  ∀ o ∈ all, ∀ o' ∈ all, ∀ τ τ', o = some τ → o' = some τ' → τ.shore T r = τ'.shore T r → τ = τ'

/-! ### The inverse Ackermann function -/

/-- Tarjan's Ackermann function, `ackT i j = A(i + 1, j)`: `A(1, j) = 2^j`,
`A(i, 1) = A(i − 1, 2)`, `A(i, j) = A(i − 1, A(i, j − 1))` (`j = 0` is unused). -/
def ackT : ℕ → ℕ → ℕ
  | 0, j => 2 ^ j
  | _ + 1, 0 => 1
  | i + 1, 1 => ackT i 2
  | i + 1, j + 2 => ackT i (ackT (i + 1) (j + 1))

/-- The inverse Ackermann function `α_UF(s, n) = min{i ≥ 1 : A(i, max(1, ⌊s/n⌋)) > log₂ n}`
(Tarjan's two-argument form). -/
noncomputable def alphaUF (s n : ℕ) : ℕ :=
  sInf {i | 1 ≤ i ∧ Nat.log 2 n < ackT (i - 1) (max 1 (s / n))}

end SunMinCut.Cactus


