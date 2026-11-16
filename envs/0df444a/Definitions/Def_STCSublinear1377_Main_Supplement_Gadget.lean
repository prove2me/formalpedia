-- Prove2me | Definitions.Def_STCSublinear1377_Main_Supplement_Gadget
-- name    : STCSublinear1377_Main_Supplement_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:20:53.336548+00:00
-- url     : https://prove2.me/theorems/2a493dde-420a-40d1-9667-f71cad674f07
-- title:
--   Restricted vertex-disjoint paths, the gadget graph H_A and weighted spanning tree congestion
-- statement:
--   A **restricted disjoint-path instance** (§4, p.16) is a connected simple graph $Q$ of maximum degree at most three with pairs $(s_1,t_1),\dots,(s_p,t_p)$ whose $2p$ terminals are distinct, such that a vertex has degree one if and only if it is a terminal. It is a **YES instance** if there are simple paths $P_i$ from $s_i$ to $t_i$ that are mutually vertex-disjoint.
--
--   For an integer $A$, the weighted graph $H_A$ keeps the edges of $Q$ with weight one and adds, for each pair, $A$ new vertices $w_{i1},\dots,w_{iA}$ with
--
--   $$s_iw_{ij}\ \text{of weight }1,\qquad w_{ij}t_i\ \text{of weight }A+1\qquad(1\le j\le A).\tag{4.1}$$
--
--   For a spanning tree $R$, $c_w(H,R,e)$ is the total weight of graph edges whose tree path uses $e$ (the fundamental cut of $e$), $c_w(H,R)=\max_{e\in E(R)}c_w(H,R,e)$ and $\mathrm{STC}_w(H)=\min_R c_w(H,R)$. Instances, trees and routings have fixed binary encodings.
--
--   **Formalization Note** $H_A$ has vertex set `Fin (n + p·A)`: the vertices of $Q$ keep their names and $w_{ij}$ is $n+iA+j$ (0-based). $\mathrm{STC}_w$ is an attained minimum over the finite set of spanning trees, explicitly zero if there is none.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, §4, (4.1) and the definitions of c_w and STC_w, PDF/printed p.16

import Definitions.Def_STCSublinear1377_Main_DataMachine
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Degree of `v` in the simple graph of the table `q`. -/
noncomputable def tdeg {n : ℕ} (q : Table n) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun u => (tableGraph q).Adj v u)).card

/-- The `2p` terminals `s₁, t₁, …, s_p, t_p`. -/
def terminalsOf {n : ℕ} (pairs : List (Fin n × Fin n)) : List (Fin n) :=
  pairs.flatMap (fun p => [p.1, p.2])

/-- The restricted disjoint-path instance of Section 4: `Q` connected and simple, maximum degree
at most three, the `2p` terminals distinct, and the degree-one vertices exactly the terminals. -/
def IsRestrictedInstance {n : ℕ} (q : Table n) (pairs : List (Fin n × Fin n)) : Prop :=
  isInput q ∧ (∀ v, tdeg q v ≤ 3) ∧ (terminalsOf pairs).Nodup ∧
    ∀ v, tdeg q v = 1 ↔ v ∈ terminalsOf pairs

/-- A simple path of `Q` from `s` to `t`, as its vertex sequence. -/
def IsQPath {n : ℕ} (q : Table n) (s t : Fin n) (p : List (Fin n)) : Prop :=
  p.head? = some s ∧ p.getLast? = some t ∧
    p.IsChain (fun u v => (tableGraph q).Adj u v) ∧ p.Nodup

/-- A routing: the `i`-th path joins `s_i` to `t_i`, and the paths are mutually vertex-disjoint. -/
def IsRouting {n : ℕ} (q : Table n) (pairs : List (Fin n × Fin n))
    (paths : List (List (Fin n))) : Prop :=
  List.Forall₂ (fun p st => IsQPath q st.1 st.2 p) paths pairs ∧
    paths.Pairwise (fun p p' => ∀ v ∈ p, v ∉ p')

/-- YES instance: all pairs can be joined by mutually vertex-disjoint paths. -/
def IsYes {n : ℕ} (q : Table n) (pairs : List (Fin n × Fin n)) : Prop :=
  ∃ paths, IsRouting q pairs paths

/-- The auxiliary vertex with name `x ≥ n` is `w_{ij}` for `i = (x - n) / A`, `j = (x - n) % A`;
this returns its pair `(s_i, t_i)`. -/
def auxPair (n : ℕ) (pairs : List (Fin n × Fin n)) (A x : ℕ) : Option (Fin n × Fin n) :=
  if n ≤ x then pairs[(x - n) / A]? else none

/-- Weight of the gadget edge between the auxiliary vertex `w` and the original vertex `v`:
`1` to `s_i`, `A + 1` to `t_i`, zero otherwise (4.1). -/
def auxLink (n : ℕ) (pairs : List (Fin n × Fin n)) (A w v : ℕ) : ℕ :=
  match auxPair n pairs A w with
  | some st => if v = st.1.val then 1 else if v = st.2.val then A + 1 else 0
  | none => 0

/-- Edge weights of `H_A`: unit weight on the edges of `Q`, and the gadget edges (4.1). -/
noncomputable def gadgetWeight {n : ℕ} (q : Table n) (pairs : List (Fin n × Fin n)) (A : ℕ)
    (x y : Fin (n + pairs.length * A)) : ℕ := by
  classical
  exact if hx : x.val < n then
      (if hy : y.val < n then (if (tableGraph q).Adj ⟨x.val, hx⟩ ⟨y.val, hy⟩ then 1 else 0)
        else auxLink n pairs A y.val x.val)
    else (if y.val < n then auxLink n pairs A x.val y.val else 0)

/-- The weighted graph `H_A` on `n + pA` vertices: the vertices of `Q` keep their names and
`w_{ij}` is the vertex `n + iA + j`. -/
noncomputable def gadget {n : ℕ} (q : Table n) (pairs : List (Fin n × Fin n)) (A : ℕ) :
    WeightedGraph (n + pairs.length * A) :=
  ⟨Finset.univ, fun x y => decide (gadgetWeight q pairs A x y ≠ 0),
    fun x y => (gadgetWeight q pairs A x y : ℝ)⟩

/-- Weighted spanning tree congestion `STC_w`: an attained minimum of the weighted congestion over
the finite set of spanning trees; explicitly zero if there is none. -/
noncomputable def stcW {n : ℕ} (f : WeightedGraph n) : ℝ := by
  classical
  let values := ((Finset.univ : Finset (Table n)).filter f.tree).image f.congestion
  exact if h : values.Nonempty then values.min' h else 0

/-- Binary encoding of a disjoint-path instance together with the integer `A`. -/
def instanceBits {n : ℕ} (q : Table n) (pairs : List (Fin n × Fin n)) (A : ℕ) : List Bool :=
  natBits n ++ tableBits q ++ natBits pairs.length ++
    pairs.flatMap (fun p => natBits p.1.val ++ natBits p.2.val) ++ natBits A

/-- Binary encoding of a list of paths. -/
def pathsBits {n : ℕ} (paths : List (List (Fin n))) : List Bool :=
  natBits paths.length ++ paths.flatMap (fun p => natBits p.length ++ p.flatMap (fun v => natBits v.val))

end STCSublinear1377.Main.Supplement


