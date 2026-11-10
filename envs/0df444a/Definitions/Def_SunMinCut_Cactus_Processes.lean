-- Prove2me | Definitions.Def_SunMinCut_Cactus_Processes
-- name    : SunMinCut_Cactus_Processes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:23:09.64764+00:00
-- url     : https://prove2.me/theorems/64490350-ecff-4b66-8029-f113b74323fd
-- title:
--   CAPFOREST labels, first-fit forests, height process, Poisson arrivals and the auxiliary graphs of the local searches
-- statement:
--   **CAPFOREST labels (App. B.1).** For a maximum-adjacency (legal) ordering $\sigma$ and a non-loop record $e$ with earlier endpoint $a$ and later endpoint $b$, `capforestLabel` is $q_e$ = (capacity from $b$ to the vertices selected before $a$) + (capacities of the records joining $a$ and $b$ with index $\le e$): the label of $b$ right after $e$ increases it, the records at a selected vertex being scanned in index order.
--
--   **First-fit forests (§2.2).** A stream of edge copies (unordered vertex pairs) is processed in order; each copy goes to the first of the initially empty forests $B_1,B_2,\dots$ in which its endpoints are disconnected (`firstFit`, `forestB`). `completeCount` is $R$, the number of layers $j\ge1$ that are spanning trees (connected). `layerCrossing` counts the copies of a layer crossing a cut; `goodLayers arr t S` counts the layers among the first $t$ that are spanning trees crossing $S$ at most twice.
--
--   **Height process (Lemma 2.5).** A state is a tree with a height on each edge. `HStep`: for an arriving copy $f=uv$, choose a path edge $g$ of minimum height $h$ on the tree path from $u$ to $v$, delete $g$ and insert $f$ with height $h+1$. `HRun arr states`: `states 0` is a spanning tree with all heights $0$ and each step is an `HStep` for the next arrival. `heightAtLeast s j` is the graph of tree edges of height $\ge j$.
--
--   **Poisson arrivals (§2.2).** One uniform $U_{e,i}\in[0,1]$ per record and index, independent (`arrivalMeasure`). Record $e$ arrives at the times $\sum_{i\le k}-\log U_{e,i}/r_e$, $k=0,1,\dots$: a Poisson process of rate $r_e$, independent over records. `stream G c0 U t` lists the copies arrived by time $t$ chronologically (ties broken by record and index) with rates $q_e=\min(w_e,c_0)/c_0$; `completeAt` is $R(t)$.
--
--   **Local searches (§2.1, §2.3).** `coverMeasure` is the law of the arrival uniforms together with one sampling uniform $V_{j,e}$ per tree index $j$ and record $e$. `sourceTree … j` is the layer $B_j$ at horizon $t$. With $p_e=\min\{w_e,d_0\}/(2d_0)$ (equation (2)), record $e$ is sampled iff $V_{j,e}<p_e$; `auxGraph` is the unit auxiliary multigraph $G_T$: the sampled records plus a separate copy of every tree edge. `IsSmallBond E S`: $\{S,V\setminus S\}$ is a nontrivial cut with at most two crossing edges of $E$ and both shores connected by their inside edges — exactly the bridges and two-edge bonds that the cactus of three-edge-connected components of $E$ represents (p. 7). `Covered G c0 ω t S`: for some $1\le j\le\min(R(t),t)$ the cut $S$ is a small bond of the auxiliary graph of source tree $j$.
--
--   **Formalization Note** On the probability-zero events where some $U=0$ (a zero waiting time) or infinitely many arrivals occur before $t$ (`Set.ncard` is then $0$) the definitions take default values; probabilities are unaffected.
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, §2.1 p. 7, §2.2 pp. 9–11, §2.3 p. 11, App. B.1 p. 33

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph

open MeasureTheory

namespace SunMinCut.Cactus

variable {n m : ℕ}

/-! ### The CAPFOREST labels of a maximum-adjacency ordering (App. B.1, p. 33) -/

open Classical in
/-- The label `q_e` of a non-loop record `e` in the maximum-adjacency ordering `σ` (`σ k` is the
`(k+1)`-st selected vertex), with the edges at the selected vertex scanned in record order.
Let `a` be the earlier and `b` the later endpoint of `e`. Before `a` is selected, the label of
`b` is its capacity to the vertices selected before `a`; scanning the records joining `a` and
`b` in index order increases it, and `q_e` is the label right after the increase by `e`. -/
noncomputable def capforestLabel (G : Graph n m) (σ : Fin n ≃ Fin n) (e : Fin m) : ℝ :=
  let x := (Quot.out (G.ends e)).1
  let y := (Quot.out (G.ends e)).2
  let a := if σ.symm x < σ.symm y then x else y
  let b := if σ.symm x < σ.symm y then y else x
  (∑ e' ∈ Finset.univ.filter (fun e' => ∃ z, G.ends e' = s(z, b) ∧ σ.symm z < σ.symm a),
      G.u e') +
    ∑ e' ∈ Finset.univ.filter (fun e' => G.ends e' = G.ends e ∧ e' ≤ e), G.u e'

/-! ### First-fit forests (§2.2, pp. 9–10) -/

/-- The forest of layer `j` of an assignment of edge copies to layers. -/
def layerGraph (asg : List (Sym2 (Fin n) × ℕ)) (j : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {f | (f, j) ∈ asg}

/-- The first layer `j ≥ 1` whose forest does not yet connect the endpoints of the copy `f`. -/
noncomputable def firstFitLayer (asg : List (Sym2 (Fin n) × ℕ)) (f : Sym2 (Fin n)) : ℕ :=
  sInf {j | 1 ≤ j ∧ ¬ (layerGraph asg j).Reachable (Quot.out f).1 (Quot.out f).2}

/-- First fit (§2.2, p. 9): process the copies of the stream in order, assigning each to the first
of the initially empty forests `B₁, B₂, …` in which its endpoints are disconnected. The result
lists every copy with its layer, in stream order. -/
noncomputable def firstFit (arr : List (Sym2 (Fin n))) : List (Sym2 (Fin n) × ℕ) :=
  arr.foldl (fun asg f => asg ++ [(f, firstFitLayer asg f)]) []

/-- The forest `B_j` after the stream `arr`. -/
noncomputable def forestB (arr : List (Sym2 (Fin n))) (j : ℕ) : SimpleGraph (Fin n) :=
  layerGraph (firstFit arr) j

open Classical in
/-- `R`, the number of complete layers (layers `B_j`, `j ≥ 1`, that are spanning trees, i.e.
connected). A layer beyond the stream length is empty. -/
noncomputable def completeCount (arr : List (Sym2 (Fin n))) : ℕ :=
  ((Finset.Icc 1 arr.length).filter fun j => (forestB arr j).Connected).card

open Classical in
/-- The number of copies of layer `j` crossing the cut with shore `S`. -/
noncomputable def layerCrossing (arr : List (Sym2 (Fin n))) (j : ℕ) (S : Finset (Fin n)) : ℕ :=
  (firstFit arr).countP fun p => decide (p.2 = j ∧ CrossesShore S p.1)

open Classical in
/-- The number of the first `t` layers that are spanning trees crossing the cut `S` at most
twice. -/
noncomputable def goodLayers (arr : List (Sym2 (Fin n))) (t : ℕ) (S : Finset (Fin n)) : ℕ :=
  ((Finset.Icc 1 t).filter fun j => (forestB arr j).Connected ∧ layerCrossing arr j S ≤ 2).card

/-! ### The height representation (Lemma 2.5, p. 9) -/

/-- A changing spanning tree with a height on every edge (heights of non-edges are unused). -/
structure HTree (n : ℕ) where
  /-- The current tree. -/
  T : SimpleGraph (Fin n)
  /-- The height of each edge. -/
  ht : Sym2 (Fin n) → ℕ

/-- One arrival `f = uv`: let `h` be the smallest height on the current tree path from `u` to
`v`; delete any path edge `g` of height `h` and insert `f` at height `h + 1`. -/
def HStep (s : HTree n) (f : Sym2 (Fin n)) (s' : HTree n) : Prop :=
  ∃ u v, f = s(u, v) ∧ ∃ p : s.T.Walk u v, p.IsPath ∧
    ∃ g ∈ p.edges, (∀ g' ∈ p.edges, s.ht g ≤ s.ht g') ∧
      s'.T = s.T.deleteEdges {g} ⊔ SimpleGraph.fromEdgeSet {f} ∧
      s'.ht = Function.update s.ht f (s.ht g + 1)

/-- `states` is a run of the height process on the stream `arr`: it starts from any spanning tree
on `V` (possibly virtual) with all heights zero and performs `HStep` for each arrival. -/
def HRun (arr : List (Sym2 (Fin n))) (states : ℕ → HTree n) : Prop :=
  (states 0).T.IsTree ∧ (∀ f, (states 0).ht f = 0) ∧
    ∀ k (hk : k < arr.length), HStep (states k) (arr[k]'hk) (states (k + 1))

/-- The current tree edges of height at least `j`. -/
def heightAtLeast (s : HTree n) (j : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {f | f ∈ s.T.edgeSet ∧ j ≤ s.ht f}

/-! ### Independent Poisson arrivals (§2.2, p. 9) -/

/-- The randomness of the arrival processes: one uniform `U_{e,i} ∈ [0, 1]` per record and index. -/
abbrev ArrivalTape (m : ℕ) := Fin m × ℕ → unitInterval

/-- Its law: independent uniforms. -/
noncomputable def arrivalMeasure (m : ℕ) : Measure (ArrivalTape m) :=
  Measure.infinitePi fun _ : Fin m × ℕ => (volume : Measure unitInterval)

/-- The `k`-th arrival time (`k = 0, 1, …`) of the rate-`r_e` Poisson process of record `e`:
the sum of the waiting times `−log U_{e,i} / r_e`, `i ≤ k`, which are independent exponentials
of rate `r_e`. -/
noncomputable def arrivalTime (r : Fin m → ℝ) (U : ArrivalTape m) (e : Fin m) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), -Real.log (U (e, i)) / r e

/-- `N_e(t)`, the number of arrivals of record `e` up to time `t`. -/
noncomputable def arrivalCount (r : Fin m → ℝ) (U : ArrivalTape m) (e : Fin m) (t : ℝ) : ℕ :=
  Set.ncard {k | arrivalTime r U e k ≤ t}

open Classical in
/-- The copies `(e, k)` arrived by time `t`, in chronological order (ties, which have probability
zero, broken by record and index). -/
noncomputable def arrivals (r : Fin m → ℝ) (U : ArrivalTape m) (t : ℝ) : List (Fin m × ℕ) :=
  ((List.finRange m).flatMap fun e => (List.range (arrivalCount r U e t)).map fun k => (e, k)).mergeSort
    fun a b => decide (arrivalTime r U a.1 a.2 < arrivalTime r U b.1 b.2 ∨
      (arrivalTime r U a.1 a.2 = arrivalTime r U b.1 b.2 ∧ (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))))

/-- The stream of edge copies arrived by time `t` when record `e` arrives at rate `q_e`
(`q = (rates G c0).u`), as endpoint pairs, in chronological order. -/
noncomputable def stream (G : Graph n m) (c0 : ℝ) (U : ArrivalTape m) (t : ℝ) :
    List (Sym2 (Fin n)) :=
  (arrivals (rates G c0).u U t).map fun a => G.ends a.1

/-- `R(t)`, the number of complete layers at time `t`. -/
noncomputable def completeAt (G : Graph n m) (c0 : ℝ) (U : ArrivalTape m) (t : ℝ) : ℕ :=
  completeCount (stream G c0 U t)

/-! ### Local searches on the source trees (§2.1 and §2.3, pp. 7, 11) -/

/-- The randomness of Lemma 2.8: the arrival uniforms and one sampling uniform per tree index
and record. -/
abbrev CoverTape (m : ℕ) := (Fin m × ℕ) ⊕ (ℕ × Fin m) → unitInterval

/-- Its law: independent uniforms. -/
noncomputable def coverMeasure (m : ℕ) : Measure (CoverTape m) :=
  Measure.infinitePi fun _ : (Fin m × ℕ) ⊕ (ℕ × Fin m) => (volume : Measure unitInterval)

/-- The sampling probability `p_e = min{w_e, d0}/(2 d0)` of (2), p. 7. -/
noncomputable def sampleProb (G : Graph n m) (T : SimpleGraph (Fin n)) (e : Fin m) : ℝ :=
  min (G.u e) (d0 G T) / (2 * d0 G T)

open Classical in
/-- The unit auxiliary multigraph `G_T` (§2.1, p. 7): the records sampled by the uniforms
`V e` (record `e` is sampled iff `V e < p_e`), plus a separate copy of every edge of `T`. -/
noncomputable def auxGraph (G : Graph n m) (T : SimpleGraph (Fin n)) (V : Fin m → unitInterval) :
    List (Sym2 (Fin n)) :=
  ((List.finRange m).filter fun e => decide (((V e : unitInterval) : ℝ) < sampleProb G T e)).map
      G.ends ++ T.edgeFinset.toList

/-- The edges of the multigraph `E` inside the vertex set `X` connect `X`. -/
def SideConnected (E : List (Sym2 (Fin n))) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, (SimpleGraph.fromEdgeSet {f | f ∈ E ∧ ∀ z ∈ f, z ∈ X}).Reachable x y

open Classical in
/-- The cut `{S, V ∖ S}` is a bridge or a two-edge bond of the multigraph `E` (at most two
crossing edges, both shores connected): exactly the cuts represented by the cactus obtained by
contracting the three-edge-connected components of `E` (§2.1, p. 7). -/
def IsSmallBond (E : List (Sym2 (Fin n))) (S : Finset (Fin n)) : Prop :=
  Nontriv S ∧ E.countP (fun f => decide (CrossesShore S f)) ≤ 2 ∧
    SideConnected E S ∧ SideConnected E (Finset.univ \ S)

/-- The `j`-th source tree of the uncapped Poisson construction at horizon `t`: layer `B_j`. -/
noncomputable def sourceTree (G : Graph n m) (c0 : ℝ) (ω : CoverTape m) (t : ℝ) (j : ℕ) :
    SimpleGraph (Fin n) :=
  forestB (stream G c0 (fun a => ω (Sum.inl a)) t) j

/-- Some retained auxiliary cactus represents the cut `S`: for some `1 ≤ j ≤ min(R(t), t)` (the
first at most `t` complete source trees), the cut is a bridge or two-edge bond of the auxiliary
graph of the `j`-th source tree sampled with the uniforms of index `j`. -/
def Covered (G : Graph n m) (c0 : ℝ) (ω : CoverTape m) (t : ℕ) (S : Finset (Fin n)) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ min (completeAt G c0 (fun a => ω (Sum.inl a)) t) t ∧
    IsSmallBond (auxGraph G (sourceTree G c0 ω t j) fun e => ω (Sum.inr (j, e))) S

end SunMinCut.Cactus


