-- Prove2me | Definitions.Def_MatroidSensOracle_Supplement_AlphaAux
-- name    : MatroidSensOracle_Supplement_AlphaAux
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:06:35.242202+00:00
-- url     : https://prove2.me/theorems/17ccfe8a-8965-44b5-a934-a5d5d9e3be67
-- title:
--   The auxiliary graph $H+U_H$, its degree bounds $\beta$ and the projection $M'$ of §8.2.2
-- statement:
--   Let $G$ be an undirected graph, $\alpha:V\to\mathbb Z_{>0}$, $M\subseteq E$ an $\alpha$-factor of $G$, $f\ge1$, and $U$ an update. Put $f_v=\min(2f,\alpha(v))$ and let $\mathrm{del}(v)$ be the number of edges of $M$ at $v$ deleted by $U$. The multigraph $H+U_H$ has the vertices $v_1,v_2,r_v,s_v$ for $v\in V$ and the following edges, in order:
--
--   1. one layer copy of each edge $e=(a,b)$ of $G+U$: the Layer 1 copy $(a_1,b_1)$ of cost $-c(e)$ if $e$ is a surviving edge of $M$, otherwise the Layer 2 copy $(a_2,b_2)$ of cost $c(e)$;
--   2. $f_v-\mathrm{del}(v)$ zero-cost edges $v_1v_2$ for each $v$;
--   3. $f_v-\mathrm{del}(v)$ zero-cost edges $s_vr_v$ for each $v$;
--   4. for each deleted $(a,b)\in M$, the zero-cost edges $r_ar_b$, $s_aa_1$, $s_bb_1$.
--
--   The degree bound $\beta$ is $f_v$ at each of $v_1,v_2,r_v,s_v$. The projection of a set $F$ of edges of $H+U_H$ is the set of edges of $G+U$ that are surviving $M$-edges whose Layer 1 copy is not in $F$, or non-$M$ edges whose Layer 2 copy is in $F$; this is $M'=(M\setminus D)\cup A$ of p.43.
--
--   This is exactly the construction of pp.42–43, with $H$ the case $U=\emptyset$; the only formal choice is that removing "one edge" of a parallel class of interchangeable zero-cost edges lowers its multiplicity.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §8.2.2 pp.42–43 (PDF pp.45–46)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_GraphProblems

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-!
# The auxiliary graph `H + U_H`, its degree bounds `β`, and the projection `M′` of §8.2.2

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), §8.2.2, pp.42–43
(PDF pp.45–46): "Let M be the fixed initial α-factor of the graph G = (V, E) and define
f_v := min(2f, α(v)), for v ∈ V. We construct an auxiliary graph H = (V1 ∪ V2 ∪ R ∪ S, E_H), and
define its degree bounds β as follows:
• Layer 1 (drop layer): […] for each edge e = (a, b) ∈ M, add the edge (a1, b1) with cost −c(e), and
  set β(v1) = f_v. […]
• Layer 2 (add layer): […] for each edge e = (a, b) of G such that e ∉ M, add the edge (a2, b2) with
  cost +c(e), and set β(v2) = f_v. […]
• Parallel edges: For each v ∈ V, add f_v parallel edges from v1 to v2, each with cost 0.
• Budget sinks (S, R): For each v ∈ V, add two vertices s_v, r_v with degree bounds
  β(s_v) = β(r_v) = f_v. Furthermore, add f_v parallel edges between s_v and r_v, all of cost 0."
"Given an update set U ⊆ E with |U| = f, we explicitly translate it into U_H as below:
• For (a, b) ∉ M (added/removed): Apply the identical operation to (a2, b2) in Layer 2.
• For (a, b) ∈ M (deleted): Remove (a1, b1) from Layer 1; remove one edge each of the following forms
  - (a1, a2), (b1, b2), (r_a, s_a), (r_b, s_b); and finally add the following edges with zero cost -
  (r_a, r_b), (s_a, a1), (s_b, b1)."
"Given a valid β-factor F of H + U_H, we project it back to G by defining M′ := (M ∖ D) ∪ A, where A
is the set of non-M edges whose Layer 2 copy is selected, and D is the set of base M-edges that are
either selected in Layer 1 or deleted by U."

**Formalization Note.**
* `G` is an undirected input graph (edges `(a, b)` with `a < b`), `M ⊆ E` an `α`-factor of `G` given
  as a set of pairs, `U = (I, F)` an update (`F ⊆ E`; inserted edges are new edges, never in `M`).
* The vertices of `H` are `Fin 4 × V`: `(0, v) = v₁`, `(1, v) = v₂`, `(2, v) = r_v`, `(3, v) = s_v`.
* `auxGraph G α M f U` is the multigraph `H + U_H` itself, built in one step: its first edges are,
  in order, one layer copy of each edge of the multigraph `G + U` (the base `G.plus U`): the
  Layer 1 copy `(a₁, b₁)` of cost `−c(e)` for a surviving edge of `M`, the Layer 2 copy `(a₂, b₂)` of
  cost `c(e)` for every other edge of `G + U` (surviving non-`M` edges and inserted edges). Then, for
  each `v`, `f_v − del(v)` parallel edges `v₁v₂` and `f_v − del(v)` edges `s_v r_v`, where `del(v)` is
  the number of deleted `M`-edges at `v` ("remove one edge each" once per deleted `M`-edge at `v`);
  then, for each deleted `(a, b) ∈ M`, the zero-cost edges `r_a r_b`, `s_a a₁`, `s_b b₁`. Parallel
  edges are interchangeable, so which copy is removed does not matter. `H` itself is
  `auxGraph G α M f ⟨[], ∅⟩`.
* Because the first edges of `H + U_H` are the layer copies of the edges of `G + U` in order, the
  projection `M′` of a set `F` of edges of `H + U_H` is the set of edges `i` of `G + U` such that `i`
  is a surviving `M`-edge whose Layer 1 copy is not in `F`, or a non-`M` edge whose Layer 2 copy is
  in `F`. This is `(M ∖ D) ∪ A`.
-/

variable {n : ℕ}

/-- `f_v = min(2f, α(v))`. -/
def fv (α : Fin n → ℕ) (f : ℕ) (v : Fin n) : ℕ := min (2 * f) (α v)

/-- `del(v)`: the number of edges of `M` at `v` deleted by `U`. -/
def delAt (M : Finset (Fin n × Fin n)) (U : Update n) (v : Fin n) : ℕ :=
  ((U.del ∩ M).filter fun e => e.1 = v ∨ e.2 = v).card

/-- The number of surviving original edges of `G + U` (the first edges of `G.plus U`). -/
def origCount (G : InputGraph n) (U : Update n) : ℕ := (pairList n (G.E \ U.del)).length

/-- Edge `i` of `G + U` is a surviving edge of `M`. -/
def InM (G : InputGraph n) (M : Finset (Fin n × Fin n)) (U : Update n) (i : Fin (G.plus U).m) :
    Prop :=
  (i : ℕ) < origCount G U ∧ ((G.plus U).arcs.tail i, (G.plus U).arcs.head i) ∈ M

instance (G : InputGraph n) (M : Finset (Fin n × Fin n)) (U : Update n) :
    DecidablePred (InM G M U) := fun _ => by unfold InM; infer_instance

/-- The layer copies of the edges of `G + U`, in order. -/
def layerEdges (G : InputGraph n) (M : Finset (Fin n × Fin n)) (U : Update n) :
    List ((Fin 4 × Fin n) × (Fin 4 × Fin n) × ℤ) :=
  List.ofFn fun i : Fin (G.plus U).m =>
    if InM G M U i then ((0, (G.plus U).arcs.tail i), (0, (G.plus U).arcs.head i), -(G.plus U).cost i)
    else ((1, (G.plus U).arcs.tail i), (1, (G.plus U).arcs.head i), (G.plus U).cost i)

/-- The multigraph `H + U_H` (see the note). -/
def auxGraph (G : InputGraph n) (α : Fin n → ℕ) (M : Finset (Fin n × Fin n)) (f : ℕ)
    (U : Update n) : CostMultigraph (Fin 4 × Fin n) :=
  CostMultigraph.ofList (layerEdges G M U ++
    (List.finRange n).flatMap (fun v => List.replicate (fv α f v - delAt M U v) ((0, v), (1, v), 0)) ++
    (List.finRange n).flatMap (fun v => List.replicate (fv α f v - delAt M U v) ((3, v), (2, v), 0)) ++
    (pairList n (U.del ∩ M)).flatMap fun e =>
      [((2, e.1), (2, e.2), 0), ((3, e.1), (0, e.1), 0), ((3, e.2), (0, e.2), 0)])

/-- The degree bounds `β`: `f_v` at each of `v₁, v₂, r_v, s_v`. -/
def auxBeta (α : Fin n → ℕ) (f : ℕ) (p : Fin 4 × Fin n) : ℕ := fv α f p.2

/-- The projection `M′ = (M ∖ D) ∪ A` of a set `F` of edges of `H + U_H`, as edges of `G + U`. -/
def proj (G : InputGraph n) (α : Fin n → ℕ) (M : Finset (Fin n × Fin n)) (f : ℕ) (U : Update n)
    (F : Finset (Fin (auxGraph G α M f U).m)) : Finset (Fin (G.plus U).m) :=
  Finset.univ.filter fun i =>
    (InM G M U i ∧ (i : ℕ) ∉ F.image (fun j : Fin (auxGraph G α M f U).m => (j : ℕ))) ∨
      (¬ InM G M U i ∧ (i : ℕ) ∈ F.image (fun j : Fin (auxGraph G α M f U).m => (j : ℕ)))

/-- `M ⊆ E` is an `α`-factor of the simple graph `G` (given as a set of pairs). -/
def IsFactorSet (G : InputGraph n) (α : Fin n → ℕ) (M : Finset (Fin n × Fin n)) : Prop :=
  M ⊆ G.E ∧ ∀ v, (M.filter fun e => e.1 = v).card + (M.filter fun e => e.2 = v).card = α v

/-- `M` is a min-cost `α`-factor of `G`. -/
def IsMinCostFactorSet (G : InputGraph n) (α : Fin n → ℕ) (M : Finset (Fin n × Fin n)) : Prop :=
  IsFactorSet G α M ∧ ((∑ e ∈ M, G.cost e : ℤ) : WithTop ℤ) = minFactorCost G.toMultigraph α

end MatroidSensOracle.Supplement


