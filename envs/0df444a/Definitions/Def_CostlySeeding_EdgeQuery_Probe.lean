-- Prove2me | Definitions.Def_CostlySeeding_EdgeQuery_Probe
-- name    : CostlySeeding_EdgeQuery_Probe
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:19.660978+00:00
-- url     : https://prove2.me/theorems/f17c0ead-6141-4217-9109-1dd600da8dde
-- title:
--   PROBE sketch and exact edge-query counter
-- statement:
--   A PROBE seed fixes the independent random choices of one run on a graph with $n$ vertices: a uniform permutation for each choice of unexplored vertex, a uniform neighbor ordering, Bernoulli choices for an edge's first chance, and independent Bernoulli choices for later queries whose answer is discarded. The deterministic function $\operatorname{probeCopy}(G,V_\rho,\tau,s)$ explores the vertices reached from the initial set $V_\rho$ and returns the edges of one truncated sketch together with the number of executions of Algorithm 2, step 10:
--
--   $$
--   (G_{\rho,\tau}(s),q_{\rho,\tau}(s)).
--   $$
--
--   The counter includes queries revealing already explored neighbors. The shared first-chance coin is symmetric in the edge endpoints, and the untruncated version uses the threshold $n+1$. This definition gives a concrete finite sample space for PROBE's probabilities and query claims.
--
--   **Formalization Note** When the sampled neighbor-index set is exhausted, the inner loop stops. The preselected Bernoulli indices and random order have the same law as the paper's Binomial count, uniform subset, and repeated uniform draws.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, pp. 9, 16–18, Definition 3–4, Algorithm 2

import Definitions.Def_CostlySeeding_EdgeQuery_Model

namespace CostlySeeding.EdgeQuery

noncomputable instance {n : ℕ} : Fintype (Equiv.Perm (Fin n)) := Fintype.ofFinite _

structure ProbeSeed (n : ℕ) where
  pick : Fin (n + 1) → Equiv.Perm (Fin n)
  order : Fin n → Equiv.Perm (Fin n)
  coin : Fin n → Fin n → Bool
  redo : Fin n → Fin n → Bool

private def probeSeedEquiv (n : ℕ) : ProbeSeed n ≃
    (Fin (n + 1) → Equiv.Perm (Fin n)) ×
      (Fin n → Equiv.Perm (Fin n)) ×
      (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) where
  toFun s := (s.pick, s.order, s.coin, s.redo)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv := by intro s; cases s; rfl
  right_inv := by intro t; rcases t with ⟨a, b, c, d⟩; rfl

noncomputable instance {n : ℕ} : Fintype (ProbeSeed n) :=
  Fintype.ofEquiv _ (probeSeedEquiv n).symm

def edgeCoin {n : ℕ} (s : ProbeSeed n) (v w : Fin n) : Bool :=
  if v ≤ w then s.coin v w else s.coin w v

structure ProbeState (n : ℕ) where
  vertices : Finset (Fin n)
  edges : Finset (Sym2 (Fin n))
  explored : Finset (Fin n)
  queries : ℕ

noncomputable def chooseRank {n : ℕ} (e : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) (h : A.Nonempty) : Fin n :=
  e.symm ((A.image e).min' (h.image e))

noncomputable def componentSize {n : ℕ} (st : ProbeState n) (v : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun u =>
    u ∈ st.vertices ∧
      (SimpleGraph.fromEdgeSet (st.edges : Set (Sym2 (Fin n)))).Reachable v u).card

noncomputable def orderedNeighbors {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (s : ProbeSeed n) (X : Finset (Fin n)) (v : Fin n) :
    List (Fin n) :=
  (((Finset.univ : Finset (Fin n)).filter fun w =>
    G.Adj v w ∧ if w ∈ X then s.redo v w else edgeCoin s v w).toList).mergeSort
      (fun a b => s.order v a ≤ s.order v b)

noncomputable def probeNeighbors {n : ℕ} (v : Fin n) (tau : ℕ) (X : Finset (Fin n)) :
    List (Fin n) → ProbeState n → ProbeState n
  | [], st => st
  | w :: ws, st =>
    if componentSize st v < tau then
      let st' :=
        if w ∈ X then { st with queries := st.queries + 1 }
        else { st with vertices := insert w st.vertices,
                       edges := insert s(v, w) st.edges,
                       queries := st.queries + 1 }
      probeNeighbors v tau X ws st'
    else st

noncomputable def probeLoop {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (tau : ℕ) (s : ProbeSeed n) :
    ℕ → ProbeState n → ProbeState n
  | 0, st => st
  | fuel + 1, st =>
    let U := st.vertices \ st.explored
    if h : U.Nonempty then
      let v := chooseRank (s.pick (Fin.ofNat (n + 1) (n - (fuel + 1)))) U h
      let X := insert v st.explored
      let st' := probeNeighbors v tau X (orderedNeighbors G s X v)
        { st with explored := X }
      probeLoop G tau s fuel st'
    else st

noncomputable def probeCopy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (Vrho : Finset (Fin n)) (tau : ℕ) (s : ProbeSeed n) :
    Finset (Sym2 (Fin n)) × ℕ :=
  let st := probeLoop G tau s n
    { vertices := Vrho, edges := ∅, explored := ∅, queries := 0 }
  (st.edges, st.queries)

end CostlySeeding.EdgeQuery


