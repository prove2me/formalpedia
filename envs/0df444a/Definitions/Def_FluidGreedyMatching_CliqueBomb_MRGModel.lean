-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_MRGModel
-- name    : FluidGreedyMatching_CliqueBomb_MRGModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:23.790662+00:00
-- url     : https://prove2.me/theorems/cbe8db9a-0e37-4c5c-bfae-56b575096396
-- title:
--   MRG on finite simple graphs
-- statement:
--   Let $G$ be any finite simple graph, with vertex set $V$. A state consists of an active set $U\subseteq V$ and a set $M$ of unordered selected edges. Initially $(U,M)=(V,\varnothing)$. If $U$ is nonempty, sample an actor $v$ uniformly from $U$. When $v$ has active neighbors, MRG samples a neighbor $w$ uniformly conditional on this state and actor, selects $\{v,w\}$, and deletes both endpoints. With no active neighbor it deletes $v$ alone. An empty active set is absorbing. The RDO variant uses a fixed strict linear preference order for each actor and selects its least active neighbor in that order.
--
--   Repeated composition of this probability kernel defines the state law after $t$ steps. The output law is the law of $M$ after $|V|$ steps, when every run has terminated. The MRG expectation is the finite sum of edge cardinality against this output law. Its benchmark $\nu(G)$ is the finite maximum of edge cardinalities of the native matching subgraphs of $G$.
--
--   $$\alpha_{\rm MRG}=\inf_{G:\nu(G)>0}\frac{\mathbb E|M_{\rm MRG}(G)|}{\nu(G)}.$$
--
--   The infimum uses graphs on $\mathrm{Fin}(N)$ for every natural $N$, covering all finite simple graphs up to relabeling. This supplies the actual algorithm and benchmark for the goal. Empty graphs and isolated vertices are allowed; only the approximation infimum excludes zero matching number. No distribution or optimum is supplied as an input.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Definition 1.1, p. 2; Sections 2 and 2.1, pp. 5–6

import Mathlib

set_option autoImplicit false

namespace FluidGreedyMatching.CliqueBomb

noncomputable section

/-- Active vertices and the (unordered) edges selected so far. -/
abbrev RunState (V : Type) := Finset V × Finset (Sym2 V)

/-- `none` is MRG; `some orders` is RDO with the specified strict preference orders.
Smaller elements in an order are preferred. -/
abbrev NeighborRule (V : Type) := Option (V → LinearOrder V)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Active neighbors, including sparse gadget edges. -/
def activeNeighbors (G : SimpleGraph V) (U : Finset V) (v : V) : Finset V := by
  classical
  exact U.filter (G.Adj v)

/-- One genuine conditional sampling step; the empty active set is absorbing. -/
def stepLaw (G : SimpleGraph V) (rule : NeighborRule V) (S : RunState V) :
    PMF (RunState V) := by
  classical
  exact if hU : S.1.Nonempty then
    (PMF.uniformOfFinset S.1 hU).bind fun v =>
      let N := activeNeighbors G S.1 v
      if hN : N.Nonempty then
        let partners : PMF V := match rule with
          | none => PMF.uniformOfFinset N hN
          | some orders => by
              letI : LinearOrder V := orders v
              exact PMF.pure (N.min' hN)
        partners.map fun w => (S.1.erase v |>.erase w, insert s(v, w) S.2)
      else PMF.pure (S.1.erase v, S.2)
    else PMF.pure S

/-- The law after exactly t steps, frozen after termination. -/
def runLaw (G : SimpleGraph V) (rule : NeighborRule V) : ℕ → PMF (RunState V)
  | 0 => PMF.pure (Finset.univ, ∅)
  | t + 1 => (runLaw G rule t).bind (stepLaw G rule)

/-- At most |V| steps are needed. The output is the actual selected edge set. -/
def outputLaw (G : SimpleGraph V) (rule : NeighborRule V := none) :
    PMF (Finset (Sym2 V)) :=
  (runLaw G rule (Fintype.card V)).map Prod.snd

/-- A finite sum, so nonintegrability cannot give a default-zero expectation. -/
def expectedSize (G : SimpleGraph V) : ℝ :=
  ∑ M : Finset (Sym2 V), ((outputLaw G) M).toReal * (M.card : ℝ)

/-- Maximum edge cardinality over native Mathlib matching subgraphs. -/
def matchingNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun M : G.Subgraph => M.IsMatching)).sup
    (fun M => M.edgeSet.ncard)

def expectedRatio (G : SimpleGraph V) : ℝ := expectedSize G / matchingNumber G

/-- Finite labeled graphs of all sizes cover all finite simple graphs up to isomorphism.
The nonempty bounded set contains K₂'s ratio and lies in [0,1]. -/
def approximationRatio : ℝ :=
  sInf {r : ℝ | ∃ (N : ℕ) (G : SimpleGraph (Fin N)),
    0 < matchingNumber G ∧ r = expectedRatio G}

end
end FluidGreedyMatching.CliqueBomb


