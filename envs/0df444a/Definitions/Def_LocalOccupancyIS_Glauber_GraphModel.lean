-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_GraphModel
-- name    : LocalOccupancyIS_Glauber_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:57:01.443869+00:00
-- url     : https://prove2.me/theorems/223bcab2-0dd0-44a7-886c-3ef9cd82429f
-- title:
--   Finite independent sets, biclique density and local occupancy
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. A configuration is a Boolean function on $V$ satisfying the published independent-set predicate; its size is the number of occupied vertices. The count $N_t(G)$ is the number of unordered pairs of disjoint $t$-element vertex sets with every cross edge present, regardless of edges inside either part. Density and its hereditary neighborhood version mean
--
--   $$2tN_t(F)\le b|V(F)|$$
--
--   for $F=G$ and, respectively, for every induced subgraph of every open neighborhood. Degree bounds, actual maximum degree and average degree retain their usual finite meanings. For fugacity $\lambda>0$, $Z_G(\lambda)=\sum_{I\in\mathcal I(G)}\lambda^{|I|}$ and $E_G(\lambda)$ is the finite expectation under the published hard-core law. Writing $p=\lambda/(1+\lambda)$, positive local occupancy parameters satisfy
--
--   $$\beta p/Z_F(\lambda)+\gamma E_F(\lambda)\ge1$$
--
--   on every induced neighborhood subgraph, including the empty one. These are shared input notions for the mission; no occupancy or density assertion is built into the graph type.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), §1.1, equation (1), equation (7), p. 3–5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=3

import Mathlib
import Definitions.Def_HardCoreBochner_hcChain

open scoped BigOperators

namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- All feasible Boolean configurations, including the empty configuration. -/
abbrev State (G : SimpleGraph V) := {σ : V → Bool // MarkovMixing.IsHardcore G σ}

def size (σ : V → Bool) : ℕ := (Finset.univ.filter (fun v => σ v = true)).card

def nbrSize (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (σ : V → Bool) : ℕ :=
  (G.neighborFinset u |>.filter (fun v => σ v = true)).card

/-- An unordered pair of disjoint t-sets; internal edges are permitted. -/
def bicliques (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : Finset (Finset (Finset V)) :=
  (Finset.univ.powerset.filter (fun A : Finset V => A.card = t)).powerset.filter
    (fun C => C.card = 2 ∧ ∀ A ∈ C, ∀ B ∈ C, A ≠ B →
      Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)

def Density (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) (b : ℝ) : Prop :=
  (2 * t * (bicliques G t).card : ℝ) ≤ b * Fintype.card V

def HereditaryDensity (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) (b : ℝ) : Prop :=
  ∀ u : V, ∀ A : Finset V, A ⊆ G.neighborFinset u →
    Density (G.induce (↑A : Set V)) t b

def DegreeBound (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : Prop :=
  ∀ v, G.degree v ≤ Δ

def MaximumDegree (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) : Prop :=
  DegreeBound G Δ ∧ ∃ v, G.degree v = Δ

def avgDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (∑ v, (G.degree v : ℝ)) / Fintype.card V

/-- Partition function, a finite sum over all feasible states. -/
def partition (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) : ℝ :=
  ∑ σ : State G, lam ^ size σ.val

def expectation {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, ν x * f x

def occupiedMean (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) : ℝ :=
  expectation (HardCoreBochner.hcLaw G lam) (fun σ => size σ.val)

def p (lam : ℝ) : ℝ := lam / (1 + lam)

def LocalOccupancy (G : SimpleGraph V) [DecidableRel G.Adj] (lam β γ : ℝ) : Prop :=
  0 < β ∧ 0 < γ ∧ ∀ u : V, ∀ A : Finset V, A ⊆ G.neighborFinset u →
    β * p lam / partition (G.induce (↑A : Set V)) lam +
      γ * occupiedMean (G.induce (↑A : Set V)) lam ≥ 1

end
end LocalOccupancyIS.Glauber


