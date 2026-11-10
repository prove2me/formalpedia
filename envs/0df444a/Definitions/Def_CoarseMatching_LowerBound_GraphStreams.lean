-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_GraphStreams
-- name    : CoarseMatching_LowerBound_GraphStreams
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:34:31.592648+00:00
-- url     : https://prove2.me/theorems/6f5e5518-c6fb-44f2-8802-4f3a93ca57bf
-- title:
--   Simple graphs, matching and cover values, and graph streams
-- statement:
--   Let $G$ be a simple graph on $n$ labeled vertices. Its matching number $\operatorname{mm}(G)$ is the maximum number of edges in an ordinary matching, using the published common matching definition. Its vertex cover number is
--
--   $$\operatorname{vc}(G)=\min\{|C|:C\text{ meets every edge of }G\}.$$
--
--   The full vertex set is a cover, so the minimum exists, including for the empty graph. Edge updates insert a pair of distinct vertices. A legal edge stream inserts each undirected edge once. A legal vertex stream announces each vertex once, listing only its neighbors that arrived earlier. The represented graph is the undirected union of these updates. A public Boolean coloring specifies the bipartition, and every edge must cross its two parts.
--
--   These definitions give graph values computed from actual edges and arbitrary adversarial arrival orders. Lower bounds already on duplicate-free streams apply to algorithms that also support reinsertion.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §1.1 and §4.1, printed pp.1,11 (PDF pp.2,12). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Mathlib
import Definitions.Def_CatalyticMatching_General_Matching

namespace CoarseMatching.LowerBound
noncomputable section

/-- Kol, STOC 2027 submission #1135, §1.1, printed p.1 / PDF p.2.
Maximum number of edges in an ordinary matching, using the published common definition. -/
abbrev mm {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  CatalyticMatching.General.matchingNumber G

/-- Minimum cardinality of an actual vertex cover. The full vertex set is feasible,
so the bounded finite infimum is attained, also for the empty graph. -/
def vc {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Nat.find (show ∃ k : ℕ, ∃ C : Finset (Fin n), C.card = k ∧
    G.IsVertexCover (C : Set (Fin n)) from
    ⟨n, Finset.univ, by simp, by simp [SimpleGraph.IsVertexCover]⟩)

inductive Arrival where
  | edge | vertex
  deriving DecidableEq

/-- A single insertion or a whole arriving vertex and its earlier neighbors. -/
abbrev Update (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Finset (Fin n))

/-- The directed edges announced by an update. -/
def announces {n : ℕ} (u : Update n) (x y : Fin n) : Prop :=
  match u with
  | .inl e => x = e.1 ∧ y = e.2
  | .inr v => x = v.1 ∧ y ∈ v.2

/-- The union graph of the insertions, with no parallel edges or loops. -/
def streamGraph {n : ℕ} (s : List (Update n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun x y => ∃ u ∈ s, announces u x y)

/-- Legal arbitrary-order edge arrival (each undirected edge once), or vertex
arrival: each vertex appears once, with neighbors only among preceding vertices. -/
def Legal {n : ℕ} (mode : Arrival) (s : List (Update n)) : Prop :=
  match mode with
  | .edge => (∀ u ∈ s, ∃ x y, u = Sum.inl (x,y) ∧ x ≠ y) ∧
      (s.filterMap (fun u => match u with
        | .inl (x,y) => some (s(x,y) : Sym2 (Fin n))
        | .inr _ => none)).Nodup
  | .vertex => ∃ vs : List (Fin n × Finset (Fin n)),
      s = vs.map Sum.inr ∧ (vs.map Prod.fst).Nodup ∧
      (∀ v : Fin n, v ∈ vs.map Prod.fst) ∧
      ∀ i (v : Fin n × Finset (Fin n)), vs[i]? = some v →
        ∀ x ∈ v.2, x ∈ (vs.take i).map Prod.fst

/-- The public bipartition is actual input data, available to the algorithm. -/
def Respects {n : ℕ} (color : Fin n → Bool) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y, G.Adj x y → color x ≠ color y

end
end CoarseMatching.LowerBound


