-- Prove2me | Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
-- name    : DvorakNorin2018_HavenCloudConfiguration
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-13T18:11:38.449194+00:00
-- url     : https://prove2.me/theorems/541ce03e-17a1-4036-bb9b-1820a75498ff
-- title:
--   Havens and the cloud configuration of Lemma 7
-- statement:
--   A haven of order $k$ chooses a nonempty component of $G-W$ for each deletion set $W$ of size less than $k$, with any two chosen components touching. The interface specifies connected sets, components, touching, balanced separations of every induced subgraph, and the lexicographic minimum that first minimizes the chosen haven component and then the deletion-set size. It also defines deletion of a component in ambient vertex notation and the active vertices of a cloud (hungry or saturated vertices). No separator-to-treewidth theorem or cloud-existence assertion is included.
-- source:
--   Dvorak and Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.1 (havens), Lemma 7 and its proof, PDF pp. 6-7.

import Definitions.Def_DvorakNorin2018_CloudNormalization
set_option autoImplicit false
open scoped Classical BigOperators
namespace StableMSR.Recovery.Havens
open TreewidthApprox.Pushed
variable {V : Type} [DecidableEq V]
/-- A nonempty vertex set with a path inside it between every two vertices. -/
def ConnectedSet (G : SimpleGraph V) (C : Finset V) : Prop :=
  C.Nonempty ∧ ∀ x ∈ C, ∀ y ∈ C, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ C

/-- A component of `G - W`: connected, avoids `W`, and has no edge to another
vertex outside `W`. This includes the nonemptiness of a component. -/
structure IsFlap (G : SimpleGraph V) (W C : Finset V) : Prop where
  connected : ConnectedSet G C
  avoids : Disjoint W C
  closed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∉ W → y ∈ C

/-- Two connected sets touch when they intersect or an edge joins them. -/
def Touch (G : SimpleGraph V) (C D : Finset V) : Prop :=
  (∃ v, v ∈ C ∧ v ∈ D) ∨ ∃ x ∈ C, ∃ y ∈ D, G.Adj x y

/-- The standard haven definition: a component choice for every deletion set
of size less than the order, and any two chosen components touch. -/
structure Haven (G : SimpleGraph V) (k : ℕ) (β : Finset V → Finset V) : Prop where
  flap : ∀ W, W.card < k → IsFlap G W (β W)
  touch : ∀ W W', W.card < k → W'.card < k → Touch G (β W) (β W')

/-- Every induced subgraph has a separation of order at most `a`, with each
exclusive side containing at most two thirds of its vertices. -/
def HasBalancedSeparations (G : SimpleGraph V) (a : ℕ) : Prop :=
  ∀ U : Finset V, ∃ L S R : Finset V,
    IsPartition3 U L S R ∧ NoEdge G L R ∧ S.card ≤ a ∧
    3 * L.card ≤ 2 * U.card ∧ 3 * R.card ≤ 2 * U.card

/-- Lexicographic choice used in the first paragraph of Dvořák–Norin Lemma7:
minimize the haven component, then the deletion-set cardinality. -/
structure IsMinimumCut (β : Finset V → Finset V) (m : ℕ) (W : Finset V) : Prop where
  card_le : W.card ≤ m
  component_min : ∀ Y, Y.card ≤ m → (β W).card ≤ (β Y).card
  cut_min : ∀ Y, Y.card ≤ m → (β Y).card = (β W).card → W.card ≤ Y.card

/-- Delete the chosen haven component while retaining ambient vertex names. -/
def outsideGraph {V : Type} (G : SimpleGraph V) (B : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ B ∧ y ∉ B
  symm := ⟨by intro x y h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro x h; exact G.ne_of_adj h.1 rfl⟩

noncomputable def activeVertices {V : Type} [Fintype V] (W : Finset V) (p : TameCloud.Data V) : Finset V :=
  Finset.univ.filter (fun v => p.1 v = 1 ∨ TameCloud.Hungry W p v)


end StableMSR.Recovery.Havens


