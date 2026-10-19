-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
-- name    : OAI_Probability_CriticalZ3_HyperedgeComparison
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:55:57.036406+00:00
-- url     : https://prove2.me/theorems/b6ae0899-97b5-4dab-b2ab-03a99287e93f
-- title:
--   Hypergraph percolation clusters and the resampling comparison
-- statement:
--   Percolation on labelled hypergraphs with independent hyperedges, and the objects of a cluster resampling argument.
--
--   1. **Clusters.** A hypergraph assigns to each label $e$ a vertex set $H_e$. In a configuration $\omega$, vertices $x,y$ are adjacent avoiding a deleted set $D$ if some open hyperedge disjoint from $D$ contains both. The cluster of $x$ is its reflexive–transitive closure, clusters of a set $S$ are the union over $S$, and $x$ meets $T$ if its cluster intersects $T$. Clusters of points outside $D$ avoid $D$.
--   2. **Resampling.** Under the product law with parameters $p$, for an observable $F$ of clusters: the mean after deleting $W$ is $\mathbb E\,F(\mathcal C_W(s))$, and resampling first draws the clusters of $S$ avoiding $U$, then the cluster of $s$ avoiding them. These define a finite transition matrix on cluster domains $\{U\ni s,\ U\cap S=\varnothing\}$.
--   3. **Root decomposition.** For listed vertices $x_1,\dots,x_n$, the first root of $x_i$ is the first $x_k$ whose cluster contains $x_i$ and avoids all earlier $x_j$. This gives cluster columns, their matrix
--   $$
--   B_{ik}=\text{column}_k(\mathbf 1)_i ,
--   $$
--   coefficients $B^{-1}\,\text{column}_k(F)$, isolation masses, expectation vectors, joint hit observables, and thinned parameters $\frac n{n+1}p$.
--   4. **Site percolation as hypergraphs.** For a graph $G$, site percolation is encoded by star hyperedges on vertices and directed edge nodes, with open adjacency requiring both endpoints open.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

/-- Full labelled hyperedges; allowing empty hyperedges causes no change to clusters. -/
abbrev Hypergraph (V : Type uV) (E : Type uE) := E → Set V

def Adj (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x y : V) : Prop :=
  ∃ e, ω e = true ∧ Disjoint (H e) D ∧ x ∈ H e ∧ y ∈ H e

def Connected (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x y : V) : Prop :=
  Relation.ReflTransGen (Adj H ω D) x y

def cluster (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) : Set V :=
  {y | Connected H ω D x y}

def clusters (H : Hypergraph V E) (ω : E → Bool) (D S : Set V) : Set V :=
  {y | ∃ x ∈ S, y ∈ cluster H ω D x}

def Meets (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) (T : Set V) : Prop :=
  ∃ y ∈ T, Connected H ω D x y

theorem clusters_contains (H : Hypergraph V E) (ω : E → Bool) (D S : Set V) :
    S ⊆ clusters H ω D S := fun x hx => ⟨x, hx, .refl⟩

theorem cluster_avoids_deleted {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x : V}
    (hx : x ∉ D) : Disjoint (cluster H ω D x) D := by
  apply Set.disjoint_left.mpr
  intro y hy
  induction hy with
  | refl => exact hx
  | @tail z y _ hzy _ =>
    obtain ⟨e, _, hd, _, hy⟩ := hzy
    exact fun hyD => Set.disjoint_left.mp hd hy hyD

theorem clusters_avoids_deleted {H : Hypergraph V E} {ω : E → Bool} {D S : Set V}
    (hSD : Disjoint S D) : Disjoint (clusters H ω D S) D := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, hy⟩ hyD
  exact Set.disjoint_left.mp (cluster_avoids_deleted
    (fun hxD => Set.disjoint_left.mp hSD hx hxD)) hy hyD

def ClusterDomain (s : V) (S : Set V) : Set (Set V) :=
  {U | s ∈ U ∧ Disjoint U S}

noncomputable def residualSample (H : Hypergraph V E) (ω : E → Bool)
    (s : V) (S U : Set V) (F : Set V → ℝ) : ℝ := by
  classical
  exact if s ∈ clusters H ω U S then 0 else
    F (cluster H ω (clusters H ω U S) s) -
    F (cluster H ω (clusters H ω U S ∪ U) s)

def earlier {n : ℕ} (x : Fin n → V) (k : Fin n) : Set V :=
  {v | ∃ j, j < k ∧ x j = v}

def firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V) (ω : E → Bool)
    (D : Set V) (k i : Fin n) : Prop :=
  Disjoint (cluster H ω D (x k)) (earlier x k) ∧ Connected H ω D (x k) (x i)

section FiniteLaw
variable [Fintype E]

noncomputable def law (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance law_probability (p : E → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (law p) := by
  unfold law
  infer_instance

noncomputable def meanAfterDelete (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (W : Set V) (F : Set V → ℝ) : ℝ :=
  ∫ ω, F (cluster H ω W s) ∂law p

noncomputable def resample (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (S : Set V) (F : Set V → ℝ) (U : Set V) : ℝ :=
  ∫ ω, meanAfterDelete H p s (clusters H ω U S) F ∂law p

noncomputable def residualMean (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (S U : Set V) (F : Set V → ℝ) : ℝ := by
  classical
  exact ∫ ω, if s ∈ clusters H ω U S then 0 else
    meanAfterDelete H p s (clusters H ω U S) F -
      meanAfterDelete H p s (clusters H ω U S ∪ U) F ∂law p

noncomputable def clusterMass (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (D S W : Set V) : ℝ :=
  ∫ ω, if clusters H ω D S = W then (1 : ℝ) else 0 ∂law p

noncomputable def column {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ)
    (i : Fin n) : ℝ := by
  classical
  exact ∫ ω, if firstRoot H x ω ∅ k i then F (cluster H ω ∅ (x k)) else 0 ∂law p

/-- A state of the alternating conditional cluster resampling chain. -/
noncomputable def nextState (H : Hypergraph V E) (s : V) (S : Set V)
    (U : ClusterDomain s S) (ω ω' : E → Bool) : ClusterDomain s S :=
  ⟨cluster H ω' (clusters H ω U.1 S) s,
    ⟨.refl, (cluster_avoids_deleted (fun hs =>
      Set.disjoint_left.mp (clusters_avoids_deleted U.2.2.symm) hs U.2.1)).mono_right
        (clusters_contains H ω U.1 S)⟩⟩

/-- The finite transition matrix for the actual two-stage cluster resampling. -/
noncomputable def resamplingTransition [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) :
    FiniteResampling.Transition (ClusterDomain s S) where
  weight U T := ∫ ω, ∫ ω', if nextState H s S U ω ω' = T then (1:ℝ) else 0 ∂law p ∂law p
  nonneg U T := integral_nonneg (fun _ => integral_nonneg (fun _ => by split_ifs <;> norm_num))
  total U := by
    classical
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    have heq : (fun ω => ∑ T : ClusterDomain s S,
        ∫ ω', if nextState H s S U ω ω' = T then (1:ℝ) else 0 ∂law p) =
        (fun _ => (1:ℝ)) := by
      funext ω
      rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp
    rw [heq]
    simp

/-- Unnormalized cluster columns d_k h_k. -/
noncomputable def baseMatrix {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => column H p x k (fun _ => 1) i

/-- Coordinates in the basis of unnormalized cluster columns. -/
noncomputable def coeff {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (baseMatrix H p x)⁻¹ *ᵥ column H p x k F

/-- The observable that a cluster contains another listed vertex. -/
noncomputable def hitsOther {n : ℕ} (x : Fin n → V) (k : Fin n) (U : Set V) : ℝ :=
  if ∃ j, j ≠ k ∧ x j ∈ U then 1 else 0

noncomputable def isolatedMass {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) : ℝ :=
  ∫ ω, if ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) then 1 else 0 ∂law p

/-- Expectation vector of a cluster observable at the listed vertices. -/
noncomputable def expectationVector {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) : Fin n → ℝ :=
  fun i => ∫ ω, F (cluster H ω ∅ (x i)) ∂law p

/-- Real probability of any event in the finite bit space. -/
noncomputable def eventProb (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) : ℝ :=
  ∫ ω, if P ω then 1 else 0 ∂law p

/-- Joint cluster-hit observable, preserving both target sets. -/
noncomputable def jointObservable (A T U : Set V) : ℝ :=
  if (∃ a ∈ A, a ∈ U) ∧ (∃ t ∈ T, t ∈ U) then 1 else 0

/-- Strictly subunit parameters approaching arbitrary permitted parameters. -/
noncomputable def thinParameter (p : E → Set.Icc (0 : ℝ) 1) (n : ℕ) (e : E) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨((n : ℝ) / ((n : ℝ) + 1)) * (p e : ℝ), by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hr0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := div_nonneg hn (by positivity)
    have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity)).mpr (by linarith)
    exact ⟨mul_nonneg hr0 (p e).2.1,
      (mul_le_of_le_one_right hr0 (p e).2.2).trans hr1.le⟩⟩

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

/-- The connector presentation uses two directed copies of each undirected
edge; duplication does not change any reachable starred vertex. Nonedges are
isolated connector nodes. -/
abbrev Node (V : Type uV) := V ⊕ (V × V)

def stars : Hypergraph (Node V) V := fun x z =>
  match z with
  | Sum.inl y => y = x
  | Sum.inr e => G.Adj e.1 e.2 ∧ (e.1 = x ∨ e.2 = x)

def OpenAdj (ω : V → Bool) (x y : V) : Prop :=
  G.Adj x y ∧ ω x = true ∧ ω y = true

def Connected (ω : V → Bool) (x y : V) : Prop :=
  ω x = true ∧ Relation.ReflTransGen (OpenAdj G ω) x y

def Meets (ω : V → Bool) (x : V) (T : Set V) : Prop :=
  ∃ y ∈ T, Connected G ω x y

/-- Predicate propagated along a hyperedge path. It explicitly retains the
site-open condition, including in the zero-edge case. -/
def Supported (ω : V → Bool) (o : V) : Node V → Prop
  | Sum.inl x => Connected G ω o x
  | Sum.inr e => G.Adj e.1 e.2 ∧ (Connected G ω o e.1 ∨ Connected G ω o e.2)

end Site

end HyperedgeComparison

end OAI


