-- Prove2me | Definitions.Def_CannonGeometricAction
-- name    : CannonGeometricAction
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.518187+00:00
-- url     : https://prove2.me/theorems/8d0ec184-2666-478a-9361-492f8b83d704
-- statement:
--   For a group G, CayleyData consists of a finite set of generators closed under inverses whose undirected multiplication Cayley graph is connected. The thin-triangles condition asserts that some integer δ ≥ 0 bounds the distance from every vertex of one shortest edge-path side of every triangle to a vertex on one of the other two shortest sides. A based geodesic ray is a sequence r: ℕ → G starting at the identity and satisfying d(r(i),r(j)) = |i−j| in the graph metric. Two such rays are equivalent when d(r(n),s(n)) is bounded by one fixed integer for all n; this is proved to be an equivalence relation. The boundary is the quotient of based rays by this relation. Given a topology on G, rays inherit the subspace topology from the product G^ℕ, and the boundary receives the quotient topology; these definitions do not require the thin-triangles condition or impose a discrete topology on G. The two-sphere is the unit sphere in real Euclidean three-space. Hyperbolic three-space is the upper half-space of triples x with x₂ > 0, with its usual subspace topology and distance arcosh(1 + Σᵢ(xᵢ−yᵢ)²/(2x₂y₂)). Its full isometry group is the subgroup of homeomorphisms preserving this distance, allowing orientation reversal. For a homomorphism ρ from G into this isometry group, properness means that each compact K meets its translate ρ(g)K for only finitely many g. Cocompactness means that the translates of some compact K cover all of hyperbolic three-space.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CannonGeometricAction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CannonGeometricAction.lean; bytes 16..3563
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
namespace CannonRelease

universe u

structure CayleyData (G : Type u) [Group G] where
  generators : Finset G
  symmetric : ∀ x ∈ generators, x⁻¹ ∈ generators
  connected : (SimpleGraph.mulCayley (generators : Set G)).Connected

def CayleyData.graph {G : Type u} [Group G] (D : CayleyData G) : SimpleGraph G :=
  SimpleGraph.mulCayley (D.generators : Set G)

/-- A uniform thinness constant for geodesic triangles in the Cayley graph. -/
def CayleyData.ThinTriangles {G : Type u} [Group G] (D : CayleyData G) : Prop :=
  ∃ δ : ℕ, ∀ x y z : G,
    ∀ p : D.graph.Walk x y, ∀ q : D.graph.Walk y z, ∀ r : D.graph.Walk z x,
      p.length = D.graph.dist x y → q.length = D.graph.dist y z →
      r.length = D.graph.dist z x →
      ∀ a ∈ p.support, ∃ b ∈ q.support ++ r.support, D.graph.dist a b ≤ δ

/-- Based geodesic rays, parametrized at integer times. -/
def BasedRay {G : Type u} [Group G] (D : CayleyData G) :=
  {r : ℕ → G // r 0 = 1 ∧ ∀ i j, D.graph.dist (r i) (r j) = Nat.dist i j}

instance {G : Type u} [Group G] [TopologicalSpace G] (D : CayleyData G) :
    TopologicalSpace (BasedRay D) := inferInstanceAs (TopologicalSpace {r : ℕ → G //
      r 0 = 1 ∧ ∀ i j, D.graph.dist (r i) (r j) = Nat.dist i j})

/-- Finite synchronous distance, equivalent to asymptoticity for based rays. -/
def raySetoid {G : Type u} [Group G] (D : CayleyData G) : Setoid (BasedRay D) where
  r r s := ∃ C : ℕ, ∀ n, D.graph.dist (r.val n) (s.val n) ≤ C
  iseqv := by
    constructor
    · intro r
      exact ⟨0, fun n => by simp⟩
    · rintro r s ⟨C, hC⟩
      exact ⟨C, fun n => by rw [SimpleGraph.dist_comm]; exact hC n⟩
    · rintro r s t ⟨C, hC⟩ ⟨E, hE⟩
      refine ⟨C + E, fun n => ?_⟩
      exact le_trans ((D.connected (r.val n) (s.val n)).dist_triangle_left (t.val n))
        (Nat.add_le_add (hC n) (hE n))

def Boundary {G : Type u} [Group G] (D : CayleyData G) := Quotient (raySetoid D)

instance {G : Type u} [Group G] [TopologicalSpace G] (D : CayleyData G) :
    TopologicalSpace (Boundary D) :=
  inferInstanceAs (TopologicalSpace (Quotient (raySetoid D)))

abbrev SphereTwo := {x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere 0 1}

/-- The upper-half-space model of hyperbolic three-space. -/
def HyperbolicThree := {x : Fin 3 → ℝ // 0 < x 2}

instance : TopologicalSpace HyperbolicThree :=
  inferInstanceAs (TopologicalSpace {x : Fin 3 → ℝ // 0 < x 2})

def hyperbolicDist (x y : HyperbolicThree) : ℝ :=
  Real.arcosh (1 + (∑ i : Fin 3, (x.val i - y.val i) ^ 2) / (2 * x.val 2 * y.val 2))

/-- The full isometry group, including orientation-reversing isometries. -/
def hyperbolicIsometries : Subgroup (HyperbolicThree ≃ₜ HyperbolicThree) where
  carrier := {f | ∀ x y, hyperbolicDist (f x) (f y) = hyperbolicDist x y}
  one_mem' := by
    change ∀ x y, hyperbolicDist x y = hyperbolicDist x y
    intros
    rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    simpa using (hf (f.symm x) (f.symm y)).symm

abbrev H3Isom := ↥hyperbolicIsometries

def ProperAction {G : Type u} [Group G] (ρ : G →* H3Isom) : Prop :=
  ∀ K : Set HyperbolicThree, IsCompact K →
    {g : G | ∃ x ∈ K, (ρ g).val x ∈ K}.Finite

def CocompactAction {G : Type u} [Group G] (ρ : G →* H3Isom) : Prop :=
  ∃ K : Set HyperbolicThree, IsCompact K ∧
    ∀ x : HyperbolicThree, ∃ g : G, ∃ y ∈ K, (ρ g).val y = x



end CannonRelease
end
end OAI


