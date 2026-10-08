-- Prove2me | Definitions.Def_HyperbolicObstruction
-- name    : HyperbolicObstruction
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.772889+00:00
-- url     : https://prove2.me/theorems/a5ba3e56-3c40-455b-a251-7bb0c2195177
-- statement:
--   This block builds the vocabulary for a defined proposition (not an established theorem) asserting the existence of a finite aspherical complex with hyperbolic fundamental group that has no geometric CAT(0) action and is not homotopy equivalent to any finite complex with a locally CAT(-1) metric. A FiniteComplex is a finite abstract simplicial complex on vertices Fin n, realized by its barycentric carrier: nonnegative weight vectors summing to 1 and supported on a face, with the subspace topology. Edges are pairs of vertices forming a face, and edge paths are nonempty lists of consecutive edges; closed paths start and end at the same vertex. Disk moves rewrite a list of vertices by deleting a repeated vertex (cost 0), removing a spur a,b,a (cost 0), or replacing a,b,c by a,c across a nondegenerate triangular face (cost 1). DiskHomotopy is the reflexive, symmetric, transitive closure of these moves with costs added, and Disk(p,faces) says p reduces to a single vertex at the given triangle count. LinearDiskFilling(K,C) says every closed edge path that admits some disk has one with at most C times (length minus 1) triangles. Aspherical at a basepoint means all homotopy groups of order at least 2 are trivial. Metric notions include constant-speed segments on [0,1], geodesic spaces, CATZero via the squared-distance comparison inequality along some segment between any two points, and CATNegOne via the cosh midpoint inequality. A GeometricAction of a group on a metric space is an isometric action that is proper (finitely many group elements move a compact set to meet itself) and cocompact. NoGeometricCATZeroAction(G) says no nonempty proper complete CAT(0) space in universe u carries a geometric G-action. Word length and distance come from a finite symmetric-closed generating set, and WordHyperbolic means that for some finite generating set and some delta at least 0, the four-point inequality d(a,c)+d(b,d) <= max(d(a,b)+d(c,d), d(a,d)+d(b,c)) + 2 delta holds. CompatibleLocallyCATNegOne(K) asks for a metric inducing the polyhedron's existing topology that is geodesic and in which every point has a ball of some positive radius satisfying CATNegOne. MainStatement asserts there exist a finite complex K, basepoint x and constant C >= 0 with K connected, aspherical, linearly disk-filling with constant C, whose fundamental group at x is word hyperbolic with no geometric CAT(0) action, and such that every finite complex L homotopy equivalent to K fails CompatibleLocallyCATNegOne.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HyperbolicObstruction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HyperbolicObstruction.lean; bytes 16..6196
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI



section

section

/-!
Finite complexes are standard barycentric realizations of finite abstract
simplicial complexes. Area-counted elementary edge homotopies encode the
usual triangular disk diagrams, allowing spurs and collapsed edges. Null edge
loops (equivalently closed lifts to the universal cover) are those admitting
such a disk, without any area bound. Asphericity is vanishing of all higher
homotopy groups of this finite polyhedron. The CAT conditions use the standard
squared-distance / hyperbolic-cosh comparison formulations.
-/

noncomputable section
open scoped Topology ContinuousMap

namespace HyperbolicObstruction

structure FiniteComplex where
  n : ℕ
  complex : AbstractSimplicialComplex (Fin n)

namespace FiniteComplex

abbrev Vertex (K : FiniteComplex) := Fin K.n

def Carrier (K : FiniteComplex) :=
  {x : K.Vertex → ℝ // (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
    ∃ s ∈ K.complex.faces, ∀ i, i ∉ s → x i = 0}

instance (K : FiniteComplex) : TopologicalSpace K.Carrier :=
  inferInstanceAs (TopologicalSpace (Subtype _))

def Edge (K : FiniteComplex) (a b : K.Vertex) : Prop :=
  {a, b} ∈ K.complex.faces

def EdgePath (K : FiniteComplex) : List K.Vertex → Prop
  | [] => False
  | [_] => True
  | a :: b :: t => K.Edge a b ∧ K.EdgePath (b :: t)

def Closed (K : FiniteComplex) (p : List K.Vertex) : Prop :=
  ∃ a t, p = a :: (t ++ [a]) ∨ p = [a]

/-- An elementary disk move. A noncollapsed triangular face costs one;
    a spur or a collapsed edge costs zero. Contexts are unchanged. -/
inductive DiskMove (K : FiniteComplex) : List K.Vertex → List K.Vertex → ℕ → Prop
  | stutter (l r) (a) :
      DiskMove K (l ++ [a, a] ++ r) (l ++ [a] ++ r) 0
  | spur (l r) (a b) (h : K.Edge a b) :
      DiskMove K (l ++ [a, b, a] ++ r) (l ++ [a] ++ r) 0
  | triangle (l r) (a b c) (h : {a, b, c} ∈ K.complex.faces)
      (hne : ({a, b, c} : Finset K.Vertex).card = 3) :
      DiskMove K (l ++ [a, b, c] ++ r) (l ++ [a, c] ++ r) 1

/-- A disk certificate obtained by elementary triangle attachments/removals,
    with spurs/collapses allowed. The index is the number of triangular faces. -/
inductive DiskHomotopy (K : FiniteComplex) : List K.Vertex → List K.Vertex → ℕ → Prop
  | refl (p) : DiskHomotopy K p p 0
  | move {p q n} : DiskMove K p q n → DiskHomotopy K p q n
  | symm {p q n} : DiskHomotopy K p q n → DiskHomotopy K q p n
  | trans {p q r m n} : DiskHomotopy K p q m → DiskHomotopy K q r n →
      DiskHomotopy K p r (m + n)

def Disk (K : FiniteComplex) (p : List K.Vertex) (faces : ℕ) : Prop :=
  ∃ a, K.DiskHomotopy p [a] faces

def LinearDiskFilling (K : FiniteComplex) (C : ℝ) : Prop :=
  ∀ p, K.EdgePath p → K.Closed p → (∃ a, K.Disk p a) →
    ∃ a, K.Disk p a ∧ (a : ℝ) ≤ C * (p.length - 1 : ℕ)

def Aspherical (K : FiniteComplex) (x : K.Carrier) : Prop :=
  ∀ n : ℕ, Subsingleton (HomotopyGroup.Pi (n + 2) K.Carrier x)

end FiniteComplex

/-- A constant-speed metric segment, parametrized on [0,1]. -/
def IsSegment {X : Type*} [MetricSpace X] (γ : ℝ → X) (x y : X) : Prop :=
  γ 0 = x ∧ γ 1 = y ∧
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    dist (γ s) (γ t) = |s - t| * dist x y

def IsGeodesic (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y

/-- The CN characterization of CAT(0), with whole metric segments. -/
def CATZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y ∧
    ∀ z : X, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist z (γ t) ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
        t * (1 - t) * dist x y ^ 2

/-- The hyperbolic-cosh midpoint characterization of CAT(-1). -/
def CATNegOne (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y ∧
    ∀ z : X, Real.cosh (dist z (γ (1 / 2))) ≤
      (Real.cosh (dist z x) + Real.cosh (dist z y)) /
        (2 * Real.cosh (dist x y / 2))

/-- A proper, cocompact isometric action of a discrete group. -/
structure GeometricAction (G X : Type*) [Group G] [MetricSpace X] where
  act : G →* (X ≃ᵢ X)
  proper : ∀ C : Set X, IsCompact C →
    {g : G | ∃ x ∈ C, act g x ∈ C}.Finite
  cocompact : ∃ C : Set X, IsCompact C ∧ ∀ x : X, ∃ g : G, ∃ y ∈ C, act g y = x

universe u

def NoGeometricCATZeroAction (G : Type*) [Group G] : Prop :=
  ∀ (X : Type u) (_ : MetricSpace X), Nonempty X → ProperSpace X → CompleteSpace X →
    CATZero X → IsEmpty (GeometricAction G X)

def WordLength {G : Type*} [Group G] (S : Finset G) (g : G) : ℕ :=
  sInf {n | ∃ w : List G, w.length = n ∧
    (∀ a ∈ w, a ∈ S ∨ a⁻¹ ∈ S) ∧ w.prod = g}

def WordDistance {G : Type*} [Group G] (S : Finset G) (g h : G) : ℝ :=
  WordLength S (g⁻¹ * h)

/-- Four-point word hyperbolicity, for some finite generating set. -/
def WordHyperbolic (G : Type*) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ a b c d : G,
      WordDistance S a c + WordDistance S b d ≤
        max (WordDistance S a b + WordDistance S c d)
          (WordDistance S a d + WordDistance S b c) + 2 * δ

/-- A metric on the given finite polyhedron, not on a different topology. -/
def CompatibleLocallyCATNegOne (K : FiniteComplex) : Prop :=
  ∃ m : MetricSpace K.Carrier,
    m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace K.Carrier) ∧
    (letI := m
     IsGeodesic K.Carrier ∧ ∀ x : K.Carrier, ∃ r : ℝ, 0 < r ∧
       CATNegOne (Metric.ball x r))

/-- A finite aspherical complex with hyperbolic fundamental group, no geometric CAT(0)
action, and no homotopy equivalent finite complex admitting a locally CAT(-1) metric. -/
def MainStatement : Prop :=
  ∃ K : FiniteComplex, ∃ x : K.Carrier, ∃ C : ℝ,
    ConnectedSpace K.Carrier ∧ K.Aspherical x ∧ 0 ≤ C ∧ K.LinearDiskFilling C ∧
    NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x) ∧
    WordHyperbolic (FundamentalGroup K.Carrier x) ∧
    ∀ L : FiniteComplex, Nonempty (K.Carrier ≃ₕ L.Carrier) →
      ¬ CompatibleLocallyCATNegOne L




end HyperbolicObstruction
end
end
end
end OAI


