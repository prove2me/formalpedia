-- Prove2me | Definitions.Def_PolycyclicRecognition
-- name    : PolycyclicRecognition
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:05.091006+00:00
-- url     : https://prove2.me/theorems/08fe8533-a1f1-471f-8432-4a16a6d18fc9
-- statement:
--   This block sets up definitions for coarse and geometric recognition of polycyclic groups. A map f between groups is group-bornologous if every finite set S of differences x⁻¹y is sent into a finite set T of differences (f x)⁻¹(f y). A GroupCoarseEquivalence consists of maps in both directions, each group-bornologous, such that the sets of left errors x⁻¹·invFun(toFun x) and right errors y⁻¹·toFun(invFun y) are finite. A cyclic step H ≤ K requires H to be normal in K with cyclic quotient K/H, and a CyclicSeries of length n from H to K is a chain of subgroups starting at H, ending at K, with each consecutive pair a cyclic step. A group is polycyclic if for some n it has such a series from the trivial subgroup to the whole group, and virtually polycyclic if it has a finite-index subgroup that is polycyclic. A uniform lattice Λ in a topological group G is a discrete subgroup for which some compact set K satisfies: every g equals γk with γ in Λ and k in K. A SimplyConnectedSolvableLieModel bundles a finite-dimensional real normed model space with a Hausdorff, second countable, simply connected, solvable group carrier that is a smooth Lie group modeled on it. IsFiniteCovolumeLattice says Λ is discrete and G/Λ carries a G-invariant probability measure for the Borel σ-algebra. LinearMetricChains on a pseudometric space record a positive step size, a nonnegative slope and a nonnegative error such that any two points x, y are joined by a chain of some length n ≤ slope·d(x,y)+error with consecutive points at distance at most the step size. A ProperChainMetric on a topological group is a metric compatible with the topology that is proper, left-invariant under isometric multiplication, and admits such chains. For linear functionals χᵢ on a real vector space, heightKernel is the intersection of their kernels (the whole space for an empty family), HeightSpace is the quotient by it, and heightProjection is the quotient map. A TriangularAdjoint structure on a real Lie algebra of dimension n is a basis in which ad x is an upper triangular matrix for every x, and its character i sends x to the ith basis coordinate of [x, bᵢ], giving the diagonal adjoint entries as linear functionals. IsGroupExponential characterizes a map Exp from the Lie algebra to the group by Exp 0 = 1, Exp((s+t)v) = Exp(sv)Exp(tv), and the curve t ↦ Exp(tv) having derivative v at t = 0. ModelIsUnimodular says that the Borel Haar measure on a simply connected solvable Lie model is right-invariant. Finally, a SelfQuasiIsometry with constants K and C of a pseudometric space is a self-map f with d(fx,fy) ≤ K·d(x,y)+C, d(x,y) ≤ K·d(fx,fy)+K·C, and every point within distance C of the image of f.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PolycyclicRecognition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PolycyclicRecognition.lean; bytes 16..8041
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! # Quasi-isometric recognition and uniform bounded height

A polycyclic group has a finite subnormal series with cyclic factors. The
height quotient below is the quotient of the Lie algebra by the common
kernel of the diagonal adjoint characters.
-/

noncomputable section

namespace ChromaticCyclic

structure CyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop where
  le : H ≤ K
  normal : (H.subgroupOf K).Normal
  cyclic : letI := normal; IsCyclic (K ⧸ H.subgroupOf K)

structure CyclicSeries {G : Type*} [Group G] (H K : Subgroup G) (n : ℕ) where
  group : ℕ → Subgroup G
  first : group 0 = H
  last : group n = K
  step : ∀ i < n, CyclicStep (group i) (group (i + 1))

end ChromaticCyclic

namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

section Coarse

variable {G H J : Type*} [Group G] [Group H] [Group J]

/-- Uniform control of finite sets of group differences. -/
def GroupBornologous (f : G → H) : Prop :=
  ∀ S : Set G, S.Finite → ∃ T : Set H, T.Finite ∧
    ∀ x y, x⁻¹ * y ∈ S → (f x)⁻¹ * f y ∈ T

/-- Coarse inverse maps with errors contained in fixed finite sets. -/
structure GroupCoarseEquivalence (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  invFun : H → G
  bornologous_toFun : GroupBornologous toFun
  bornologous_invFun : GroupBornologous invFun
  left_error : (Set.range fun x => x⁻¹ * invFun (toFun x)).Finite
  right_error : (Set.range fun y => y⁻¹ * toFun (invFun y)).Finite

end Coarse

section Polycyclic

open ChromaticCyclic

variable (G : Type*) [Group G]

/-- Polycyclicity expressed by an actual cyclic subnormal series. -/
def IsPolycyclic : Prop :=
  ∃ n : ℕ, Nonempty (CyclicSeries (⊥ : Subgroup G) ⊤ n)

/-- Virtual polycyclicity means a polycyclic subgroup of finite index. -/
def IsVirtuallyPolycyclic : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

end Polycyclic

section UniformLattice

variable {G : Type*} [Group G]

/-- A uniform lattice is discrete and has a compact fundamental cover. -/
def IsUniformLattice [TopologicalSpace G] (Λ : Subgroup G) : Prop :=
  DiscreteTopology Λ ∧ ∃ K : Set G, IsCompact K ∧
    ∀ g : G, ∃ (γ : Λ) (k : G), k ∈ K ∧ (γ : G) * k = g

end UniformLattice

/-- A connected simply connected finite-dimensional real solvable Lie group. -/
structure SimplyConnectedSolvableLieModel where
  modelSpace : Type
  [normedAddCommGroup : NormedAddCommGroup modelSpace]
  [normedSpace : NormedSpace ℝ modelSpace]
  [finiteDimensional : FiniteDimensional ℝ modelSpace]
  carrier : Type
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace modelSpace carrier]
  [group : Group carrier]
  [lieGroup : LieGroup (𝓘(ℝ, modelSpace)) ⊤ carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [simplyConnectedSpace : SimplyConnectedSpace carrier]
  [solvable : Group.IsSolvable carrier]

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- A discrete subgroup with a normalized invariant measure on its coset space. -/
def IsFiniteCovolumeLattice {G : Type} [Group G] [TopologicalSpace G]
    (Λ : Subgroup G) : Prop :=
  letI : MeasurableSpace (G ⧸ Λ) := borel _
  DiscreteTopology Λ ∧ ∃ μ : Measure (G ⧸ Λ),
    IsProbabilityMeasure μ ∧ SMulInvariantMeasure G (G ⧸ Λ) μ

/-- Explicit chains with bounded steps and a linear bound on their length. -/
structure LinearMetricChains (X : Type*) [PseudoMetricSpace X] where
  step : ℝ
  step_pos : 0 < step
  slope : ℝ
  slope_nonneg : 0 ≤ slope
  error : ℝ
  error_nonneg : 0 ≤ error
  chain : ∀ x y : X, ∃ (n : ℕ) (p : ℕ → X),
    p 0 = x ∧ p n = y ∧ (n : ℝ) ≤ slope * dist x y + error ∧
      ∀ i < n, dist (p i) (p (i + 1)) ≤ step

/-- A compatible proper left-invariant metric with large-scale-geodesic chains. -/
structure ProperChainMetric (G : Type*) [Group G] [TopologicalSpace G] where
  metric : MetricSpace G
  topology_eq : metric.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace G›
  proper : letI := metric; ProperSpace G
  leftInvariant : letI := metric; IsIsometricSMul G G
  chains : letI := metric; LinearMetricChains G

/-- The compatible metric retains the original topology definitionally. -/
abbrev ProperChainMetric.compatibleMetric
    {G : Type*} [Group G] [TopologicalSpace G] (d : ProperChainMetric G) : MetricSpace G :=
  d.metric.replaceTopology d.topology_eq.symm

section Height

variable {L I : Type*} [AddCommGroup L] [Module ℝ L]

/-- The common kernel, including the empty family of characters. -/
def heightKernel (χ : I → L →ₗ[ℝ] ℝ) : Submodule ℝ L := ⨅ i, (χ i).ker

/-- The canonical linear height quotient. -/
abbrev HeightSpace (χ : I → L →ₗ[ℝ] ℝ) := L ⧸ heightKernel χ

/-- The quotient map defining infinitesimal height. -/
def heightProjection (χ : I → L →ₗ[ℝ] ℝ) : L →ₗ[ℝ] HeightSpace χ :=
  (heightKernel χ).mkQ

end Height

/-- A simultaneous real upper triangular basis for the adjoint representation. -/
structure TriangularAdjoint (L : Type*) [LieRing L] [LieAlgebra ℝ L] (n : ℕ) where
  basis : Basis (Fin n) ℝ L
  upper : ∀ x : L, (LinearMap.toMatrix basis basis (LieAlgebra.ad ℝ L x)).IsUpperTriangular

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
variable (T : TriangularAdjoint L n)

/-- The diagonal entries of the adjoint representation. -/
noncomputable def character (i : Fin n) : L →ₗ[ℝ] ℝ where
  toFun x := T.basis.repr ⁅x, T.basis i⁆ i
  map_add' x y := by simp [add_lie]
  map_smul' r x := (by simp [smul_lie] : _ = r * T.basis.repr ⁅x, T.basis i⁆ i)

end TriangularAdjoint

section Exponential

attribute [local instance 10000] NormedField.toNormedSpace

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The exponential is characterized by its one-parameter subgroups and
by their tangent vectors at the identity. -/
structure IsGroupExponential (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) : Prop where
  map_zero : Exp 0 = 1
  map_add_smul : ∀ (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s t : ℝ),
    Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)
  hasMFDerivAt_zero : ∀ v : GroupLieAlgebra (𝓘(ℝ, E)) G,
    HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ => Exp (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v)

end Exponential

/-- Unimodularity for the canonical Borel Haar measure of the Lie group. -/
def ModelIsUnimodular (R : SimplyConnectedSolvableLieModel) : Prop :=
  letI : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  letI : LocallyCompactSpace R.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, R.modelSpace))
  letI : MeasurableSpace R.carrier := borel _
  letI : BorelSpace R.carrier := ⟨rfl⟩
  (Measure.haar : Measure R.carrier).IsMulRightInvariant

/-- The upper, lower, and coarse-surjectivity bounds of a self quasi-isometry. -/
structure SelfQuasiIsometry (G : Type*) [PseudoMetricSpace G] (K C : ℝ) where
  toFun : G → G
  upper : ∀ x y, dist (toFun x) (toFun y) ≤ K * dist x y + C
  lower : ∀ x y, dist x y ≤ K * dist (toFun x) (toFun y) + K * C
  surjective : ∀ y, ∃ x, dist y (toFun x) ≤ C



end PolycyclicRecognition
end
end OAI


