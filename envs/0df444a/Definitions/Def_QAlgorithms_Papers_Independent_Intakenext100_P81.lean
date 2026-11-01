-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P81
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P81
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:59:16.575596+00:00
-- url     : https://prove2.me/theorems/e06c79dc-84e8-476f-8c77-872de424aff9
-- title:
--   Definitions for Symmetries in quantum field theory and quantum gravity
-- statement:
--   The objects the formalized statements of *Symmetries in quantum field theory and quantum gravity* (arXiv:1810.05338) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FactorBasisIndex`: PDF pp.23--24: a basis for a finite family of factors of arbitrary dimensions.
--   - `embedSite`: PDF p.23: embed an operator on one factor, with identity on every other factor.
--   - `factorTensorMatrix`: PDF pp.23--24: tensor product of a finite family of factor matrices.
--   - `RegionIndex`: PDF p.24: basis indices for the factors in a spatial set of sites.
--   - `embedRegion`: PDF p.24: extend a region operator by the identity on its complementary sites.
--   - `adjointConjugationCLM`: PDF p.139, (C.5): conjugation uses the adjoint on the left.
--   - `UniformlyBounded`: PDF p.138: one finite operator-norm bound for every member of a set. The printed strict inequality is corrected to a non-strict bound, including v=0. This pointwise bound is equivalent to a common operator-norm bound and avoids assigning an operator norm to the strong-topology type synonym.
--   - `IsCyclic`: PDF pp.141--142: cyclicity is density of the entire algebra orbit, not finite spanning.
--   - `VacuumSeparating`: PDF p.142: separation allows the zero operator and excludes every nonzero annihilator.
--   - `BoundedConjugationContinuous`: PDF pp.141--143: joint strong continuity on each uniformly bounded subset of the algebra.
--   - `vacuumInner`: PDF p.142 (C.14): the vacuum inner product on operators.
--   - `vacuumTopology`: PDF p.143: vacuum topology is induced by evaluation at the vacuum.
--   - `VacuumConjugationContinuous`: PDF p.143: continuity for the vacuum topology on both algebra copies. The codomain is expressed through its defining embedding into H.
--   - `cyclicVacuumSector`: PDF pp.19--20,137: the closed sector generated from a vacuum by local operators.
--   - `extremalConstant`: PDF p.126 (9.2): the extremal-black-hole normalization. Used below only for d>4.
--   - `emergentCoupling`: PDF p.128 (9.9): positive gauge coupling from the model data.
--   - `emergentNewton`: PDF p.128 (9.10): Newton constant induced by all copies together.
--   - `chargeMassVector`: PDF pp.126,128: charge-to-mass vectors, with one charged species per axis.
--   - `realizedChargeVectors`: PDF pp.126--129: both particles and antiparticles occur in the charge hull.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, https://arxiv.org/abs/1810.05338v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

/-!
Statements from Harlow--Ooguri, arXiv:1810.05338v2.
All new definitions are local to this paper; ASSESSMENT.json records the exact
accepted-library comparisons. Names distinguish unrelated accepted definitions.
Hilbert unitaries and pointwise operator topology use Mathlib directly.
No QFT or gravitational predicate is
introduced by assuming the conclusion it is intended to express.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P81

open scoped BigOperators ComplexConjugate Manifold ContDiff

/-- PDF pp.23--24: a basis for a finite family of factors of arbitrary dimensions. -/
abbrev FactorBasisIndex {n : ℕ} (dim : Fin n → ℕ) := (i : Fin n) → Fin (dim i)

/-- PDF p.23: embed an operator on one factor, with identity on every other factor. -/
def embedSite {n : ℕ} (dim : Fin n → ℕ) (i : Fin n)
    (O : Matrix (Fin (dim i)) (Fin (dim i)) ℂ) :
    Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ :=
  fun x y => if ∀ j, j ≠ i → x j = y j then O (x i) (y i) else 0

/-- PDF pp.23--24: tensor product of a finite family of factor matrices. -/
def factorTensorMatrix {n : ℕ} (dim : Fin n → ℕ)
    (V : (i : Fin n) → Matrix (Fin (dim i)) (Fin (dim i)) ℂ) :
    Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ :=
  fun x y => ∏ i, V i (x i) (y i)

/-- PDF p.24: basis indices for the factors in a spatial set of sites. -/
abbrev RegionIndex {n : ℕ} (dim : Fin n → ℕ) (s : Finset (Fin n)) :=
  (i : {i // i ∈ s}) → Fin (dim i.val)

/-- PDF p.24: extend a region operator by the identity on its complementary sites. -/
def embedRegion {n : ℕ} (dim : Fin n → ℕ) (s : Finset (Fin n))
    (O : Matrix (RegionIndex dim s) (RegionIndex dim s) ℂ) :
    Matrix (FactorBasisIndex dim) (FactorBasisIndex dim) ℂ :=
  fun x y => if ∀ i, i ∉ s → x i = y i then
    O (fun i => x i.val) (fun i => y i.val) else 0

/-- Single-factor sanity check: the tensor formula is the given matrix entry. -/
example (d : ℕ) (V : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d) :
    factorTensorMatrix (fun _ : Fin 1 => d) (fun _ => V) (fun _ => x) (fun _ => y) = V x y := by
  simp [factorTensorMatrix]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [hilbertComplete : CompleteSpace H]

/-- PDF p.139, (C.5): conjugation uses the adjoint on the left. -/
def adjointConjugationCLM (U : H ≃ₗᵢ[ℂ] H) (O : H →L[ℂ] H) : H →L[ℂ] H :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (O.comp U.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Conjugation by the identity leaves every operator unchanged. -/
example (O : H →L[ℂ] H) : adjointConjugationCLM (1 : H ≃ₗᵢ[ℂ] H) O = O := by
  ext v
  rfl

/-- PDF p.138: one finite operator-norm bound for every member of a set.
The printed strict inequality is corrected to a non-strict bound, including v=0.
This pointwise bound is equivalent to a common operator-norm bound and avoids
assigning an operator norm to the strong-topology type synonym. -/
def UniformlyBounded (M : Set (H →Lₚₜ[ℂ] H)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ O ∈ M, ∀ v : H, ‖O v‖ ≤ C * ‖v‖

/-- The zero-operator set has the common bound zero, even on infinite Hilbert spaces. -/
example : UniformlyBounded ({0} : Set (H →Lₚₜ[ℂ] H)) := by
  refine ⟨0, le_rfl, ?_⟩
  intro O hO
  have h : O = 0 := Set.mem_singleton_iff.mp hO
  subst O
  intro v
  simp

/-- PDF pp.141--142: cyclicity is density of the entire algebra orbit, not finite spanning. -/
def IsCyclic (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) : Prop :=
  DenseRange (fun O : A => (O : H →L[ℂ] H) vac)

/-- PDF p.142: separation allows the zero operator and excludes every nonzero annihilator. -/
def VacuumSeparating (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) : Prop :=
  ∀ O : A, (O : H →L[ℂ] H) vac = 0 → (O : H →L[ℂ] H) = 0

/-- PDF pp.141--143: joint strong continuity on each uniformly bounded subset of the algebra. -/
def BoundedConjugationContinuous {G : Type*} [TopologicalSpace G]
    (U : G → H ≃ₗᵢ[ℂ] H) (A : Subalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∀ M : Set (H →Lₚₜ[ℂ] H),
    (∀ O ∈ M, (O : H →L[ℂ] H) ∈ A) → UniformlyBounded M →
    Continuous (fun p : G × M =>
      (adjointConjugationCLM (U p.1) (p.2.val : H →L[ℂ] H) : H →Lₚₜ[ℂ] H))

/-- PDF p.142 (C.14): the vacuum inner product on operators. -/
def vacuumInner (vac : H) (O P : H →L[ℂ] H) : ℂ :=
  inner ℂ (O vac) (P vac)

/-- PDF p.143: vacuum topology is induced by evaluation at the vacuum. -/
def vacuumTopology (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) : TopologicalSpace A :=
  TopologicalSpace.induced (fun O : A => (O : H →L[ℂ] H) vac) inferInstance

/-- PDF p.143: continuity for the vacuum topology on both algebra copies.
The codomain is expressed through its defining embedding into H. -/
def VacuumConjugationContinuous {G : Type*} [TopologicalSpace G]
    (U : G → H ≃ₗᵢ[ℂ] H) (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) : Prop :=
  letI : TopologicalSpace A := vacuumTopology A vac
  Continuous (fun p : G × A => adjointConjugationCLM (U p.1) (p.2 : H →L[ℂ] H) vac)

/-- The vacuum inner product has the usual diagonal value, fixing its normalization. -/
example (vac : H) (O : H →L[ℂ] H) :
    vacuumInner vac O O = inner ℂ (O vac) (O vac) := rfl

section Lie

variable {m : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [lieCharts : ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
  [lieSmooth : LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G]
  [lieHausdorff : T2Space G] [lieSecondCountable : SecondCountableTopology G]

include hilbertComplete lieCharts lieSmooth lieHausdorff lieSecondCountable

/-- PDF pp.19--20,137: the closed sector generated from a vacuum by local operators. -/
def cyclicVacuumSector (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (fun O : A => (O : H →L[ℂ] H) vac))).topologicalClosure

/-- The sector contains its vacuum because the algebra contains the identity. -/
example (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) : vac ∈ cyclicVacuumSector A vac := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

end Lie

end Hilbert

/-- PDF p.126 (9.2): the extremal-black-hole normalization. Used below only for d>4. -/
def extremalConstant (d : ℕ) : ℝ :=
  Real.sqrt (((d : ℝ) - 2) / (8 * Real.pi * ((d : ℝ) - 3)))

/-- PDF p.128 (9.9): positive gauge coupling from the model data. -/
def emergentCoupling {k : ℕ} (d : ℕ) (multiplicity : Fin k → ℕ) (cutoff : ℝ)
    (i : Fin k) : ℝ :=
  1 / Real.sqrt ((multiplicity i : ℝ) * cutoff ^ (d - 4))

/-- PDF p.128 (9.10): Newton constant induced by all copies together. -/
def emergentNewton {k : ℕ} (d : ℕ) (multiplicity : Fin k → ℕ) (cutoff : ℝ) : ℝ :=
  1 / ∑ i, (multiplicity i : ℝ) * cutoff ^ (d - 2)

/-- PDF pp.126,128: charge-to-mass vectors, with one charged species per axis. -/
def chargeMassVector {k : ℕ} (d : ℕ) (multiplicity : Fin k → ℕ)
    (cutoff : ℝ) (mass : Fin k → ℝ) (i : Fin k) : EuclideanSpace ℝ (Fin k) :=
  EuclideanSpace.single i
    (extremalConstant d * emergentCoupling d multiplicity cutoff i /
      (mass i * Real.sqrt (emergentNewton d multiplicity cutoff)))

/-- PDF pp.126--129: both particles and antiparticles occur in the charge hull. -/
def realizedChargeVectors {k : ℕ} (d : ℕ) (multiplicity : Fin k → ℕ)
    (cutoff : ℝ) (mass : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  Set.range (chargeMassVector d multiplicity cutoff mass) ∪
    Set.range (fun i => -chargeMassVector d multiplicity cutoff mass i)

/-- One-copy sanity check of (9.9): at unit cutoff and multiplicity the coupling is one. -/
example (d : ℕ) : emergentCoupling d (fun _ : Fin 1 => 1) 1 0 = 1 := by
  simp [emergentCoupling]

end QAlgorithms.Papers.Independent.Intakenext100.P81


