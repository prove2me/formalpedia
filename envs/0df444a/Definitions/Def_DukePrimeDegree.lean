-- Prove2me | Definitions.Def_DukePrimeDegree
-- name    : DukePrimeDegree
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.567782+00:00
-- url     : https://prove2.me/theorems/cf53fc23-0c72-47c0-8681-9a37fa7e58a0
-- statement:
--   For each n, let Gₙ=SLₙ(ℝ), Γₙ be the image of SLₙ(ℤ), and Xₙ=Γₙ\Gₙ with its Borel measurable structure and right multiplication action. Sign matrices are diagonal members of Gₙ with entries ±1. A full lattice M in a number field K consists of a ℤ-submodule, a specified basis indexed by n elements, and the requirement that its ℚ-span is K. Its multiplier subgroup consists of a∈K satisfying aM⊆M; its multiplier discriminant is |disc(K)| times the square of this subgroup’s relative index in the additive group of algebraic integers. An ordering σ of all real embeddings gives the matrix Bᵢⱼ=σⱼ(bᵢ); the normalized lattice is the integer span of the rows of |det B|^(−1/n)B. Its point in Xₙ is chosen from an SLₙ(ℝ) representative of that row lattice, with the identity coset used if none exists. For n=d+1, logarithmic coordinates u∈ℝᵈ give the diagonal matrix a(u)=diag(e^{u₁},…,e^{u_d},e^{−∑uᵢ}); the supporting identities establish the right-action and additive-flow laws. The diagonal orbit of x is {xa(u)}, its period group is {u:xa(u)=x}, and its volume is that group’s additive covolume. Orbital Haar measure is the pushforward of Lebesgue measure restricted to a chosen additive fundamental domain, or zero if no such domain exists; orbitProbability scales this measure by the inverse orbit volume. At each prime p, the completed lattice is the ℤₚ-span of M inside ℚₚ⊗ℚK. Two lattices are locally homothetic when their completions differ by multiplication by a unit of this algebra at every prime. The packet of M consists of diagonal orbits of normalized locally homothetic lattices, also allowing sign-matrix translates. Choosing a basepoint for each distinct orbit, packetMeasure is the sum of its orbitProbability measures weighted by orbit volumes, divided by the total volume. These formulas impose no finiteness or positivity conditions guaranteeing probability measures. Finally, IsHaarProbability means a probability measure invariant under every right translation, and WeakProbabilityConvergence requires probability measures throughout and convergence of integrals against every bounded continuous real-valued function.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DukePrimeDegree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DukePrimeDegree.lean; bytes 16..8004
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
namespace PrimeDegreePackets

abbrev G (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℝ

def integralGroup (n : ℕ) : Subgroup (G n) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).range

abbrev X (n : ℕ) := Quotient (QuotientGroup.rightRel (integralGroup n))

instance xMeasurableSpace (n : ℕ) : MeasurableSpace (X n) := borel (X n)
instance xBorelSpace (n : ℕ) : BorelSpace (X n) := ⟨rfl⟩

def rightAction {n : ℕ} (x : X n) (g : G n) : X n :=
  Quotient.map (fun h => h * g) (by
    intro a b hab
    change (QuotientGroup.rightRel (integralGroup n)) a b at hab
    change (QuotientGroup.rightRel (integralGroup n)) (a * g) (b * g)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab) x

@[simp] theorem rightAction_one {n : ℕ} (x : X n) : rightAction x 1 = x := by
  induction x using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) (mul_one a)

@[simp] theorem rightAction_mul {n : ℕ} (x : X n) (g h : G n) :
    rightAction (rightAction x g) h = rightAction x (g * h) := by
  induction x using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) (mul_assoc a g h)

def signMatrices (n : ℕ) : Set (G n) :=
  {g | (∀ i j, i ≠ j → g.1 i j = 0) ∧ ∀ i, g.1 i i = 1 ∨ g.1 i i = -1}

def rowLattice {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range fun i => g i)

structure FullLattice (n : ℕ) (K : Type*) [Field K] [NumberField K] where
  carrier : Submodule ℤ K
  basis : Basis (Fin n) ℤ carrier
  spans : Submodule.span ℚ (carrier : Set K) = ⊤

def multiplierOrder {n : ℕ} {K : Type*} [Field K] [NumberField K] (M : FullLattice n K) : AddSubgroup K where
  carrier := {a | ∀ x ∈ M.carrier, a * x ∈ M.carrier}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx
    simpa only [add_mul] using M.carrier.add_mem (ha x hx) (hb x hx)
  neg_mem' := by
    intro a ha x hx
    simpa only [neg_mul] using M.carrier.neg_mem (ha x hx)

def integralElements (K : Type*) [Field K] : AddSubgroup K :=
  (integralClosure ℤ K).toSubring.toAddSubgroup

def multiplierDiscriminant {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ℝ :=
  |(NumberField.discr K : ℝ)| *
    ((multiplierOrder M).relIndex (integralElements K) : ℝ) ^ 2

abbrev OrderedEmbeddings (n : ℕ) (K : Type*) [Field K] := Fin n ≃ (K →+* ℝ)

def embeddingMatrix {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => σ j (M.basis i)

def normalizedLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : Submodule ℤ (Fin n → ℝ) :=
  let B := embeddingMatrix M σ
  rowLattice (|(Matrix.det B)| ^ (-(1 : ℝ) / n) • B)

def latticePoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : X n :=
  if h : ∃ g : G n, rowLattice g.1 = normalizedLattice M σ then
    Quotient.mk _ h.choose
  else Quotient.mk _ (1 : G n)

abbrev LogCoordinates (d : ℕ) := Fin d → ℝ

def diagonalFlow {d : ℕ} (u : LogCoordinates d) : G (d + 1) :=
  ⟨Matrix.diagonal (Fin.snoc (fun i => Real.exp (u i)) (Real.exp (-∑ i, u i))), by
    rw [Matrix.det_diagonal, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Real.exp_sum, ← Real.exp_add, add_neg_cancel, Real.exp_zero]⟩

@[simp] theorem diagonalFlow_zero (d : ℕ) : diagonalFlow (0 : LogCoordinates d) = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
  simp
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem diagonalFlow_add {d : ℕ} (u v : LogCoordinates d) :
    diagonalFlow (u + v) = diagonalFlow u * diagonalFlow v := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Real.exp_add, Finset.sum_add_distrib, neg_add_rev, mul_comm]
  · simp [Real.exp_add]

def orbitMap {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) : X (d + 1) :=
  rightAction x (diagonalFlow u)

@[simp] theorem orbitMap_zero {d : ℕ} (x : X (d + 1)) : orbitMap x 0 = x := by
  simp [orbitMap]

@[simp] theorem orbitMap_add {d : ℕ} (x : X (d + 1)) (u v : LogCoordinates d) :
    orbitMap x (u + v) = orbitMap (orbitMap x u) v := by
  simp [orbitMap]

def periodGroup {d : ℕ} (x : X (d + 1)) : AddSubgroup (LogCoordinates d) where
  carrier := {u | orbitMap x u = x}
  zero_mem' := orbitMap_zero x
  add_mem' := by
    intro u v hu hv
    change orbitMap x (u + v) = x
    rw [orbitMap_add, hu, hv]
  neg_mem' := by
    intro u hu
    have h := congrArg (fun y => orbitMap y (-u)) hu
    rw [← orbitMap_add, add_neg_cancel, orbitMap_zero] at h
    exact h.symm

def diagonalOrbit {d : ℕ} (x : X (d + 1)) : Set (X (d + 1)) := Set.range (orbitMap x)

def orbitVolume {d : ℕ} (x : X (d + 1)) : ℝ≥0∞ :=
  addCovolume (periodGroup x) (LogCoordinates d) volume

def orbitalHaar {d : ℕ} (x : X (d + 1)) : Measure (X (d + 1)) :=
  if h : HasAddFundamentalDomain (periodGroup x) (LogCoordinates d) volume then
    Measure.map (orbitMap x) (volume.restrict h.ExistsIsAddFundamentalDomain.choose)
  else 0

def orbitProbability {d : ℕ} (x : X (d + 1)) : Measure (X (d + 1)) :=
  (orbitVolume x)⁻¹ • orbitalHaar x

abbrev LocalAlgebra (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :=
  Padic p ⊗[ℚ] K

def completedLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (M : FullLattice n K) :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  Submodule.span (PadicInt p)
    ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) '' (M.carrier : Set K))

def LocallyHomothetic {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M M' : FullLattice n K) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
    ∃ c : (LocalAlgebra p K)ˣ,
      (completedLattice p M' : Set (LocalAlgebra p K)) =
        (fun z => (c : LocalAlgebra p K) * z) '' (completedLattice p M : Set (LocalAlgebra p K))

def packetOrbits {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K) :
    Set (Set (X (d + 1))) :=
  {O | ∃ M' : FullLattice (d + 1) K, LocallyHomothetic M M' ∧
    ∃ w ∈ signMatrices (d + 1), O = diagonalOrbit (rightAction (latticePoint M' σ) w)}

def orbitBasepoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    {M : FullLattice (d + 1) K} {σ : OrderedEmbeddings (d + 1) K}
    (O : packetOrbits M σ) : X (d + 1) :=
  Classical.epsilon (fun x => diagonalOrbit x = O.1)

def packetMeasure {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K) : Measure (X (d + 1)) :=
  (∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O))⁻¹ •
    Measure.sum (fun O : packetOrbits M σ =>
      orbitVolume (orbitBasepoint O) • orbitProbability (orbitBasepoint O))

def IsHaarProbability {n : ℕ} (μ : Measure (X n)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ g : G n, Measure.map (fun x => rightAction x g) μ = μ

def WeakProbabilityConvergence {n : ℕ} (μ : ℕ → Measure (X n)) (m : Measure (X n)) : Prop :=
  (∀ i, IsProbabilityMeasure (μ i)) ∧ IsProbabilityMeasure m ∧
    ∀ f : BoundedContinuousFunction (X n) ℝ,
    Tendsto (fun i => ∫ x, f x ∂μ i) atTop (𝓝 (∫ x, f x ∂m))

end PrimeDegreePackets
end
end

open MeasureTheory Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

universe u



end DukePrimeDegree
end OAI


