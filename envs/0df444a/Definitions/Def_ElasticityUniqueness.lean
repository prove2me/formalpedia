-- Prove2me | Definitions.Def_ElasticityUniqueness
-- name    : ElasticityUniqueness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.6006+00:00
-- url     : https://prove2.me/theorems/9eeda4b0-616c-4203-9c7b-46196f1e76b5
-- statement:
--   For three-dimensional Euclidean space X, a domain Ω is an open, connected, bounded set whose boundary admits smooth local coordinate maps with smooth inverses, sending each boundary point to the plane of first coordinate zero and identifying Ω locally with the positive half-space. A scalar function is smooth up to Ω if it is smooth on an open neighborhood of its closure. Lamé coefficients λ and μ are admissible when both are smooth up to Ω and satisfy μ(x)>0 and 3λ(x)+2μ(x)>0 throughout the closure. The ambient space consists of an L² displacement field and three L² vector fields representing its coordinate derivatives. Smooth jets are the tuples arising from globally smooth displacement fields with square-integrable values and derivatives; test jets additionally come from compactly supported fields whose support lies in Ω. H¹(Ω) is defined as the closure of smooth jets in the ambient space. Zero trace means membership in the closure of test jets, and two H¹ elements have the same trace when their difference belongs to that closure. Boundary data are the resulting quotient classes, with trace the quotient map. From the derivative components, divergence is the sum of diagonal entries and strain is the symmetric part of the derivative matrix. The elasticity energy pairing is E(u,v)=∫Ω[λ div(u)div(v)+2μ∑ᵢⱼ strain(u)ᵢⱼ strain(v)ᵢⱼ] dx. A weak solution pairs to zero with every zero-trace element. For prescribed boundary data f, dirichletSolution chooses a weak solution having trace f if one exists, and otherwise chooses a representative of f. The Dirichlet-to-Neumann pairing is E(dirichletSolution(f),g.out), where g.out is a chosen representative of g. MainClaim is the defined proposition that, on every such domain, two admissible coefficient pairs with identical Dirichlet-to-Neumann pairings have equal λ and equal μ at every point of Ω.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ElasticityUniqueness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ElasticityUniqueness.lean; bytes 16..3599
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-!
# Global uniqueness for smooth isotropic elasticity

The physical Dirichlet-to-Neumann pairing acts on the variational trace
quotient. Its quotient norm is not identified here with boundary-chart
fractional Sobolev norms.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Elasticity

abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev V := X

def coordVector (i : Fin 3) : X := EuclideanSpace.single i 1

def SmoothBoundary (Ω : Set X) : Prop :=
  ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph X X,
    x ∈ e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
    e x 0 = 0 ∧
    ∀ y ∈ e.source, y ∈ Ω ↔ 0 < e y 0

def Domain (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧ SmoothBoundary Ω

def SmoothUpTo (Ω : Set X) (f : X → ℝ) : Prop :=
  ∃ U : Set X, IsOpen U ∧ closure Ω ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U

def Admissible (Ω : Set X) (lam mu : X → ℝ) : Prop :=
  SmoothUpTo Ω lam ∧ SmoothUpTo Ω mu ∧
    ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x

abbrev Ambient (Ω : Set X) :=
  Lp V 2 (volume.restrict Ω) × (Fin 3 → Lp V 2 (volume.restrict Ω))

def coordDeriv (f : X → V) (i : Fin 3) (x : X) : V :=
  fderiv ℝ f x (coordVector i)

def SmoothJets (Ω : Set X) : Set (Ambient Ω) :=
  {j | ∃ (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
      (hd : ∀ i, MemLp (coordDeriv f i) 2 (volume.restrict Ω)),
    ContDiff ℝ (⊤ : ℕ∞) f ∧
    j.1 = hf.toLp f ∧ j.2 = fun i => (hd i).toLp (coordDeriv f i)}

def TestJets (Ω : Set X) : Set (Ambient Ω) :=
  {j | ∃ (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
      (hd : ∀ i, MemLp (coordDeriv f i) 2 (volume.restrict Ω)),
    ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω ∧
    j.1 = hf.toLp f ∧ j.2 = fun i => (hd i).toLp (coordDeriv f i)}

abbrev H1 (Ω : Set X) := {j : Ambient Ω // j ∈ closure (SmoothJets Ω)}

def HasZeroTrace (Ω : Set X) (u : H1 Ω) : Prop :=
  u.val ∈ closure (TestJets Ω)

def SameTrace (Ω : Set X) (u v : H1 Ω) : Prop :=
  u.val - v.val ∈ closure (TestJets Ω)

abbrev BoundaryData (Ω : Set X) := Quot (SameTrace Ω)

def trace (Ω : Set X) (u : H1 Ω) : BoundaryData Ω := Quot.mk _ u

def div (Ω : Set X) (u : H1 Ω) (x : X) : ℝ :=
  ∑ i, (u.val.2 i x) i

def strain (Ω : Set X) (u : H1 Ω) (x : X) (i j : Fin 3) : ℝ :=
  ((u.val.2 j x) i + (u.val.2 i x) j) / 2

def energy (Ω : Set X) (lam mu : X → ℝ) (u v : H1 Ω) : ℝ :=
  ∫ x, (lam x * div Ω u x * div Ω v x +
    2 * mu x * ∑ i, ∑ j, strain Ω u x i j * strain Ω v x i j)
    ∂(volume.restrict Ω)

def WeakSolution (Ω : Set X) (lam mu : X → ℝ) (u : H1 Ω) : Prop :=
  ∀ v : H1 Ω, HasZeroTrace Ω v → energy Ω lam mu u v = 0

def dirichletSolution (Ω : Set X) (lam mu : X → ℝ)
    (f : BoundaryData Ω) : H1 Ω := by
  classical
  exact if h : ∃ u : H1 Ω, trace Ω u = f ∧ WeakSolution Ω lam mu u
  then Classical.choose h
  else f.out

def DN (Ω : Set X) (lam mu : X → ℝ) : BoundaryData Ω → BoundaryData Ω → ℝ :=
  fun f g => energy Ω lam mu (dirichletSolution Ω lam mu f) g.out

def MainClaim : Prop :=
  ∀ (Ω : Set X), Domain Ω →
  ∀ (lam₁ mu₁ lam₂ mu₂ : X → ℝ),
    Admissible Ω lam₁ mu₁ → Admissible Ω lam₂ mu₂ →
    DN Ω lam₁ mu₁ = DN Ω lam₂ mu₂ →
    (∀ x ∈ Ω, lam₁ x = lam₂ x) ∧ (∀ x ∈ Ω, mu₁ x = mu₂ x)



end Elasticity
end
end OAI


