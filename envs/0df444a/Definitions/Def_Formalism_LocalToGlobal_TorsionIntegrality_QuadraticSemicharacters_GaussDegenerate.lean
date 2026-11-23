-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:01.145812+00:00
-- url     : https://prove2.me/theorems/86f68b81-4e8f-43a7-8e57-6dd7a6d2e057
-- title:
--   Gauss Degenerate
-- statement:
--   Definitions and structural lemmas for Gauss Degenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/GaussDegenerate.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Objects
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def psiT (H : Sesq V) (α : V → ℂ) (z y : V) : ℂ :=
  α z * α y * α (z + y) * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))
open Classical in

def tripleSum (H : Sesq V) (α : V → ℂ) (Λ₁ : AddSubgroup V) (S₂ S₃ : Finset V) : ℂ :=
  ∑ z ∈ S₃, ∑ y ∈ S₂, if z + y ∈ Λ₁ then psiT H α z y else 0
def tripleMu (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) (S₂ S₃ : Finset V) : ℂ :=
  ((Real.sqrt (relIdx Λ₁ Λ₃) / (Real.sqrt (relIdx Λ₁ Λ₂) * Real.sqrt (relIdx Λ₂ Λ₃)) : ℝ) : ℂ)
    * tripleSum H α Λ₁ S₂ S₃
structure TripleData (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V) : Prop where
  herm : IsHerm H
  sd₁ : IsSelfDual H Λ₁
  sd₂ : IsSelfDual H Λ₂
  sd₃ : IsSelfDual H Λ₃
  sc₁ : IsSemiChar H Λ₁ α
  sc₂ : IsSemiChar H Λ₂ α
  sc₃ : IsSemiChar H Λ₃ α
  i₁₂ : relIdx Λ₁ Λ₂ ≠ 0
  i₂₁ : relIdx Λ₂ Λ₁ ≠ 0
  i₁₃ : relIdx Λ₁ Λ₃ ≠ 0
  i₃₁ : relIdx Λ₃ Λ₁ ≠ 0
  i₂₃ : relIdx Λ₂ Λ₃ ≠ 0
  i₃₂ : relIdx Λ₃ Λ₂ ≠ 0
end Objects
def TripleFormula : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    ∀ F ∈ fixedBy H α Λ₁, ∀ v,
      inter H α Λ₂ Λ₃ (inter H α Λ₁ Λ₂ F) v = tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ * inter H α Λ₁ Λ₃ F v
def PsiQuadratic : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ →
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ z' ∈ Λ₃, ∀ y' ∈ Λ₂, z' + y' ∈ Λ₁ →
      psiT H α (z + z') (y + y') = psiT H α z y * psiT H α z' y'
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y z' : ℂ))) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ k : ℕ, psiT H α (k • z) (k • y) = psiT H α z y ^ (k ^ 2)) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ‖psiT H α z y‖ = 1) ∧
    (∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ u' ∈ Λ₁ ⊓ Λ₃, ∀ u ∈ Λ₁ ⊓ Λ₂, ∀ t ∈ Λ₂ ⊓ Λ₃,
      psiT H α (z + u' + t) (y + u - t) = psiT H α z y)
structure IsQuadFn0 {M : Type*} [AddCommGroup M] (φ : M → ℂ) (b : M → M → ℂ) : Prop where
  add : ∀ x y, φ (x + y) = φ x * φ y * b x y
  left : ∀ x y z, b (x + y) z = b x z * b y z
  sq : ∀ (k : ℕ) (x : M), φ (k • x) = φ x ^ (k ^ 2)
  ne : ∀ x, φ x ≠ 0
def GaussDegenerate : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (φ : M → ℂ) (b : M → M → ℂ), IsQuadFn0 φ b →
    ∑ x, φ x ≠ 0 → ∃ r : ℝ, 0 < r ∧ (∑ x, φ x) ^ 8 = (r : ℂ)
def TripleSumEighth : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    tripleSum H α Λ₁ S₂ S₃ ≠ 0 → ∃ r : ℝ, 0 < r ∧ tripleSum H α Λ₁ S₂ S₃ ^ 8 = (r : ℂ)
def TripleConj : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → ∀ S₂ S₃ S₂' S₃' : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ →
    IsReps Λ₁ Λ₃ S₃' → IsReps Λ₃ Λ₂ S₂' →
    tripleMu H α Λ₁ Λ₃ Λ₂ S₃' S₂' = conj (tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃)
def TripleEighth : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ : AddSubgroup V),
    TripleData H α Λ₁ Λ₂ Λ₃ → (∃ F ∈ fixedBy H α Λ₁, F ≠ 0) →
    ∀ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ → IsReps Λ₂ Λ₃ S₃ → tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ ^ 8 = 1
end Formalism.L2.Th1.H


