-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:45.674573+00:00
-- url     : https://prove2.me/theorems/a33d6c69-8409-4583-ab6d-33ac0b117732
-- title:
--   Target St
-- statement:
--   Definitions and structural lemmas for Target St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/TargetSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
def genIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    (y : (Σ k, ι k) → Ω) : Ideal (MRingOver ℚ ι) :=
  (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))
def NormalGenericFibre {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    IsIntegrallyClosed (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩))
def GeneratesOn {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] {ι' : Type*} [Fintype ι']
    (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ u : ι' → Ω, (∀ j, u j ∈ chartRingZ y c) ∧
    ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = 1
def SecEqStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ τ₀ : ℕ, ∀ τ : ℕ, τ₀ ≤ τ → chartLat y (fun k => (a k : ℤ)) τ = secM y (fun k => τ * a k)
def NormalizationBoundedIndexStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y → NormalGenericFibre y →
    ∃ m τ₀ : ℕ, 1 ≤ m ∧ ∀ τ : ℕ, τ₀ ≤ τ → ∀ s ∈ chartLatNm y (fun k => (a k : ℤ)) τ,
      (m : Ω) * s ∈ secM y (fun k => τ * a k)
def CondStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y →
    ∃ (k : ℕ) (c : MRing ι), IsMultiHomog c (fun κ => k * a κ) ∧ aeval y c ≠ 0 ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ, aeval y c * s ∈ secM y (fun κ => (τ + k) * a κ)
def NefGenericStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (I : IFamily ℚ ι),
    IsFieldIntersection I → IsArithVar (mCoordIdeal y) (D + 1) → NefOnFibres (mCoordIdeal y) α →
    NefOnF I (genIdeal y) α
def LiftStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (t : ℚ) (I : IFamily ℚ ι),
    IsFieldIntersection I → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → 0 < t →
    NefOnFibres (mCoordIdeal y) α → NefOnF I (genIdeal y) α →
    ∃ (a : ℕ) (n : K → ℤ) (ι' : Type) (_ : Fintype ι') (x' : ι' → Ω),
      1 ≤ a ∧ (∀ k, (n k : ℚ) = a * (α k + t)) ∧ (∀ j, x' j ∈ chartLat y n 1) ∧
      LinearIndependent ℤ x' ∧ GeneratesOn y n x' ∧ Birational (fun p : Σ _ : Unit, ι' => x' p.2)
def SiuZStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (I : IFamily ℚ ι),
    IsFieldIntersection I → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnF I (genIdeal y) α →
    0 < I (genIdeal y) D (fun _ => α) →
    ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


