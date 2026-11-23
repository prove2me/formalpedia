-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
-- name    : Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:08.837106+00:00
-- url     : https://prove2.me/theorems/8a9a92e1-9216-4ede-bd85-5385c24a418f
-- title:
--   Good Char
-- statement:
--   Definitions and structural lemmas for Good Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/GoodChar.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix GlobalTheory.WeilM
namespace GlobalTheory.CompanionTheory.VacLoc
section Ground
variable {R : Type} [CommRing R] [TopologicalSpace R]
structure GoodChar (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) : Prop where
  norm_one : ∀ x, ‖ψ x‖ = 1
  compact : IsCompact (O : Set R)
  isOpen : IsOpen (O : Set R)
  ann : ∀ x : R, (∀ y ∈ O, ψ (x * y) = 1) ↔ ((u⁻¹ : Rˣ) : R) * x ∈ O
  basis : ∀ U ∈ nhds (0 : R), ∃ v : Rˣ, ∀ y ∈ O, (v : R) * y ∈ U
  den : ∀ x : R, ∃ v : Rˣ, (v : R) ∈ O ∧ (v : R) * x ∈ O
def pair {κ : Type} (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) : ℂ :=
  ∫ x, (starRingEnd ℂ) (φ x) * φ' x ∂μ
variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]
def IsModel (ψ : AddChar R ℂ) (d : Darboux B κ) (μ : @Measure (κ → R) (borel _))
    (S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R))) : Prop :=
  (∀ w (φ : SB (κ → R)), ((S.rho w φ : SB (κ → R)) : (κ → R) → ℂ) = d.rho ψ w φ) ∧
  (∀ φ φ' : SB (κ → R), S.B φ φ' = pair μ φ φ') ∧ ∀ w w', S.c w w' = ψ (⅟(2 : R) * B w w')
end Ground
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
def alH [Invertible (2 : R)] (ψ : AddChar R ℂ) (ξ w₀ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E) : ℂ :=
  ψ (⅟(2 : R) * ⅟(2 : R) * Algebra.trace R E (ξ * (w₀ - c w₀) * hTens c JA JB x x))
def KU (A : Subring E) (J : Matrix β β E) : Set (UG c J) :=
  {g | (∀ i j, ((g : GL β E) : Matrix β β E) i j ∈ A) ∧ ∀ i j, (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) i j ∈ A}
structure OrderCondition (A : Subring E) (w₀ : E) (J : Matrix β β E) : Prop where
  stable : ∀ z ∈ A, c z ∈ A
  mem : w₀ ∈ A
  tr : w₀ + c w₀ = 1
  herm : ∀ i j, c (J j i) = J i j
  int : ∀ i j, J i j ∈ A
  inv : ∃ J' : Matrix β β E, (∀ i j, J' i j ∈ A) ∧ J * J' = 1
structure LatOK [TopologicalSpace E] (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (A : Subring E)
    (Γ : AddSubgroup (Matrix α β E)) : Prop where
  compact : IsCompact (Γ : Set (Matrix α β E))
  isOpen : IsOpen (Γ : Set (Matrix α β E))
  dual : ∀ x, x ∈ Γ ↔ ∀ γ ∈ Γ, ψ (symp c ξ JA JB γ x) = 1
  stable : ∀ x ∈ Γ, ∀ m : Matrix β β E, (∀ i j, m i j ∈ A) → x * m ∈ Γ
def IsVac [TopologicalSpace R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (ξ w₀ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (Γ : AddSubgroup (Matrix α β E)) (φ : (κ → R) → ℂ) : Prop :=
  φ ∈ SB (κ → R) ∧ φ ≠ 0 ∧ ∀ x ∈ Γ, d.rho ψ x φ = (alH c ψ ξ w₀ JA JB x)⁻¹ • φ
def latB {JB : Matrix β β E} (g : UG c JB) (Γ : AddSubgroup (Matrix α β E)) : AddSubgroup (Matrix α β E) :=
  Γ.map (AddMonoidHom.mk' (actB c g) fun x y => by simp [actB, Matrix.add_mul])
def latD (Γ : AddSubgroup (Matrix α β E)) : AddSubgroup (Matrix α (β ⊕ β) E) where
  carrier := {x | x.toCols₁ ∈ Γ ∧ x.toCols₂ ∈ Γ}
  zero_mem' := ⟨Γ.zero_mem, Γ.zero_mem⟩
  add_mem' := fun hx hy => ⟨Γ.add_mem hx.1 hy.1, Γ.add_mem hx.2 hy.2⟩
  neg_mem' := fun hx => ⟨Γ.neg_mem hx.1, Γ.neg_mem hx.2⟩
def InP {J : Matrix β β E} (p : UG c (dbl J)) (t : GL β E) : Prop :=
  ((p : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * diagCols β = diagCols β * (t : Matrix β β E)
def BigCell (A : Subring E) (J : Matrix β β E) : Prop :=
  ∃ k ∈ KU c A (dbl J), ∀ g ∈ KU c A (dbl J), ∃ p ∈ KU c A (dbl J), ∃ p' ∈ KU c A (dbl J), ∃ p'' ∈ KU c A (dbl J),
    ∃ p''' ∈ KU c A (dbl J), (∃ t, InP c p t) ∧ (∃ t, InP c p' t) ∧ (∃ t, InP c p'' t) ∧ (∃ t, InP c p''' t) ∧
      g = p * (k * p' * k⁻¹) * p'' * (k * p''' * k⁻¹)
def ordQ (O : Subring R) (ξ : E) : Subring E := Subring.closure ((algebraMap R E '' (O : Set R)) ∪ {ξ})
end GlobalTheory.CompanionTheory.VacLoc


