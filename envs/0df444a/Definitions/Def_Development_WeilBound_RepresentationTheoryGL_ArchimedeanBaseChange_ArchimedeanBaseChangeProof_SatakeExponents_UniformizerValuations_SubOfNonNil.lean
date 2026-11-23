-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:38.950328+00:00
-- url     : https://prove2.me/theorems/697730f9-a6f5-4669-851b-0fea95152d74
-- title:
--   Sub Of Non Nil
-- statement:
--   Definitions and structural lemmas for Sub Of Non Nil, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/SubOfNonNil.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep
namespace PositivityTheory.Rg.BcN.F2
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
def IsHk (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) : Prop :=
  IsOpen (K : Set (GL ι F)) ∧ IsCompact (K : Set (GL ι F)) ∧ HasCompactSupport e ∧
    ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, e (k₁ * g * k₂) = e g
def hk {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F))
    (e : GL ι F → ℂ) (v : V) : V :=
  ∑ᶠ q : GL ι F ⧸ K, e q.out • ρ q.out v
def hconv (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) (g : GL ι F) : ℂ :=
  ∑ᶠ q : GL ι F ⧸ K, e₁ q.out * e₂ (q.out⁻¹ * g)
def hstar (e : GL ι F → ℂ) (g : GL ι F) : ℂ := starRingEnd ℂ (e g⁻¹)
variable (F ι)
def HkAlg : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ), IsHk K e₁ → IsHk K e₂ →
    IsHk K (hconv K e₁ e₂) ∧ IsHk K (hstar e₁) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K,
      hk ρ K e₁ v ∈ fixed ρ K ∧ hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) ∧
      ∀ B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ w ∈ fixed ρ K,
        B (hk ρ K e₁ v) w = B v (hk ρ K (hstar e₁) w)
def IsolateAt : Prop :=
  ∀ (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
      (∃ v ∈ fixed π K, v ≠ 0) →
    ∀ (J : Type) [Fintype J] (W : J → Type) [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
      (τ : ∀ j, Representation ℂ (GL ι F) (W j)), (∀ j, IsSmooth (τ j)) → (∀ j, (τ j).IsIrreducible) →
      (∀ j, IsEmpty ((τ j).Equiv π)) →
      ∃ e : GL ι F → ℂ, IsHk K e ∧ ∃ v₀ ∈ fixed π K, ∃ l : V →ₗ[ℂ] ℂ, l v₀ = 1 ∧
        (∀ v ∈ fixed π K, hk π K e v = l v • v₀) ∧ ∀ j, ∀ w ∈ fixed (τ j) K, hk (τ j) K e w = 0
def SubOfNonNil : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
      (∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0) → IsSubquotient π ρ
def SubOfEig : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
      (∃ u ∈ fixed ρ K, u ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ hk ρ K e u = c • u) → IsSubquotient π ρ
def ProdFinLen : Prop :=
  ∀ (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ ι)
    (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) F) (X a)),
    (∀ a, IsSmooth (σ a)) → (∀ a, (σ a).IsIrreducible) → HasFiniteLength (multiProd e σ)
def LocOp : Prop :=
  ∀ (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ ι)
    (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) →
    [MeasurableSpace (Levi F m)] → [BorelSpace (Levi F m)] → ∀ μM : Measure (Levi F m), μM.IsHaarMeasure →
    ∃ (X : Finset (GL ι F)) (Kx : X → Subgroup (Levi F m)) (Φ : (GL ι F → ℂ) → X → X → Levi F m → ℂ),
      (∀ g, ∃! x ∈ X, ∃ p ∈ parab F e, ∃ k ∈ K, g = p * x * k) ∧
      (∀ x, IsOpen (Kx x : Set (Levi F m)) ∧ IsCompact (Kx x : Set (Levi F m))) ∧
      (∀ f, IsHk K f → ∀ x y, IsLocallyConstant (Φ f x y) ∧ HasCompactSupport (Φ f x y) ∧
        ∀ k₁ ∈ Kx x, ∀ k₂ ∈ Kx y, ∀ l, Φ f x y (k₁ * l * k₂) = Φ f x y l) ∧
      (∀ f₁ f₂, IsHk K f₁ → IsHk K f₂ → ∀ x z l,
        Φ (hconv K f₁ f₂) x z l = ∑ y, ∫ l', Φ f₁ x y l' * Φ f₂ y z (l'⁻¹ * l) ∂μM) ∧
      (∀ f, IsHk K f → ∀ x y l, Φ (hstar f) x y l = starRingEnd ℂ (Φ f y x l⁻¹)) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi F m) W), IsSmooth σ →
        ∃ T : fixed (parInd e σ) K ≃ₗ[ℂ] ((x : X) → fixed σ (Kx x)),
          ∀ f, IsHk K f → ∀ (u : fixed (parInd e σ) K) (hu : hk (parInd e σ) K f u ∈ fixed (parInd e σ) K) x,
            ∀ lw : W →ₗ[ℂ] ℂ, lw ((T ⟨_, hu⟩ x : fixed σ (Kx x)) : W) =
              ∑ y, ∫ l, Φ f x y l * lw (σ l ((T u y : fixed σ (Kx y)) : W)) ∂μM
end PositivityTheory.Rg.BcN.F2


