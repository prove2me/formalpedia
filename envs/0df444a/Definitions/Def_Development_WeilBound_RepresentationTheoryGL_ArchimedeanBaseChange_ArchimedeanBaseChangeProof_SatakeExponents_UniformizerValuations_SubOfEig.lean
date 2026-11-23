-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfEig
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfEig
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:44:03.978194+00:00
-- url     : https://prove2.me/theorems/9b302263-2a2f-4b29-86ee-91b4cc871408
-- title:
--   Sub Of Eig
-- statement:
--   Definitions and structural lemmas for Sub Of Eig, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/SubOfEig.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_IwahoriDcosU
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Bc.ArchbcB.B
namespace PositivityTheory.Rg.BcN.F2
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]
def SubOfEig' : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
      (∃ u ∈ fixed ρ K, u ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ hk ρ K e u = c • u) → IsSubquotient π ρ
def SubOfNonNil' : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
    ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ → τ.IsIrreducible →
      IsSubquotient τ ρ → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0) →
      (∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0) → IsSubquotient π ρ
def FinSubq : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL ι F) U), IsSmooth ρ → HasFiniteLength ρ →
    ∃ (J : Type) (_ : Fintype J) (W : J → Type) (_ : ∀ j, AddCommGroup (W j)) (_ : ∀ j, Module ℂ (W j))
      (τ : ∀ j, Representation ℂ (GL ι F) (W j)), (∀ j, IsSmooth (τ j) ∧ (τ j).IsIrreducible ∧ IsSubquotient (τ j) ρ) ∧
      ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (τ' : Representation ℂ (GL ι F) W'), τ'.IsIrreducible →
        IsSubquotient τ' ρ → ∃ j, Nonempty (τ'.Equiv (τ j))
variable (a b : ℕ)
def LocOp2 : Prop :=
  ∀ (K : Subgroup (GL (Fin a ⊕ Fin b) F)), IsOpen (K : Set (GL (Fin a ⊕ Fin b) F)) →
    K ≤ unitGL (n := Fin a ⊕ Fin b) F →
    [MeasurableSpace F] → [BorelSpace F] → ∀ μF : Measure F, μF.IsAddHaarMeasure →
    [MeasurableSpace (GL (Fin a ⊕ Fin b) F)] → [BorelSpace (GL (Fin a ⊕ Fin b) F)] →
    [MeasurableSpace (GL (Fin a) F × GL (Fin b) F)] → [BorelSpace (GL (Fin a) F × GL (Fin b) F)] →
    ∀ (μG : Measure (GL (Fin a ⊕ Fin b) F)) (μM : Measure (GL (Fin a) F × GL (Fin b) F))
      (μN : Measure (Fin a → Fin b → F)), μG.IsHaarMeasure → μM.IsHaarMeasure → μN.IsAddHaarMeasure →
      μG (unitGL (n := Fin a ⊕ Fin b) F : Set (GL (Fin a ⊕ Fin b) F)) = 1 →
      μM ((unitGL (n := Fin a) F : Set (GL (Fin a) F)) ×ˢ (unitGL (n := Fin b) F : Set (GL (Fin b) F))) = 1 →
      μN {X | ∀ i j, ValuativeRel.valuation F (X i j) ≤ 1} = 1 →
    ∃ (X : Finset (GL (Fin a ⊕ Fin b) F)) (Kx : X → Subgroup (GL (Fin a) F × GL (Fin b) F))
      (Φ : (GL (Fin a ⊕ Fin b) F → ℂ) → X → X → GL (Fin a) F × GL (Fin b) F → ℂ),
      (∀ g, ∃! x ∈ X, ∃ A D Y k, k ∈ K ∧ g = blockDiag A D * unipN Y * x * k) ∧
      (∀ x, IsOpen (Kx x : Set (GL (Fin a) F × GL (Fin b) F)) ∧ IsCompact (Kx x : Set (GL (Fin a) F × GL (Fin b) F))) ∧
      (∀ f, IsHk K f → ∀ x y, IsLocallyConstant (Φ f x y) ∧ HasCompactSupport (Φ f x y) ∧
        ∀ k₁ ∈ Kx x, ∀ k₂ ∈ Kx y, ∀ l, Φ f x y (k₁ * l * k₂) = Φ f x y l) ∧
      (∀ f₁ f₂, IsHk K f₁ → IsHk K f₂ → ∀ x z l,
        Φ (hconv K f₁ f₂) x z l = ∑ y, ∫ l', Φ f₁ x y l' * Φ f₂ y z (l'⁻¹ * l) ∂μM) ∧
      (∀ f, IsHk K f → ∀ x y l, Φ (hstar f) x y l = starRingEnd ℂ (Φ f y x l⁻¹)) ∧
      (∀ f, IsHk K f → ∀ (A : GL (Fin a) F) (D : GL (Fin b) F)
        (μγM : Measure (Subgroup.centralizer ({(A, D)} : Set (GL (Fin a) F × GL (Fin b) F)))),
        ((blockDiag A D : GL (Fin a ⊕ Fin b) F) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F).charpoly.Separable →
        μγM.IsHaarMeasure →
        orbIntegralC μM (A, D) μγM (constTerm μF μG μN f) = orbIntegralC μM (A, D) μγM (fun l => ∑ x, Φ f x x l)) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin a) F × GL (Fin b) F) W), IsSmooth σ →
        ∃ T : fixed (ind₂ (Equiv.refl (Fin a ⊕ Fin b)) σ) K ≃ₗ[ℂ] ((x : X) → fixed σ (Kx x)),
          ∀ f, IsHk K f → ∀ (u : fixed (ind₂ (Equiv.refl (Fin a ⊕ Fin b)) σ) K)
            (hu : hk (ind₂ (Equiv.refl (Fin a ⊕ Fin b)) σ) K f u ∈ fixed (ind₂ (Equiv.refl (Fin a ⊕ Fin b)) σ) K) x,
            ∀ lw : W →ₗ[ℂ] ℂ, lw ((T ⟨_, hu⟩ x : fixed σ (Kx x)) : W) =
              ∑ y, ∫ l, Φ f x y l * lw (σ l ((T u y : fixed σ (Kx y)) : W)) ∂μM
end PositivityTheory.Rg.BcN.F2


