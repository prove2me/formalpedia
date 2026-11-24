-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:44.056272+00:00
-- url     : https://prove2.me/theorems/7448d443-8e45-4100-8186-2bfedbb0ce00
-- title:
--   Poitou Tate Sequence Transport
-- statement:
--   Definitions and structural lemmas for Poitou Tate Sequence Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
namespace GlobalTheory.CompanionTheory.PTIso.NineTransfer
section Ladder
variable {R : Type*} [CommRing R]
def piE {I I' : Type*} {A : I' → Type*} {B : I → Type*} [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    (eI : I ≃ I') (e : ∀ i, A (eI i) ≃ₗ[R] B i) : (∀ i', A i') ≃ₗ[R] ∀ i, B i :=
  (LinearEquiv.piCongrLeft R A eI).symm ≪≫ₗ LinearEquiv.piCongrRight e
end Ladder
section Main
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type}
  [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I]
  [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ')
  (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
  (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) (hχ : ∀ g, χ' (eG g) = χ g)
  (hc : ∀ g m, ρ' (eG g) m = ρ g m)
  (hd : ∀ g f, twDual χ' ρ' (eG g) f = twDual χ ρ g f)
  (hl : ∀ i d m, (ρ'.comp (φ' (eI i))) (eD i d) m = (ρ.comp (φ i)) d m)
def P0 : (∀ i', H0 (ρ'.comp (φ' i'))) ≃ₗ[R] ∀ i, H0 (ρ.comp (φ i)) :=
  piE eI fun i => equivH0OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i)
def P1 : (∀ i', H1 (ρ'.comp (φ' i'))) ≃ₗ[R] ∀ i, H1 (ρ.comp (φ i)) :=
  piE eI fun i => equivH1OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i)
def P2 : (∀ i', H2 (ρ'.comp (φ' i'))) ≃ₗ[R] ∀ i, H2 (ρ.comp (φ i)) :=
  piE eI fun i => equivH2OfIso (eD i) (ρ'.comp (φ' (eI i))) (ρ.comp (φ i)) (hl i)
variable (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
  (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R)
  (hj : ∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))),
    (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) →
      j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z))
end Main
end GlobalTheory.CompanionTheory.PTIso.NineTransfer


