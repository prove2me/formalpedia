-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PoitouTateExactSecond
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PoitouTateExactSecond
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:48.428485+00:00
-- url     : https://prove2.me/theorems/9c960f25-686e-4975-a30f-756e2e35cdac
-- title:
--   Poitou Tate Exact Second
-- statement:
--   Definitions and structural lemmas for Poitou Tate Exact Second, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/GelfandSpectralNormalisation/NormalisedInvariants/PoitouTateExactSecond.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNormalised_a407f4592f87c8cd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
namespace PositivityTheory.PoitouTateConclusion
section Loc
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {r : ℕ}
def InvNormalised (ζ : Ω) (inv : InvFam F Ω l r) : Prop :=
  ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
    Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A)
end Loc
section Glob
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (inv : InvFam F Ω l r)
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
def PoitouTateExactSecond : Prop :=
  Function.Exact (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)
end Glob
def InvExists : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
    ∃ inv : InvFam F Ω l r, InvNormalised ζ inv
def NineAll : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ), (l ≠ 2 ∨ IsTotallyComplex F) → 0 < r →
  ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam F Ω l r, InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ),
    NineTermExact S Av μ (invAt S Av μ hμ inv) ρ hρ
def ShaDualAll : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ), (l ≠ 2 ∨ IsTotallyComplex F) → 0 < r →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ),
    μ.comp (toGS Ω _) = cycMod F Ω l r →
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    ContAction ρ → ShaDual S Av μ ρ
def VanishAll : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ), (l ≠ 2 ∨ IsTotallyComplex F) → 0 < r →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    ContAction ρ → ∀ n, 3 ≤ n → Subsingleton (Hn ρ n)
def EulerPTCase : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    (l ≠ 2 ∨ IsTotallyComplex F) → GlobalEulerCharAt S rhoS
end PositivityTheory.PoitouTateConclusion


