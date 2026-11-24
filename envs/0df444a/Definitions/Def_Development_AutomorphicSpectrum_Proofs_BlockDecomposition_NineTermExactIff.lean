-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:44.394802+00:00
-- url     : https://prove2.me/theorems/0309a704-6afd-415b-b577-10d3465a65be
-- title:
--   Nine Term Exact Iff
-- statement:
--   Definitions and structural lemmas for Nine Term Exact Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NineTermExactIff.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion
namespace GlobalTheory.CompanionTheory.PTIso
section Gen
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {I : Type} [Fintype I] {D : I → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (χ : Γ →* Rˣ)
  (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M)
def gloc0 : H0 ρ →ₗ[R] ∀ i, H0 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH0 ρ (φ i)
def gloc1 : H1 ρ →ₗ[R] ∀ i, H1 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH1 ρ (φ i) (hφ i)
def gloc2 : H2 ρ →ₗ[R] ∀ i, H2 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH2 ρ (φ i) (hφ i)
def gtr0 : (∀ i, H0 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H2 (twDual χ ρ)) :=
  ∑ i, (((cupH0H2TwistedDual χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH2 (twDual χ ρ) (φ i) (hφ i)))
def gtr1 (hρ : ContAction ρ) : (∀ i, H1 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H1 (twDual χ ρ)) :=
  ∑ i, (((cupH1H1TwistedDual χ ρ (φ i) (hρ.comp' (hφ i))).flip.compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH1 (twDual χ ρ) (φ i) (hφ i)))
def gtr2 : (∀ i, H2 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H0 (twDual χ ρ)) :=
  ∑ i, (((cup20 χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH0 (twDual χ ρ) (φ i)))
def NineG (hρ : ContAction ρ) : Prop :=
  ∃ (δ₁ : Module.Dual R (H2 (twDual χ ρ)) →ₗ[R] H1 ρ)
    (δ₂ : Module.Dual R (H1 (twDual χ ρ)) →ₗ[R] H2 ρ),
    Function.Injective (gloc0 φ ρ) ∧
    Function.Exact (gloc0 φ ρ) (gtr0 φ hφ χ j ρ) ∧
    Function.Exact (gtr0 φ hφ χ j ρ) δ₁ ∧
    Function.Exact δ₁ (gloc1 φ hφ ρ) ∧
    Function.Exact (gloc1 φ hφ ρ) (gtr1 φ hφ χ j ρ hρ) ∧
    Function.Exact (gtr1 φ hφ χ j ρ hρ) δ₂ ∧
    Function.Exact δ₂ (gloc2 φ hφ ρ) ∧
    Function.Exact (gloc2 φ hφ ρ) (gtr2 φ χ j ρ) ∧
    Function.Surjective (gtr2 φ χ j ρ)
def ShaG : Prop :=
  (Finite (Sha1 (twDual χ ρ) φ hφ) ∧ Finite (Sha2 ρ φ hφ) ∧
    Nonempty (Sha2 ρ φ hφ ≃ₗ[R] Module.Dual R (Sha1 (twDual χ ρ) φ hφ)) ∧
    Nat.card (Sha1 (twDual χ ρ) φ hφ) = Nat.card (Sha2 ρ φ hφ)) ∧
  (Finite (Sha1 ρ φ hφ) ∧ Finite (Sha2 (twDual χ ρ) φ hφ) ∧
    Nonempty (Sha2 (twDual χ ρ) φ hφ ≃ₗ[R] Module.Dual R (Sha1 ρ φ hφ)) ∧
    Nat.card (Sha1 ρ φ hφ) = Nat.card (Sha2 (twDual χ ρ) φ hφ))
end Gen
section Concrete
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
end Concrete
def subgroupIso {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
    (Φ : A ≃ₜ* B) (H : Subgroup A) (K : Subgroup B) (h : ∀ a, a ∈ H ↔ Φ a ∈ K) : H ≃ₜ* K where
  toFun a := ⟨Φ a.1, (h a.1).1 a.2⟩
  invFun b := ⟨Φ.symm b.1, (h _).2 (by simpa using b.2)⟩
  left_inv a := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  continuous_toFun := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _
end GlobalTheory.CompanionTheory.PTIso


