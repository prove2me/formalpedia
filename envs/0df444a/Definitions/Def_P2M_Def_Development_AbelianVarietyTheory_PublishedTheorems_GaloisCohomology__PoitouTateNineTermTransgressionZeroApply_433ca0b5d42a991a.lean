-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:48.902799+00:00
-- url     : https://prove2.me/theorems/2721bd04-dfff-466d-ab02-841d181c74fc
-- title:
--   Poitou Tate Nine Term Transgression Zero Apply
-- statement:
--   Definitions and structural lemmas for Poitou Tate Nine Term Transgression Zero Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.Published
namespace PoitouTate
section Local
variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  (l : ℕ) [Fact l.Prime] (r : ℕ)
abbrev muLoc (A : ValuationSubring Ω) :
    Representation (ZMod (l ^ r)) (Dec (F := F) A) (ZMod (l ^ r)) :=
  charRep ((cycMod F Ω l r).comp (Dec (F := F) A).subtype)
variable (Ω) in

abbrev InvFam : Type :=
  ∀ A : ValuationSubring Ω, H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)
variable {F l r}
def IsNormalised (ζ : Ω) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F))
    (inv : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) : Prop :=
  ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)),
    ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) →
    (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) →
    (∀ g h, χ (g * h) = χ g + χ h) →
    (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) →
    (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) →
    (∀ g h, z.1 (g, h) = κ g * χ h) →
    inv (Submodule.Quotient.mk z) = 1
def ConjCompatible (ζ : Ω) (inv : InvFam F Ω l r) : Prop :=
  ∀ (σ : Ω ≃+* Ω) (τ : F ≃+* F), (∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)) →
  ∀ c : ZMod (l ^ r), σ ζ = ζ ^ c.val →
  ∀ (A A' : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
    (∀ x, σ x ∈ A' ↔ x ∈ A) →
  ∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F l r A')),
    (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F) A'),
      (∀ x, (g' : G F Ω) (σ x) = σ ((g : G F Ω) x)) →
      (∀ x, (h' : G F Ω) (σ x) = σ ((h : G F Ω) x)) → z'.1 (g', h') = c * z.1 (g, h)) →
    inv A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)
def IsLocalInvariants (ζ : Ω) (inv : InvFam F Ω l r) : Prop :=
  (∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
    Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A)) ∧
  ConjCompatible ζ inv
end Local
section Global
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
theorem locFam_apply_eq (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (v : S)
    (g : Dec (F := F) (Av v)) (m : ZMod (l ^ r)) :
    ((charRep μ).comp (locFam S Av v)) g m = muLoc F l r (Av v) g m := by
  have key : μ (toGS Ω _ (g : G F Ω)) = cycMod F Ω l r g := by
    rw [← hμ]
    rfl
  show charRep μ (toGS Ω _ (g : G F Ω)) m =
    charRep ((cycMod F Ω l r).comp (Dec (F := F) (Av v)).subtype) g m
  rw [charRep_apply, charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, key]
def toMuLoc (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (v : S) :
    H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] H2 (muLoc F l r (Av v)) :=
  mapH2 _ _ LinearMap.id continuous_id (locFam_apply_eq S Av μ hμ v)
def invAt (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (inv : InvFam F Ω l r) (v : S) :
    H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r) :=
  (inv (Av v)).comp (toMuLoc S Av μ hμ v)
variable (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
def loc0 : H0 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H0 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH0 ρ (locFam S Av v)
def loc1 : H1 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H1 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH1 ρ (locFam S Av v) (continuous_locFam S Av v)
def loc2 : H2 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H2 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH2 ρ (locFam S Av v) (continuous_locFam S Av v)
def tr0 : (∀ v : S, H0 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H2 (twDual μ ρ)) :=
  ∑ v : S, (((cupH0H2TwistedDual μ ρ (locFam S Av v)).compr₂ (j v)).compl₁₂ (LinearMap.proj v)
    (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v)))
def tr1 (hρ : ContAction ρ) : (∀ v : S, H1 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H1 (twDual μ ρ)) :=
  ∑ v : S, (((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).flip.compr₂
    (j v)).compl₁₂ (LinearMap.proj v)
    (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v)))
def tr2 : (∀ v : S, H2 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H0 (twDual μ ρ)) :=
  ∑ v : S, (((cup20 μ ρ (locFam S Av v)).compr₂ (j v)).compl₁₂ (LinearMap.proj v)
    (resH0 (twDual μ ρ) (locFam S Av v)))
def NineTermExact (hρ : ContAction ρ) : Prop :=
  ∃ (δ₁ : Module.Dual (ZMod (l ^ r)) (H2 (twDual μ ρ)) →ₗ[ZMod (l ^ r)] H1 ρ)
    (δ₂ : Module.Dual (ZMod (l ^ r)) (H1 (twDual μ ρ)) →ₗ[ZMod (l ^ r)] H2 ρ),
    Function.Injective (loc0 S Av ρ) ∧
    Function.Exact (loc0 S Av ρ) (tr0 S Av μ j ρ) ∧
    Function.Exact (tr0 S Av μ j ρ) δ₁ ∧
    Function.Exact δ₁ (loc1 S Av ρ) ∧
    Function.Exact (loc1 S Av ρ) (tr1 S Av μ j ρ hρ) ∧
    Function.Exact (tr1 S Av μ j ρ hρ) δ₂ ∧
    Function.Exact δ₂ (loc2 S Av ρ) ∧
    Function.Exact (loc2 S Av ρ) (tr2 S Av μ j ρ) ∧
    Function.Surjective (tr2 S Av μ j ρ)
def ShaDual : Prop :=
  (Finite (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
    Finite (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) ∧
    Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃ₗ[ZMod (l ^ r)]
      Module.Dual (ZMod (l ^ r)) (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))) ∧
    Nat.card (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) =
      Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av))) ∧
  (Finite (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) ∧
    Finite (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
    Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃ₗ[ZMod (l ^ r)]
      Module.Dual (ZMod (l ^ r)) (Sha1 ρ (locFam S Av) (continuous_locFam S Av))) ∧
    Nat.card (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) =
      Nat.card (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)))
variable {S Av μ j ρ}
def idInv (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) :
    H0 (twDual μ (charRep μ)) :=
  ⟨TDual.mk LinearMap.id, fun g => by
    ext m
    simp only [twDual_apply, TDual.mk_apply, LinearMap.id_apply, charRep_apply, map_inv]
    rw [← mul_assoc, Units.mul_inv, one_mul]⟩
end Global
end PoitouTate
open PoitouTate in

def PoitouTateTotallyComplex : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r →
  ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
  ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      NineTermExact S Av μ (invAt S Av μ hμ inv) ρ hρ ∧ ShaDual S Av μ ρ
end GlobalTheory.Published


