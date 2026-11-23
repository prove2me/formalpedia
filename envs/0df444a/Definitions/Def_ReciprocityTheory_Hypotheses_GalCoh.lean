-- Prove2me | Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
-- name    : ReciprocityTheory_Hypotheses_GalCoh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:54.771307+00:00
-- url     : https://prove2.me/theorems/e355ea84-2188-4949-a481-9475d4517627
-- title:
--   Gal Coh
-- statement:
--   Definitions and structural lemmas for Gal Coh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/GalCoh.lean

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd
import Theorems.Thm_ReciprocityTheory_Gal_continuous_locHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
namespace ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
section Local
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
def LocalFinitenessAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ n, 3 ≤ n → Subsingleton (Hn rho n)
def LocalTateDualityAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ∀ hrho : ContAction rho,
    Nonempty (H2 (charRep ((cycMod F Ω l r).comp (Dec (F := F) A).subtype)) ≃ₗ[ZMod (l ^ r)]
      ZMod (l ^ r)) ∧
    Function.Bijective
      (cupH0H2TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho
      (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho
      (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective
      (cup20 ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _))
def UnramifiedOrthogonalityAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
    (∀ σ : Dec (F := F) A, (σ : G F Ω) ∈ Ine (F := F) A → rho σ = 1) →
    ∀ hrho : ContAction rho,
    (∀ x : H1 rho,
      x ∈ H1ur rho ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ y ∈ H1ur (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho)
            ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _)
            (hrho.comp' continuous_id) y x = 0) ∧
    (∀ y : H1 (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho),
      y ∈ H1ur (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho)
          ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ x ∈ H1ur rho ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) rho (MonoidHom.id _)
            (hrho.comp' continuous_id) y x = 0)
def LocalEulerCharAt (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) * Nat.card M ^ locDeg v) ∧
    (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho))
def LocalFinitenessResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    Finite (H0 (rho.comp (Dec (F := F) A).subtype)) ∧ Finite (H1 (rho.comp (Dec (F := F) A).subtype)) ∧
    Finite (H2 (rho.comp (Dec (F := F) A).subtype)) ∧
    ∀ n, 3 ≤ n → Subsingleton (Hn (rho.comp (Dec (F := F) A).subtype) n)
def LocalTateDualityResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ∀ hrho : ContAction rho,
    Nonempty (H2 ((muRep F Ω l r).comp (Dec (F := F) A).subtype) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype) ∧
    Function.Bijective (cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype
      (hrho.comp' continuous_subtype_val)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype
      (hrho.comp' continuous_subtype_val)).flip ∧
    Function.Bijective (cup20 (cycMod F Ω l r) rho (Dec (F := F) A).subtype)
def UnramifiedOrthogonalityResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ σ ∈ Ine A, rho σ = 1) →
    ∀ hrho : ContAction rho,
    (∀ x : H1 (rho.comp (Dec (F := F) A).subtype),
      x ∈ H1ur (rho.comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ y ∈ H1ur ((tateDual rho).comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype (hrho.comp' continuous_subtype_val) y x = 0) ∧
    (∀ y : H1 ((tateDual rho).comp (Dec (F := F) A).subtype),
      y ∈ H1ur ((tateDual rho).comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔
        ∀ x ∈ H1ur (rho.comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)),
          cupH1H1TwistedDual (cycMod F Ω l r) rho (Dec (F := F) A).subtype (hrho.comp' continuous_subtype_val) y x = 0)
def LocalEulerCharResAt (rho : Representation (ZMod (l ^ r)) (G F Ω) M)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  0 < r → IsPlaceOver A v → ContAction rho →
    (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      Nat.card (H1 (rho.comp (Dec (F := F) A).subtype)) = Nat.card (H0 (rho.comp (Dec (F := F) A).subtype)) *
        Nat.card (H2 (rho.comp (Dec (F := F) A).subtype)) * Nat.card M ^ locDeg v) ∧
    (((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
      Nat.card (H1 (rho.comp (Dec (F := F) A).subtype)) = Nat.card (H0 (rho.comp (Dec (F := F) A).subtype)) *
        Nat.card (H2 (rho.comp (Dec (F := F) A).subtype)))
end Local
section Global
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
def locFam (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Av : S → ValuationSubring Ω) :
    ∀ v : S, Dec (F := F) (Av v) →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
  fun v => locHom _ (Av v)
theorem continuous_locFam (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Av : S → ValuationSubring Ω) (v : S) : Continuous (locFam S Av v) :=
  continuous_locHom _ _
def ContainsAbove (S : Finset (HeightOneSpectrum (𝓞 F))) (l : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S
def archH0Card (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (c : InfinitePlace F → G F Ω) : ℕ :=
  open scoped Classical in
  (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
    Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m}) * Nat.card M ^ InfinitePlace.nrComplexPlaces F
def GlobalFinitenessAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → ContainsAbove S l → ContAction rhoS →
    Finite (H0 rhoS) ∧ Finite (H1 rhoS) ∧ Finite (H2 rhoS) ∧
    (l ≠ 2 → ∀ n, 3 ≤ n → Subsingleton (Hn rhoS n))
def GlobalEulerCharAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → ContainsAbove S l → ContAction rhoS →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, w.IsReal → IsCCAt w (c w)) →
      Nat.card (H0 rhoS) * Nat.card (H2 rhoS) * Nat.card M ^ Module.finrank ℚ F =
        Nat.card (H1 rhoS) * archH0Card S rhoS c
def ShaDualityAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → l ≠ 2 → ContainsAbove S l → ContAction rhoS →
    ∀ muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
      muS.comp (toGS Ω _) = cycMod F Ω l r →
    ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
      Finite (Sha1 rhoS (locFam S Av) (continuous_locFam S Av)) ∧
      Finite (Sha2 (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av)) ∧
      Nat.card (Sha1 rhoS (locFam S Av) (continuous_locFam S Av)) =
        Nat.card (Sha2 (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av))
def GreenbergWilesAt (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) : Prop :=
  0 < r → l ≠ 2 → ContainsAbove S l → ∀ hrho : ContAction rhoS,
    ∀ muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
      muS.comp (toGS Ω _) = cycMod F Ω l r →
    ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, w.IsReal → IsCCAt w (c w)) →
    ∀ L : LocCond rhoS (locFam S Av),
      Nat.card (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) *
          Nat.card (H0 (twDual muS rhoS)) *
          (∏ v : S, Nat.card (H0 (rhoS.comp (locFam S Av v)))) * archH0Card S rhoS c =
        Nat.card (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av)
            (perpCond muS rhoS (locFam S Av)
              (fun v => hrho.comp' (continuous_locFam S Av v)) L)) *
          Nat.card (H0 rhoS) * ∏ v : S, Nat.card (L v)
end Global
section Universal
def LocalFiniteness : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), LocalFinitenessAt A rho v
def LocalTateDuality : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), LocalTateDualityAt A rho v
def UnramifiedOrthogonality : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), UnramifiedOrthogonalityAt A rho v
def LocalEulerChar : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (A : ValuationSubring Ω) (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M)
    (v : HeightOneSpectrum (𝓞 F)), LocalEulerCharAt A rho v
def GlobalFiniteness : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    GlobalFinitenessAt S rhoS
def GlobalEulerChar : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    GlobalEulerCharAt S rhoS
def ShaDuality : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    ShaDualityAt S rhoS
def GreenbergWiles : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    GreenbergWilesAt S rhoS
end Universal
section Restrict
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
  [TopologicalSpace M] [DiscreteTopology M]
end Restrict
end ReciprocityTheory.Gal


