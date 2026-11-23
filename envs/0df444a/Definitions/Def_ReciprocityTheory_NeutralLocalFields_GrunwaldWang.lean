-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_GrunwaldWang
-- name    : ReciprocityTheory_NeutralLocalFields_GrunwaldWang
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:20.447837+00:00
-- url     : https://prove2.me/theorems/a1be9ed5-2933-40c7-8e74-cec81730cedd
-- title:
--   Grunwald Wang
-- statement:
--   Definitions and structural lemmas for Grunwald Wang, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/GrunwaldWang.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace Neutral.GrunwaldWang
variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]
def LiesAbove (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A.nonunits ↔ x ∈ v.asIdeal
def IsComplexConjugationAt (w : InfinitePlace K) (c : Ω ≃ₐ[K] Ω) : Prop :=
  ∃ j : Ω →+* ℂ, (∀ x, j (c x) = starRingEnd ℂ (j x)) ∧ InfinitePlace.mk (j.comp (algebraMap K Ω)) = w
def Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (m : ℕ), 0 < m → ¬ 8 ∣ m →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (A : T → ValuationSubring Ω), (∀ v, LiesAbove (A v) v.1) →
    ∀ χ : ∀ v : T, (A v).decompositionSubgroup K →* Multiplicative (ZMod m), (∀ v, Continuous (χ v)) →
    ∀ (R : Finset (InfinitePlace K)) (c : R → (Ω ≃ₐ[K] Ω)), (∀ w, IsComplexConjugationAt w.1 (c w)) →
    ∀ ε : R → Multiplicative (ZMod m), (∀ w, ε w ^ 2 = 1) →
      ∃ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod m), Continuous ψ ∧
        (∀ v : T, ψ.comp ((A v).decompositionSubgroup K).subtype = χ v) ∧ ∀ w : R, ψ (c w) = ε w
def SolubleStatement : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (N : Subgroup (Ω ≃ₐ[F] Ω)), N.Normal → IsOpen (N : Set (Ω ≃ₐ[F] Ω)) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : S → ValuationSubring Ω), (∀ v, LiesAbove (A v) v.1) →
    ∀ U : ∀ v : S, Subgroup ((A v).decompositionSubgroup F), (∀ v, (U v).Normal) →
      (∀ v, IsOpen (U v : Set ((A v).decompositionSubgroup F))) →
    ∀ R : Set (InfinitePlace F), (∀ w ∈ R, w.IsReal) →
      ∃ (H : Subgroup (Ω ≃ₐ[F] Ω)) (_ : H.Normal), IsOpen (H : Set (Ω ≃ₐ[F] Ω)) ∧ Group.IsSolvable ((Ω ≃ₐ[F] Ω) ⧸ H) ∧ H ⊔ N = ⊤ ∧
        (∀ v : S, H.subgroupOf ((A v).decompositionSubgroup F) = U v) ∧
        ∀ w ∈ R, ∀ c : Ω ≃ₐ[F] Ω, IsComplexConjugationAt w c → c ∈ H
end Neutral.GrunwaldWang


