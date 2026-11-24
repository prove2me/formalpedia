-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:53:23.96581+00:00
-- url     : https://prove2.me/theorems/56ec1e7a-3a1c-4910-a7c7-e451f625a386
-- title:
--   Hermitian Hasse Principle Holds
-- statement:
--   Definitions and structural lemmas for Hermitian Hasse Principle Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
namespace GlobalTheory.HermGlobal
section Defs
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
noncomputable abbrev baseConj (σ : E ≃ₐ[F] E) (A : Type*) [CommRing A] [Algebra F A] :
    A ⊗[F] E →ₐ[A] A ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id A A) σ.toAlgHom
def CongrOver (σ : E ≃ₐ[F] E) (A : Type*) [CommRing A] [Algebra F A] {r : ℕ}
    (G G' : Matrix (Fin r) (Fin r) E) : Prop :=
  ∃ P : Matrix (Fin r) (Fin r) (A ⊗[F] E), IsUnit P.det ∧
    G'.map (fun x => (1 : A) ⊗ₜ[F] x) =
      Pᵀ * G.map (fun x => (1 : A) ⊗ₜ[F] x) * P.map (baseConj σ A)
variable {σ : E ≃ₐ[F] E} {A : Type*} [CommRing A] [Algebra F A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
end Defs
section Quadratic
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E}
end Quadratic
section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E}
variable [Algebra.IsQuadraticExtension F E] {r : ℕ} {G G' : Matrix (Fin r) (Fin r) E}
end Global
end GlobalTheory.HermGlobal
namespace GlobalTheory.Published
open GlobalTheory.HermGlobal
def HermitianHassePrinciple : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] (σ : E ≃ₐ[F] E), σ ≠ 1 →
    ∀ (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E),
      (∀ a b, σ (G a b) = G b a) → (∀ a b, σ (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 F), CongrOver σ (v.adicCompletion F) G G') →
      (∀ v : InfinitePlace F, CongrOver σ v.Completion G G') →
      ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ
end GlobalTheory.Published


