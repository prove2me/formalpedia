-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:54.727844+00:00
-- url     : https://prove2.me/theorems/3435c6f9-25ab-4f5c-a293-9b29d9e3775b
-- title:
--   Exists Orthonormal Of Unimodular
-- statement:
--   Definitions and structural lemmas for Exists Orthonormal Of Unimodular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
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
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
namespace GlobalTheory.HermLocal
section Abstract
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {c : L →+* L}
end Abstract
section Global
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable abbrev ccBase (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Type*)
    [CommRing A] [Algebra (maximalRealSubfield E) A] :
    A ⊗[maximalRealSubfield E] E →ₐ[A] A ⊗[maximalRealSubfield E] E :=
  Algebra.TensorProduct.map (AlgHom.id A A) (IsCMField.complexConj E).toAlgHom
def CongrOver (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A] {r : ℕ}
    (G G' : Matrix (Fin r) (Fin r) E) : Prop :=
  ∃ P : Matrix (Fin r) (Fin r) (A ⊗[maximalRealSubfield E] E), IsUnit P.det ∧
    G'.map (fun x => (1 : A) ⊗ₜ[maximalRealSubfield E] x) =
      Pᵀ * G.map (fun x => (1 : A) ⊗ₜ[maximalRealSubfield E] x) * P.map (ccBase E A)
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
end Global
end GlobalTheory.HermLocal
namespace GlobalTheory.Published
open GlobalTheory.HermLocal
def HermitianLocalGlobal : Prop :=
  (∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
    (2 : K) ≠ 0 →
    ∀ (L : Type) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] (σ : L ≃ₐ[K] L), σ ≠ 1 →
    ∀ (r : ℕ) (G G' : Matrix (Fin r) (Fin r) L),
      (∀ a b, σ (G a b) = G b a) → (∀ a b, σ (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
      ((∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
        ∃ x : L, G.det / G'.det = x * σ x)) ∧
  (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G G' : Matrix (Fin r) (Fin r) E),
    (∀ a b, cc (G a b) = G b a) → (∀ a b, cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      CongrOver (v.adicCompletion (maximalRealSubfield E)) G G') →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) →
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc)
end GlobalTheory.Published


