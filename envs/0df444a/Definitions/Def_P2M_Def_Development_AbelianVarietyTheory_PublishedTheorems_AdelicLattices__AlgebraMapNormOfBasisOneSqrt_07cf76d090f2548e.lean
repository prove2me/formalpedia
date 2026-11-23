-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:17.280984+00:00
-- url     : https://prove2.me/theorems/458624b6-d66f-4844-8b22-b7e1121191dc
-- title:
--   Algebra Map Norm Of Basis One Sqrt
-- statement:
--   Definitions and structural lemmas for Algebra Map Norm Of Basis One Sqrt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/AlgebraMapNormOfBasisOneSqrt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
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
open ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory.Published
def Landherr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G G' : Matrix (Fin r) (Fin r) E),
    (∀ a b, cc (G a b) = G b a) → (∀ a b, cc (G' a b) = G' b a) →
    G.det ≠ 0 → G'.det ≠ 0 →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) →
    (∃ x : E, G.det / G'.det = x * cc x) →
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc
def HasseNorm : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (a : K), a ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L,
      Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) a) →
    (∀ v : InfinitePlace K, ∃ z : v.Completion ⊗[K] L,
      Algebra.norm v.Completion z = algebraMap K v.Completion a) →
    ∃ x : L, Algebra.norm K x = a
section Basic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end Basic
namespace Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
end Landherr
section QuadraticNorm
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
end QuadraticNorm
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A]
end CM
namespace HasseNorm
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end HasseNorm
section Tests
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
end Tests
end GlobalTheory.Published


