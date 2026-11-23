-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:28.030357+00:00
-- url     : https://prove2.me/theorems/496cb200-2c63-4b88-8527-c77811029b19
-- title:
--   Form Perp Vector Mem Of Integral
-- statement:
--   Definitions and structural lemmas for Form Perp Vector Mem Of Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
namespace GlobalTheory
section Covector
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
def pairingMatrix (ε : ι → Module.Dual R M) (e' : ι → M) : Matrix ι ι R :=
  Matrix.of fun a' a => ε a (e' a')
def perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) : M :=
  (pairingMatrix ε e').det • g
    - ∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a'
section Integral
variable {A : Type*} [CommRing A] [Algebra A R]
end Integral
end Covector
section Size
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
end Size
section Degree
open MvPolynomial
variable {S τ : Type*} [CommRing S]
end Degree
section Form
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}
def formPairMatrix (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) : Matrix ι ι R :=
  pairingMatrix (fun a => h.flip (e a)) e'
def formPerpVector (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) : M :=
  perpVector (fun a => h.flip (e a)) e' g
end Form
section InnerProduct
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]
noncomputable def innerFormLeft (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  (innerₛₗ ℂ).flip
end InnerProduct
section Places
variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
end Places
end GlobalTheory


