-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_IsoDet
-- name    : Formalism_PeriodIntegrals_IsoDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:17:47.053009+00:00
-- url     : https://prove2.me/theorems/02f9cecf-0b3a-4c69-ada8-fc54a04dd05e
-- title:
--   Iso Det
-- statement:
--   Definitions and structural lemmas for Iso Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/IsoDet.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace PI.IsoDetDefs
open NumberField IsDedekindDomain Module
section Defs
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
def hdual (B : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (1 : Submodule R K).comap ((B y).restrictScalars R)
def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx
def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L
def locLen (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℕ :=
  (Module.length R ((localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype)).toNat
def lidx (p : Ideal R) [p.IsPrime] (A B : Submodule R V) : ℤ :=
  (locLen p A (A ⊓ B) : ℤ) - locLen p B (A ⊓ B)
end Defs
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
def dualInH (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  hdual h M ⊓ (Submodule.span E (M : Set V)).restrictScalars (𝓞 E)
def genIdxH (A B : Submodule (𝓞 E) V) : ℝ :=
  ∏ᶠ P : HeightOneSpectrum (𝓞 E),
    ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (haveI := P.isPrime; lidx P.asIdeal A B)
def latDetH (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : ℝ :=
  Real.sqrt (genIdxH (dualInH h M) M)
def pseudoSpan {ι : Type} [Fintype ι] (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : ι → V) :
    Submodule (𝓞 E) V :=
  ⨆ a, ((𝔞 a : Submodule (𝓞 E) E)).map ((LinearMap.toSpanSingleton E V (v a)).restrictScalars (𝓞 E))
end PI.IsoDetDefs
namespace PI
open NumberField PI.IsoDetDefs
def IsoDet : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
    (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm →
    ∀ (n : ℕ) (e e' : Fin n → V) (𝔞 : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      (∀ a, 𝔞 a ≠ 0) →
      (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (e' a) (e' b) = 0) →
      (Matrix.of fun a b => h (e a) (e' b)).det ≠ 0 →
      latDetH h (pseudoSpan 𝔞 e ⊔ pseudoSpan 𝔞 e') ≤
        |((Algebra.norm ℚ (Matrix.of fun a b => h (e a) (e' b)).det : ℚ) : ℝ)| *
          ∏ a, ((FractionalIdeal.absNorm (𝔞 a) : ℚ) : ℝ) ^ 2
end PI


