-- Prove2me | Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalE
-- name    : ReciprocityTheory_GaloisValuations_GlobalE
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:34:28.290471+00:00
-- url     : https://prove2.me/theorems/0a9c975f-2ac5-4aab-a0d5-e98618b76902
-- title:
--   Global E
-- statement:
--   Definitions and structural lemmas for Global E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalE.lean

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalEA
import Theorems.Thm_ReciprocityTheory_Gal_isClosedEmbedding_resGal
import Theorems.Thm_ReciprocityTheory_Gal_resGal_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Gal.resGal_apply


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise Polynomial
namespace ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp
section split
variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}
theorem mem_decompositionSubgroup_iff_galois_valuations {K : Type*} [Field K] [Algebra K Ω] {B : ValuationSubring Ω}
    {σ : Ω ≃ₐ[K] Ω} : σ ∈ B.decompositionSubgroup K ↔ ∀ x, σ x ∈ B ↔ x ∈ B := by
  constructor
  · intro h x
    have h' : σ • B = B := h
    have e := ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := B) (x := x)
    rw [h'] at e
    exact e
  · intro h
    show σ • B = B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h (σ⁻¹ • x), AlgEquiv.smul_def]
    rw [show σ (σ⁻¹ x) = x from AlgEquiv.apply_symm_apply σ x]
theorem resGal_mem_Dec_iff {σ : G L Ω} :
    resGal F L Ω σ ∈ Dec (F := F) A ↔ σ ∈ Dec (F := L) A := by
  show resGal F L Ω σ ∈ A.decompositionSubgroup F ↔ σ ∈ A.decompositionSubgroup L
  rw [mem_decompositionSubgroup_iff_galois_valuations, mem_decompositionSubgroup_iff_galois_valuations]
  simp only [resGal_apply]
variable (F L) in

def decRes (A : ValuationSubring Ω) : Dec (F := L) A →* Dec (F := F) A :=
  ((resGal F L Ω).comp (Dec (F := L) A).subtype).codRestrict (Dec (F := F) A)
    (fun σ => resGal_mem_Dec_iff.mpr σ.2)
theorem decRes_apply (σ : Dec (F := L) A) : (decRes F L A σ : G F Ω) = resGal F L Ω σ := rfl
theorem decRes_injective : Function.Injective (decRes F L A) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun g : Dec (F := F) A => (g : G F Ω) x) h
  simpa [decRes_apply, resGal_apply] using this
theorem decRes_surjective (h : Dec (F := F) A ≤ (resGal F L Ω).range) :
    Function.Surjective (decRes F L A) := by
  intro τ
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp (h τ.2)
  refine ⟨⟨σ, resGal_mem_Dec_iff.mp (by rw [hσ]; exact τ.2)⟩, ?_⟩
  apply Subtype.ext
  rw [decRes_apply]
  exact hσ
theorem continuous_decRes [IsAlgClosure F Ω] : Continuous (decRes F L A) := by
  refine continuous_induced_rng.2 ?_
  have hc : Continuous (resGal F L Ω) :=
    (isClosedEmbedding_resGal (F := F) (L := L) (Ω := Ω)).continuous
  have e : ((↑) : Dec (F := F) A → G F Ω) ∘ decRes F L A =
      resGal F L Ω ∘ ((↑) : Dec (F := L) A → G L Ω) := by
    funext σ
    exact decRes_apply σ
  rw [e]
  exact hc.comp continuous_subtype_val
def decEquiv [IsAlgClosure F Ω] (h : Dec (F := F) A ≤ (resGal F L Ω).range) :
    Dec (F := L) A ≃ₜ* Dec (F := F) A where
  toMulEquiv := MulEquiv.ofBijective (decRes F L A) ⟨decRes_injective, decRes_surjective h⟩
  continuous_toFun := continuous_decRes
  continuous_invFun := by
    have hI : Topology.IsInducing (resGal F L Ω) :=
      (isClosedEmbedding_resGal (F := F) (L := L) (Ω := Ω)).toIsEmbedding.toIsInducing
    refine continuous_induced_rng.2 (hI.continuous_iff.2 ?_)
    convert (continuous_subtype_val : Continuous (fun τ : Dec (F := F) A => (τ : G F Ω))) using 1
    funext τ
    exact congrArg Subtype.val
      ((MulEquiv.ofBijective (decRes F L A) ⟨decRes_injective, decRes_surjective h⟩).apply_symm_apply τ)
end split
section frob
variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}
end frob
section conj
variable {L Ω : Type*} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
def mapPlace (τ : Ω ≃+* Ω) (A : ValuationSubring Ω) : ValuationSubring Ω :=
  A.comap τ.symm.toRingHom
def conjV (s : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 L) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv s.symm : 𝓞 L →+* 𝓞 L)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    refine (Submodule.ne_bot_iff _).mpr ⟨RingOfIntegers.mapRingEquiv s y, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      convert hy using 1
      exact RingOfIntegers.ext (by simp)
    · exact (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv s).injective).mpr hy0
variable (s : L ≃+* L) (τ : Ω ≃+* Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω (s x))
end conj
end ReciprocityTheory.Gal


