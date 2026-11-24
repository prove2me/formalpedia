-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_IsProjEigenspaceNegOneOfMulSelfEqOne
-- name    : GroundTheory_GlobalFields_Artin_IsProjEigenspaceNegOneOfMulSelfEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:18.555819+00:00
-- url     : https://prove2.me/theorems/ff8df25e-fe6a-4efd-8f0b-8eb983c8c151
-- title:
--   Is Proj Eigenspace Neg One Of Mul Self Eq One
-- statement:
--   Definitions and structural lemmas for Is Proj Eigenspace Neg One Of Mul Self Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/IsProjEigenspaceNegOneOfMulSelfEqOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Global.Artin
open NumberField InfinitePlace Complex Module
section Involution
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
theorem isProj_eigenspace_one_of_mul_self_eq_one {T : Module.End ℂ V} (hT : T * T = 1) :
    LinearMap.IsProj (Module.End.eigenspace T 1) ((2 : ℂ)⁻¹ • (1 + T)) where
  map_mem x := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    have : T (T x) = x := by simpa using LinearMap.congr_fun hT x
    simp [this, add_comm]
  map_id x hx := by
    rw [Module.End.mem_eigenspace_iff, one_smul] at hx
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, hx]
    rw [← two_smul ℂ x, smul_smul]
    norm_num
theorem isProj_eigenspace_neg_one_of_mul_self_eq_one {T : Module.End ℂ V} (hT : T * T = 1) :
    LinearMap.IsProj (Module.End.eigenspace T (-1)) ((2 : ℂ)⁻¹ • (1 - T)) where
  map_mem x := by
    rw [Module.End.mem_eigenspace_iff]
    have : T (T x) = x := by simpa using LinearMap.congr_fun hT x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, this, neg_smul, one_smul, smul_sub]
    abel
  map_id x hx := by
    rw [Module.End.mem_eigenspace_iff, neg_smul, one_smul] at hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hx, sub_neg_eq_add]
    rw [← two_smul ℂ x, smul_smul]
    norm_num
theorem finrank_eigenspace_of_mul_self_eq_one [FiniteDimensional ℂ V] {T : Module.End ℂ V} (hT : T * T = 1) :
    ((finrank ℂ (Module.End.eigenspace T 1) : ℂ) + finrank ℂ (Module.End.eigenspace T (-1))
        = finrank ℂ V) ∧
    (LinearMap.trace ℂ V T = finrank ℂ (Module.End.eigenspace T 1)
        - finrank ℂ (Module.End.eigenspace T (-1))) := by
  have hP := (isProj_eigenspace_one_of_mul_self_eq_one hT).trace
  have hQ := (isProj_eigenspace_neg_one_of_mul_self_eq_one hT).trace
  rw [← hP, ← hQ]
  constructor
  · rw [← map_add, ← smul_add, ← LinearMap.trace_one]
    congr 1
    rw [show (1 : Module.End ℂ V) + T + (1 - T) = (2 : ℂ) • 1 by
      rw [two_smul]; abel, smul_smul]
    norm_num
  · rw [← map_sub, ← smul_sub]
    congr 1
    rw [show (1 : Module.End ℂ V) + T - (1 - T) = (2 : ℂ) • T by
      rw [two_smul]; abel, smul_smul]
    norm_num
end Involution
section ComplexConj
variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
noncomputable def complexConjAt (w : InfinitePlace L) : L ≃ₐ[K] L := by
  classical
  exact if h : ∃ σ : L ≃ₐ[K] L, ComplexEmbedding.IsConj w.embedding σ then h.choose else 1
variable {K}
theorem exists_isConj_of_isReal_comap [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ∃ σ : L ≃ₐ[K] L, ComplexEmbedding.IsConj w.embedding σ := by
  by_cases hw : w.IsReal
  · exact ⟨1, ComplexEmbedding.isConj_one_iff.mpr (isReal_iff.mp hw)⟩
  · have hram : IsRamified K w :=
      isRamified_iff.mpr ⟨not_isReal_iff_isComplex.mp hw, hv⟩
    rw [← mk_embedding w] at hram
    exact exists_isConj_of_isRamified hram
theorem isConj_complexConjAt [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ComplexEmbedding.IsConj w.embedding (complexConjAt K w) := by
  have h := exists_isConj_of_isReal_comap hv
  rw [complexConjAt, dif_pos h]
  exact h.choose_spec
theorem complexConjAt_mul_self [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    complexConjAt K w * complexConjAt K w = 1 :=
  AlgEquiv.ext fun x ↦ ComplexEmbedding.isConj_apply_apply (isConj_complexConjAt hv) x
end ComplexConj
section Factor
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ (L ≃ₐ[K] L) V)
noncomputable def plusDim (w : InfinitePlace L) : ℕ :=
  finrank ℂ (Module.End.eigenspace (ρ (complexConjAt K w)) 1)
noncomputable def minusDim (w : InfinitePlace L) : ℕ :=
  finrank ℂ (Module.End.eigenspace (ρ (complexConjAt K w)) (-1))
variable {ρ}
omit [FiniteDimensional ℂ V] in

theorem rho_complexConjAt_mul_self [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ρ (complexConjAt K w) * ρ (complexConjAt K w) = 1 := by
  rw [← map_mul, complexConjAt_mul_self hv, map_one]
theorem plusDim_add_minusDim [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    plusDim ρ w + minusDim ρ w = finrank ℂ V := by
  have := (finrank_eigenspace_of_mul_self_eq_one (rho_complexConjAt_mul_self (ρ := ρ) hv)).1
  exact_mod_cast this
theorem character_complexConjAt [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ρ.character (complexConjAt K w) = (plusDim ρ w : ℂ) - minusDim ρ w :=
  (finrank_eigenspace_of_mul_self_eq_one (rho_complexConjAt_mul_self (ρ := ρ) hv)).2
theorem plusDim_eq_character [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    (plusDim ρ w : ℂ) = (ρ.character 1 + ρ.character (complexConjAt K w)) / 2 := by
  rw [Representation.char_one, character_complexConjAt hv, ← plusDim_add_minusDim hv]
  push_cast
  ring
theorem minusDim_eq_character [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    (minusDim ρ w : ℂ) = (ρ.character 1 - ρ.character (complexConjAt K w)) / 2 := by
  rw [Representation.char_one, character_complexConjAt hv, ← plusDim_add_minusDim hv]
  push_cast
  ring
theorem character_prod {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) (g : L ≃ₐ[K] L) :
    (ρ.prod σ).character g = ρ.character g + σ.character g :=
  LinearMap.trace_prodMap' (ρ g) (σ g)
theorem plusDim_prod {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    plusDim (ρ.prod σ) w = plusDim ρ w + plusDim σ w := by
  have h1 := plusDim_eq_character (ρ := ρ.prod σ) hv
  rw [character_prod, character_prod, add_add_add_comm, add_div, ← plusDim_eq_character hv,
    ← plusDim_eq_character hv] at h1
  exact_mod_cast h1
theorem minusDim_prod {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    minusDim (ρ.prod σ) w = minusDim ρ w + minusDim σ w := by
  have h1 := minusDim_eq_character (ρ := ρ.prod σ) hv
  rw [character_prod, character_prod, add_sub_add_comm, add_div, ← minusDim_eq_character hv,
    ← minusDim_eq_character hv] at h1
  exact_mod_cast h1
variable (L) in

noncomputable def placeOver [Algebra.IsAlgebraic K L] (v : InfinitePlace K) : InfinitePlace L :=
  (comap_surjective (k := K) (K := L) v).choose
theorem comap_placeOver [Algebra.IsAlgebraic K L] (v : InfinitePlace K) :
    (placeOver L v).comap (algebraMap K L) = v :=
  (comap_surjective (k := K) (K := L) v).choose_spec
variable (ρ) in
open scoped Classical in

noncomputable def gammaFactorAt [Algebra.IsAlgebraic K L] (v : InfinitePlace K) (s : ℂ) : ℂ :=
  if v.IsReal then
    Gammaℝ s ^ plusDim ρ (placeOver L v) * Gammaℝ (s + 1) ^ minusDim ρ (placeOver L v)
  else Gammaℂ s ^ finrank ℂ V
theorem gammaFactorAt_prod [IsGalois K L] [Algebra.IsAlgebraic K L]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) (v : InfinitePlace K) (s : ℂ) :
    gammaFactorAt (ρ.prod σ) v s = gammaFactorAt ρ v s * gammaFactorAt σ v s := by
  by_cases hv : v.IsReal
  · have hv' : ((placeOver L v).comap (algebraMap K L)).IsReal := by rwa [comap_placeOver]
    simp only [gammaFactorAt, if_pos hv, plusDim_prod σ hv', minusDim_prod σ hv', pow_add]
    ring
  · simp only [gammaFactorAt, if_neg hv, Module.finrank_prod, pow_add]
variable (ρ) in

noncomputable def gammaFactor [NumberField K] [Algebra.IsAlgebraic K L] (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace K, gammaFactorAt ρ v s
theorem gammaFactor_prod [NumberField K] [IsGalois K L] [Algebra.IsAlgebraic K L]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) (s : ℂ) :
    gammaFactor (ρ.prod σ) s = gammaFactor ρ s * gammaFactor σ s := by
  simp only [gammaFactor, gammaFactorAt_prod, Finset.prod_mul_distrib]
end Factor
example {K L V W : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) (σ : Representation ℂ (L ≃ₐ[K] L) W) (s : ℂ) :
    gammaFactor (ρ.prod σ) s = gammaFactor ρ s * gammaFactor σ s :=
  gammaFactor_prod σ s
end GroundTheory.Global.Artin


