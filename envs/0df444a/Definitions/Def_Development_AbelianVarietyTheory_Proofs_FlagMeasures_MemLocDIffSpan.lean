-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:42.287734+00:00
-- url     : https://prove2.me/theorems/aba46698-f2cc-4a49-a4ae-0305a551dd81
-- title:
--   Mem Loc DIff Span
-- statement:
--   Definitions and structural lemmas for Mem Loc DIff Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
namespace GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain in
theorem natCast_not_isUnit_lemma_3 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsUnit (N : 𝓞 F) := by
  intro h
  have h1 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 F) (N : ℤ))) := by
    have : algebraMap ℤ (𝓞 F) (N : ℤ) = (N : 𝓞 F) := by simp
    rw [this]; exact h.map _
  rw [Algebra.norm_algebraMap, Int.isUnit_iff] at h1
  have hk : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h2 : (2 : ℤ) ≤ (N : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    calc (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      _ = (N : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by omega) hk
  omega
open NumberField IsDedekindDomain in
theorem mem_primeTo_ne_zero_lemma_2 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N)
    {x : 𝓞 F} (hx : x ∈ _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F)) : x ≠ 0 := by
  rintro rfl
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(N : 𝓞 F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit_lemma_3 hN)
  exact hx Q hQ (hle (Ideal.mem_span_singleton_self _)) Q.zero_mem
open NumberField IsDedekindDomain in
theorem primeTo_le_nonZeroDivisors__lemma {F : Type} [Field F] [NumberField F] {N : ℕ}
    (hN : 2 ≤ N) : _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
  fun _ hx => mem_nonZeroDivisors_of_ne_zero (mem_primeTo_ne_zero_lemma_2 hN hx)
open NumberField Matrix in
open scoped ENNReal Classical in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mass.SemiBasis.primeTo_le {d : ℕ} (hd : 2 ≤ d) :
    _root_.GlobalTheory.Mass.primeTo (d : 𝓞 K) ≤ nonZeroDivisors (𝓞 K) :=
  primeTo_le_nonZeroDivisors__lemma hd
abbrev A (K : Type) [Field K] [NumberField K] {d : ℕ} (hd : 2 ≤ d) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (primeTo (d : 𝓞 K)) (primeTo_le hd)
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end GlobalTheory.Mass.SemiBasis


