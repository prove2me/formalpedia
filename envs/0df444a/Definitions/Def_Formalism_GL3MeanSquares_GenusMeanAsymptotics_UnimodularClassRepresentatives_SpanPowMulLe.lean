-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SpanPowMulLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:55.391063+00:00
-- url     : https://prove2.me/theorems/4bddf3c3-b85e-4d7b-ad43-4c2486ea3ff5
-- title:
--   Span Pow Mul Le
-- statement:
--   Definitions and structural lemmas for Span Pow Mul Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SpanPowMulLe.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
def InP (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : K) : Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k, jK z = jK (ι t) * a
theorem InP.add {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 k b) : InP 𝔭 k (a + b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, ι t₂ * z₁ + ι t₁ * z₂,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz₁) (Ideal.mul_mem_left _ _ hz₂), ?_⟩
  simp only [map_add, map_mul, e₁, e₂]
  ring
theorem InP.neg {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : K} (ha : InP 𝔭 k a) : InP 𝔭 k (-a) := by
  obtain ⟨t, ht, z, hz, e⟩ := ha
  exact ⟨t, ht, -z, neg_mem hz, by rw [map_neg, e, mul_neg]⟩
theorem InP.mul {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k l : ℕ} {a b : K} (ha : InP 𝔭 k a)
    (hb : InP 𝔭 l b) : InP 𝔭 (k + l) (a * b) := by
  obtain ⟨t₁, ht₁, z₁, hz₁, e₁⟩ := ha
  obtain ⟨t₂, ht₂, z₂, hz₂, e₂⟩ := hb
  refine ⟨t₁ * t₂, fun hm => (h𝔭.mem_or_mem hm).elim ht₁ ht₂, z₁ * z₂, ?_, ?_⟩
  · rw [pow_add]
    exact Ideal.mul_mem_mul hz₁ hz₂
  · simp only [map_mul, e₁, e₂]
    ring
theorem inP_jK {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsPrime] {k : ℕ} {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    InP 𝔭 k (jK z) := ⟨1, (Ideal.ne_top_iff_one _).mp h𝔭.ne_top, z, hz, by rw [map_one, map_one, one_mul]⟩
def SP (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subring K where
  carrier := {a | InP 𝔭 0 a}
  mul_mem' := fun ha hb => ha.mul hb
  one_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 1) (by simp)
    rwa [map_one] at this
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := by
    have := inP_jK (K := K) (𝔭 := 𝔭) (k := 0) (z := 0) (by simp)
    rwa [map_zero] at this
  neg_mem' := fun ha => ha.neg
end Formalism.HermitianLattices.Ext.L3.HU


