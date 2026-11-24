-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:21.570868+00:00
-- url     : https://prove2.me/theorems/1f22fef8-6338-411c-891b-2f71478cde86
-- title:
--   Smul Gen Mem Iff
-- statement:
--   Definitions and structural lemmas for Smul Gen Mem Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SmulGenMemIff.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
abbrev Qk (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}
theorem exists_mul_sub_one_mem_pow_of_not_mem_maximal (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (k : ℕ) :
    ∃ s : 𝓞 F, s * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ l ∈ Finset.range k, i ^ l, ?_⟩
  have h1 : y * t = 1 - i := by rw [← hyi]; ring
  have h2 : y * (∑ l ∈ Finset.range k, i ^ l) * t - 1 = -(i ^ k) := by
    rw [mul_right_comm, h1, mul_neg_geom_sum]; ring
  rw [h2]
  exact (Submodule.neg_mem_iff _).mpr (Ideal.pow_mem_pow hi k)
theorem algebraMap_mem_extP_pow_of_mem_pow {k : ℕ} {a : 𝓞 F} (ha : a ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha
theorem smul_top_spec (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k, algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e := by
  refine Submodule.smul_induction_on
    (p := fun w : ↥L => ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k,
      algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e) hw ?_ ?_
  · intro r hr n _
    obtain ⟨t, ht, a, hta⟩ := he.2.2 n n.2
    refine ⟨t, ht, r * a, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, smul_comm, hta, smul_smul]
  · rintro x y ⟨t1, ht1, c1, hc1, h1⟩ ⟨t2, ht2, c2, hc2, h2⟩
    refine ⟨t1 * t2, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht1 ht2,
      algebraMap (𝓞 F) (𝓞 K) t2 * c1 + algebraMap (𝓞 F) (𝓞 K) t1 * c2,
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc1) (Ideal.mul_mem_left _ _ hc2), ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (x : V) = algebraMap (𝓞 F) (𝓞 K) t2 • (c1 • e) := by
      rw [map_mul, mul_comm (algebraMap (𝓞 F) (𝓞 K) t1), mul_smul, h1]
    have e2 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (y : V) = algebraMap (𝓞 F) (𝓞 K) t1 • (c2 • e) := by
      rw [map_mul, mul_smul, h2]
    rw [Submodule.coe_add, smul_add, e1, e2, add_smul, mul_smul, mul_smul]
theorem smul_gen_mem_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    b • (⟨e, he.1⟩ : ↥L) ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro hb
    obtain ⟨t, ht, c, hc, htc⟩ := smul_top_spec h𝔭 he k hb
    have h1 : (algebraMap (𝓞 F) (𝓞 K) t * b) • e = c • e := by
      rw [Submodule.coe_smul] at htc
      rw [mul_smul]
      exact htc
    have h2 : algebraMap (𝓞 F) (𝓞 K) t * b = c := by
      rw [← algebraMap_smul K _ e, ← algebraMap_smul K c e] at h1
      exact IsFractionRing.injective (𝓞 K) K (smul_left_injective K he.2.1 h1)
    obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
    have hb' : b = algebraMap (𝓞 F) (𝓞 K) s * c -
        algebraMap (𝓞 F) (𝓞 K) (s * t - 1) * b := by
      rw [← h2, map_sub, map_mul, map_one]; ring
    rw [hb']
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_right _ _ (algebraMap_mem_extP_pow_of_mem_pow hs))
  · intro hb
    exact Submodule.smul_mem_smul hb Submodule.mem_top
theorem end_eq_zero_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = 0 ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro h0
    have := LinearMap.congr_fun h0 (Submodule.Quotient.mk ⟨e, he.1⟩)
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at this
    exact (smul_gen_mem_iff h𝔭 he k b).mp this
  · intro hb
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
def endHom (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ k) →+* Module.End (𝓞 K) (Qk L 𝔭 k) :=
  Ideal.Quotient.lift _ (algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)))
    fun b hb => (end_eq_zero_iff h𝔭 he k b).2 hb
end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars


