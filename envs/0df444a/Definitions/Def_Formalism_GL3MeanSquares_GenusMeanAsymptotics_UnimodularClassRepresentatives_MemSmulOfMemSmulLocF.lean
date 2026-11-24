-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:43.21619+00:00
-- url     : https://prove2.me/theorems/3ac4da36-427d-47a1-b10d-04a138456098
-- title:
--   Mem Smul Of Mem Smul Loc F
-- statement:
--   Definitions and structural lemmas for Mem Smul Of Mem Smul Loc F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_exists_mul_sub_one_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
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
namespace Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
theorem le_locF (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (L : Submodule (𝓞 K) V) : L ≤ locF 𝔭 L := fun x hx =>
  (mem_locF 𝔭 L x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h,
    by simpa using hx⟩
theorem ι_mem_pow {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a : 𝓞 F} (ha : a ∈ 𝔭 ^ k) : ι a ∈ extP K 𝔭 ^ k :=
  (mem_pow_iff 𝔭 k a).2 ha
theorem exists_approx {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) (k : ℕ) {w : V}
    (hw : w ∈ locF 𝔭 L) : ∃ c : 𝓞 F, c - 1 ∈ 𝔭 ^ k ∧ ι c • w ∈ L := by
  have := h𝔭.isPrime
  obtain ⟨t, ht, h⟩ := (mem_locF 𝔭 L w).1 hw
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  exact ⟨u * t, hu, by rw [map_mul, mul_smul]; exact L.smul_mem _ h⟩
theorem exists_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V)
    (J : Ideal (𝓞 K)) {v : V} (hv : v ∈ J • locF 𝔭 L) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ι t • v ∈ J • L := by
  have := h𝔭.isPrime
  induction hv using Submodule.smul_induction_on' with
  | smul a ha w hw =>
    obtain ⟨t, ht, h⟩ := (mem_locF 𝔭 L w).1 hw
    exact ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul ha h⟩
  | add x _ y _ hx hy =>
    obtain ⟨t, ht, h1⟩ := hx
    obtain ⟨u, hu, h2⟩ := hy
    refine ⟨t * u, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht hu, ?_⟩
    rw [smul_add, map_mul]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h1
    · rw [mul_smul]; exact Submodule.smul_mem _ _ h2
theorem mem_smul_of_mem_smul_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V)
    (k : ℕ) {y : V} (hy : y ∈ L) (h : y ∈ extP K 𝔭 ^ k • locF 𝔭 L) : y ∈ extP K 𝔭 ^ k • L := by
  obtain ⟨t, ht, h1⟩ := exists_smul_mem h𝔭 L _ h
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have : y = ι u • (ι t • y) - ι (u * t - 1) • y := by
    rw [map_sub, map_mul, map_one, sub_smul, mul_smul, one_smul]; abel
  rw [this]
  exact sub_mem (Submodule.smul_mem _ _ h1) (Submodule.smul_mem_smul (ι_mem_pow hu) hy)
def quotLocF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) (k : ℕ) :
    (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) ≃ₗ[𝓞 K]
      (↥(locF 𝔭 L) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 L))) :=
  have := h𝔭.isPrime
  LinearEquiv.ofBijective
    (Submodule.mapQ _ _ (Submodule.inclusion (le_locF 𝔭 L)) (by
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hy
      exact Submodule.smul_mono le_rfl (le_locF 𝔭 L) hy))
    (by
      constructor
      · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro x hx
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff] at hx
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]
        exact mem_smul_of_mem_smul_locF h𝔭 L k y.2 hx
      · intro x
        obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨c, hc, h⟩ := exists_approx h𝔭 L k w.2
        refine ⟨Submodule.Quotient.mk ⟨_, h⟩, ?_⟩
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
        have : ((Submodule.inclusion (le_locF 𝔭 L) ⟨ι c • (w : V), h⟩ - w : ↥(locF 𝔭 L)) : V) =
            ι (c - 1) • (w : V) := by
          rw [map_sub, map_one, sub_smul, one_smul]; rfl
        rw [this]
        exact Submodule.smul_mem_smul (ι_mem_pow hc) w.2)
end Formalism.HermitianLattices.Ext.L3.localizedQuotients


