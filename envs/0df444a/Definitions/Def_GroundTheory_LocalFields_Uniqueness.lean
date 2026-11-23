-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Uniqueness
-- name    : GroundTheory_LocalFields_Uniqueness
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:14.851804+00:00
-- url     : https://prove2.me/theorems/4495d156-0d3d-4c32-8bd0-1743b3b6d6ce
-- title:
--   Uniqueness
-- statement:
--   Definitions and structural lemmas for Uniqueness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Topology Filter
section Topology
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
theorem t2Space_of_isNonarchimedeanLocalField : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance
@[instance_reducible]
def nontriviallyNormedField : NontriviallyNormedField K :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
example : (nontriviallyNormedField K).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace K› :=
  rfl
theorem completeSpace_nontriviallyNormedField :
    @CompleteSpace K (nontriviallyNormedField K).toUniformSpace := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact (inferInstance : CompleteSpace K)
variable [Algebra K L] [ValuativeExtension K L]
theorem isModuleTopology [FiniteDimensional K L] : IsModuleTopology K L := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  exact isModuleTopologyOfFiniteDimensional
end Topology
section Nilpotent
variable {F : Type*} [Field F] [ValuativeRel F]
theorem vle_iff_not_valuation_div_lt_one {x : F} (hx : x ≠ 0) (y : F) :
    x ≤ᵥ y ↔ ¬ valuation F (y / x) < 1 := by
  have hx' : 0 < valuation F x := by
    rw [zero_lt_iff]
    simpa using hx
  rw [(valuation F).vle_iff_le, map_div₀, div_lt_one₀ hx', not_lt]
theorem vle_map_iff_of_valuation_lt_one_iff {F' : Type*} [Field F'] [ValuativeRel F']
    (f : F →+* F') (hf : ∀ z, valuation F' (f z) < 1 ↔ valuation F z < 1) (x y : F) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [map_zero]
    exact ⟨fun _ ↦ ValuativeRel.zero_vle y, fun _ ↦ ValuativeRel.zero_vle (f y)⟩
  · rw [vle_iff_not_valuation_div_lt_one hx, vle_iff_not_valuation_div_lt_one
      ((map_ne_zero f).mpr hx), ← map_div₀, hf]
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
theorem tendsto_pow_atTop_nhds_zero_iff (x : F) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) ↔ valuation F x < 1 := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero F).tendsto_right_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (h 1 trivial).exists
    simp only [Set.mem_ofPred_eq, map_pow, Units.val_one] at hn
    by_contra hx
    exact (one_le_pow₀ (not_lt.mp hx)).not_gt hn
  · intro hx γ _
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [map_pow]
    exact (pow_le_pow_of_le_one zero_le hx.le hm).trans_lt hn
end Nilpotent
section Maps
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]
theorem continuous_algHom (f : L →ₐ[K] M) : Continuous f := by
  have := isModuleTopology K L
  exact IsModuleTopology.continuous_of_linearMap (R := K) f.toLinearMap
theorem isClosedEmbedding_algHom (f : L →ₐ[K] M) : IsClosedEmbedding f := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  have := t2Space_of_isNonarchimedeanLocalField M
  exact LinearMap.isClosedEmbedding_of_injective (f := f.toLinearMap)
    (LinearMap.ker_eq_bot.mpr f.toRingHom.injective)
theorem valuation_map_lt_one_iff (f : L →ₐ[K] M) (x : L) :
    valuation M (f x) < 1 ↔ valuation L x < 1 := by
  rw [← tendsto_pow_atTop_nhds_zero_iff, ← tendsto_pow_atTop_nhds_zero_iff,
    (isClosedEmbedding_algHom f).isInducing.tendsto_nhds_iff, ← map_zero f]
  simp only [Function.comp_def, map_pow]
theorem vle_map_iff (f : L →ₐ[K] M) (x y : L) : f x ≤ᵥ f y ↔ x ≤ᵥ y :=
  vle_map_iff_of_valuation_lt_one_iff f.toRingHom (valuation_map_lt_one_iff f) x y
end Maps
section Uniqueness
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
end Uniqueness
section Galois
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]
theorem valuation_map_le_iff (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) ≤ valuation M (f y) ↔ valuation L x ≤ valuation L y := by
  rw [← (valuation M).vle_iff_le, ← (valuation L).vle_iff_le, vle_map_iff]
theorem valuation_map_eq_iff (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) = valuation M (f y) ↔ valuation L x = valuation L y := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_map_le_iff, valuation_map_le_iff]
theorem map_mem_integer_iff (f : L →ₐ[K] M) (x : L) : f x ∈ 𝒪[M] ↔ x ∈ 𝒪[L] := by
  simp only [Valuation.mem_integer_iff]
  rw [← map_one (valuation M), ← map_one f, valuation_map_le_iff, map_one]
def continuousAlgHom (f : L →ₐ[K] M) : L →A[K] M where
  __ := f
  cont := continuous_algHom f
@[simp]
theorem coe_continuousAlgHom (f : L →ₐ[K] M) : ⇑(continuousAlgHom f) = f :=
  rfl
def integerAlgHom (f : L →ₐ[K] M) : 𝒪[L] →ₐ[𝒪[K]] 𝒪[M] where
  toFun x := ⟨f x, (map_mem_integer_iff f x).mpr x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' r := by ext; simp
@[simp]
theorem coe_integerAlgHom_apply (f : L →ₐ[K] M) (x : 𝒪[L]) :
    (integerAlgHom f x : M) = f x :=
  rfl
instance isLocalHom_integerAlgHom (f : L →ₐ[K] M) : IsLocalHom (integerAlgHom f) where
  map_nonunit x hx := by
    rw [(Valuation.integer.integers (valuation M)).isUnit_iff_valuation_eq_one] at hx
    rw [(Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one]
    have hx' : valuation M (f x) = valuation M (f 1) := by
      rw [map_one, map_one]
      exact hx
    exact ((valuation_map_eq_iff f x 1).mp hx').trans (map_one _)
def residueAlgHom (f : L →ₐ[K] M) : 𝓀[L] →ₐ[𝓀[K]] 𝓀[M] :=
  IsLocalRing.ResidueField.mapAlgHom' (integerAlgHom f)
@[simp]
theorem residueAlgHom_residue (f : L →ₐ[K] M) (x : 𝒪[L]) :
    residueAlgHom f (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[M] (integerAlgHom f x) :=
  rfl
variable (K L)
def continuousAlgEquiv (σ : L ≃ₐ[K] L) : L ≃A[K] L where
  toAlgEquiv := σ
  continuous_toFun := continuous_algHom σ.toAlgHom
  continuous_invFun := continuous_algHom σ.symm.toAlgHom
@[simp]
theorem coe_continuousAlgEquiv (σ : L ≃ₐ[K] L) : ⇑(continuousAlgEquiv K L σ) = σ :=
  rfl
def homeomorph (σ : L ≃ₐ[K] L) : L ≃ₜ L :=
  (continuousAlgEquiv K L σ).toHomeomorph
@[simp]
theorem coe_homeomorph (σ : L ≃ₐ[K] L) : ⇑(homeomorph K L σ) = σ :=
  rfl
def integerAlgEquiv : (L ≃ₐ[K] L) →* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) where
  toFun σ := AlgEquiv.ofAlgHom (integerAlgHom σ.toAlgHom) (integerAlgHom σ.symm.toAlgHom)
    (by ext; simp) (by ext; simp)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
@[simp]
theorem coe_integerAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    (integerAlgEquiv K L σ x : L) = σ x :=
  rfl
def residueAlgEquiv : (L ≃ₐ[K] L) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun σ := IsLocalRing.ResidueField.mapAlgEquiv' (integerAlgEquiv K L σ)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simp
  map_mul' σ τ := by
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simp
end Galois
end GroundTheory.LocalField


