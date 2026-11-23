-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
-- name    : GroundTheory_AutomorphicForms_HaarSK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:50.295741+00:00
-- url     : https://prove2.me/theorems/deccd7e2-ff9a-4d25-9fca-5a7aeaf57fe9
-- title:
--   Haar SK
-- statement:
--   Definitions and structural lemmas for Haar SK, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarSK.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
noncomputable section
namespace HaarSK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def mulMap (S K : Subgroup G) (p : S × K) : G := (p.1 : G) * (p.2 : G)
variable {S K : Subgroup G}
theorem continuous_mulMap : Continuous (mulMap S K) :=
  (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
section Topology
variable [T2Space G] (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G))
include hS hK
theorem isCompact_preimage_mulMap {C : Set G} (hC : IsCompact C) :
    IsCompact (mulMap S K ⁻¹' C) := by
  have hA : IsCompact ((fun q : G × G => q.1 * q.2⁻¹) '' (C ×ˢ (K : Set G))) :=
    (hC.prod hK).image (continuous_fst.mul continuous_snd.inv)
  have hA' := hS.isClosedEmbedding_subtypeVal.isCompact_preimage hA
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine (hA'.prod isCompact_univ).of_isClosed_subset
    (hC.isClosed.preimage continuous_mulMap) ?_
  rintro ⟨s, k⟩ h
  refine ⟨⟨((s : G) * k, (k : G)), ⟨h, k.2⟩, ?_⟩, mem_univ _⟩
  simp
variable [LocallyCompactSpace G]
theorem isProperMap_mulMap : IsProperMap (mulMap S K) :=
  isProperMap_iff_isCompact_preimage.2
    ⟨continuous_mulMap, fun _ hC => isCompact_preimage_mulMap hS hK hC⟩
theorem isQuotientMap_mulMap (hSK : Surjective (mulMap S K)) : IsQuotientMap (mulMap S K) :=
  (isProperMap_mulMap hS hK).isClosedMap.isQuotientMap continuous_mulMap hSK
end Topology
abbrev inter (S K : Subgroup G) : Subgroup S := K.subgroupOf S
theorem mem_inter_iff {m : S} : m ∈ inter S K ↔ (m : G) ∈ K := Subgroup.mem_subgroupOf
theorem exists_mem_inter_of_mul_eq {s s' : S} {k k' : K} (h : (s : G) * k = (s' : G) * k') :
    ∃ m ∈ inter S K, s' = s * m := by
  refine ⟨s⁻¹ * s', ?_, by group⟩
  rw [mem_inter_iff]
  have : ((s⁻¹ * s' : S) : G) = (k : G) * (k' : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h]; group
  rw [this]
  exact K.mul_mem k.2 (K.inv_mem k'.2)
variable (hSK : Surjective (mulMap S K))
def lift (u : S → ℝ) (g : G) : ℝ := u (hSK.hasRightInverse.choose g).1
variable {hSK}
theorem lift_mulMap {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) (p : S × K) :
    lift hSK u (mulMap S K p) = u p.1 := by
  set q := hSK.hasRightInverse.choose (mulMap S K p)
  have hq : mulMap S K q = mulMap S K p := hSK.hasRightInverse.choose_spec _
  obtain ⟨m, hm, he⟩ := exists_mem_inter_of_mul_eq (s := p.1) (s' := q.1) (k := p.2) (k' := q.2)
    hq.symm
  change u q.1 = u p.1
  rw [he, hu _ _ hm]
theorem lift_add (u w : S → ℝ) : lift hSK (u + w) = lift hSK u + lift hSK w := rfl
theorem lift_smul (c : ℝ) (u : S → ℝ) : lift hSK (c • u) = c • lift hSK u := rfl
section Measure
variable [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
def flat (mL : Measure (inter S K)) (v : S → ℝ) (s : S) : ℝ := ∫ m, v (s * m) ∂mL
variable {mL : Measure (inter S K)}
theorem flat_mul_inter [mL.IsMulLeftInvariant] (v : S → ℝ) (s : S) (m : inter S K) :
    flat mL v (s * m) = flat mL v s := by
  unfold flat
  have := integral_mul_left_eq_self (μ := mL) (fun m' : inter S K => v (s * m')) m
  simpa only [Subgroup.coe_mul, mul_assoc] using this
theorem flat_right_inv [mL.IsMulLeftInvariant] (v : S → ℝ) :
    ∀ s, ∀ m ∈ inter S K, flat mL v (s * m) = flat mL v s :=
  fun s m hm => flat_mul_inter v s ⟨m, hm⟩
variable [LocallyCompactSpace S] [CompactSpace (inter S K)]
theorem integrable_mul_inter [IsFiniteMeasure mL] {v : S → ℝ} (hv : Continuous v) (s : S) :
    Integrable (fun m : inter S K => v (s * m)) mL :=
  (hv.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
theorem continuous_flat [IsFiniteMeasure mL] {v : S → ℝ} (hv : Continuous v) :
    Continuous (flat mL v) := by
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  show Continuous fun s : S => ∫ m, v (s * m) ∂mL
  have := continuous_parametric_integral_of_continuous (μ := mL)
    (f := fun (s : S) (m : inter S K) => v (s * m))
    (hv.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))) isCompact_univ
  simpa [flat] using this
theorem hasCompactSupport_flat {v : S → ℝ} (hv : HasCompactSupport v) :
    HasCompactSupport (flat mL v) := by
  refine HasCompactSupport.intro
    ((IsCompact.prod hv (isCompact_univ (X := inter S K))).image
      (f := fun p : S × inter S K => p.1 * (p.2 : S)⁻¹) (by fun_prop)) ?_
  intro s hs
  have h0 : ∀ m : inter S K, v (s * m) = 0 := fun m => by
    by_contra h
    exact hs ⟨(s * m, m), ⟨subset_tsupport _ h, mem_univ _⟩, by simp⟩
  simp [flat, h0]
theorem flat_add [IsFiniteMeasure mL] (v w : CompactlySupportedContinuousMap S ℝ) :
    flat mL (⇑(v + w)) = flat mL v + flat mL w := by
  funext s
  simp only [flat, CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
  exact integral_add (integrable_mul_inter v.continuous s) (integrable_mul_inter w.continuous s)
theorem flat_smul (c : ℝ) (v : CompactlySupportedContinuousMap S ℝ) :
    flat mL (⇑(c • v)) = c • flat mL v := by
  funext s
  change ∫ m, (c • v) (s * m) ∂mL = c • ∫ m, v (s * m) ∂mL
  rw [smul_eq_mul, ← integral_const_mul]
  rfl
variable (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
include hS hK
theorem continuous_lift {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s)
    (huc : Continuous u) : Continuous (lift hSK u) := by
  rw [(isQuotientMap_mulMap hS hK hSK).continuous_iff]
  have : lift hSK u ∘ mulMap S K = u ∘ Prod.fst := funext fun p => lift_mulMap hu p
  rw [this]
  exact huc.comp continuous_fst
theorem hasCompactSupport_lift {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s)
    (hcs : HasCompactSupport u) : HasCompactSupport (lift hSK u) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine HasCompactSupport.intro ((IsCompact.prod hcs (isCompact_univ (X := K))).image
    continuous_mulMap) ?_
  intro g hg
  obtain ⟨p, rfl⟩ := hSK g
  rw [lift_mulMap hu]
  by_contra h
  exact hg ⟨p, ⟨subset_tsupport _ h, mem_univ _⟩, rfl⟩
variable (mL) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure mL]
  [mL.IsMulLeftInvariant]
theorem integrable_lift_flat (v : CompactlySupportedContinuousMap S ℝ) :
    Integrable (lift hSK (flat mL v)) μ :=
  (continuous_lift hS hK hSK (flat_right_inv _) (continuous_flat v.continuous)).integrable_of_hasCompactSupport
    (hasCompactSupport_lift hS hK hSK (flat_right_inv _) (hasCompactSupport_flat v.hasCompactSupport))
def funcL : CompactlySupportedContinuousMap S ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun v => ∫ g, lift hSK (flat mL v) g ∂μ
      map_add' := fun v w => by
        rw [flat_add, lift_add]
        exact integral_add (integrable_lift_flat mL hS hK hSK μ v)
          (integrable_lift_flat mL hS hK hSK μ w)
      map_smul' := fun c v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [flat_smul, lift_smul]
        exact integral_const_mul c _ }
    (fun v hv => integral_nonneg fun g => integral_nonneg fun m => hv _)
end Measure
section Main
variable [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
def translate (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) :
    CompactlySupportedContinuousMap S ℝ where
  toFun s := v (s₀ * s)
  continuous_toFun := v.continuous.comp (continuous_const.mul continuous_id)
  hasCompactSupport' := v.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft s₀)
variable {mL : Measure (inter S K)} [LocallyCompactSpace S] [CompactSpace (inter S K)]
  [IsFiniteMeasure mL] [mL.IsMulLeftInvariant]
  {hS : IsClosed (S : Set G)} {hK : IsCompact (K : Set G)} {hSK : Surjective (mulMap S K)}
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
variable (mL hS hK hSK μ)
abbrev rmk : Measure S := RealRMK.rieszMeasure (funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ))
end Main
end HaarSK
end
end GroundTheory.Automorphic


