-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
-- name    : GroundTheory_GlobalFields_CompletionAtPlace_Integers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:08.841076+00:00
-- url     : https://prove2.me/theorems/68cd6e81-5a14-45f0-b1c9-c4abb45571af
-- title:
--   Integers
-- statement:
--   Definitions and structural lemmas for Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero
namespace GroundTheory.Global
section Density
variable {L : Type*} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
theorem adicCompletionIntegers_subset_closure_ringOfIntegers :
    (w.adicCompletionIntegers L : Set (w.adicCompletion L)) ⊆
      closure (Set.range fun r : 𝓞 L ↦ algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have h1 : {y : w.adicCompletion L | Valued.v.restrict (y - x) < γ.1} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨γ, subset_rfl⟩
  have h2 : {y : w.adicCompletion L | Valued.v.restrict (y - x) <
      ((1 : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
        Valuation (w.adicCompletion L) ℤᵐ⁰)))ˣ) : _)} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨1, subset_rfl⟩
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 L) (K := L) w).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding] at hk1 hk2
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := by simp [hc]
  have hx1 : Valued.v x ≤ 1 := hx
  have hkv : w.valuation L k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' w k]
    have : (k : w.adicCompletion L) = (algebraMap L (w.adicCompletion L) k - x) + x := by
      rw [sub_add_cancel]; rfl
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le hk2.le hx1)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hkv (Units.mk0 c hc0)
  refine ⟨_, hγ ?_, r, rfl⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  have hr' : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) -
      algebraMap L (w.adicCompletion L) k) < c := by
    rw [← map_sub]
    exact (valuedAdicCompletion_eq_valuation' w _).trans_lt hr
  have : algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) - x =
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) -
        algebraMap L (w.adicCompletion L) k) + (algebraMap L (w.adicCompletion L) k - x) := by
    ring
  rw [this]
  exact Valuation.map_add_lt _ hr' hk1
end Density
section IntegralClosure
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
theorem mem_integer_of_isIntegral {x : w.adicCompletion L}
    (hx : IsIntegral 𝒪[v.adicCompletion K] x) : x ∈ 𝒪[w.adicCompletion L] :=
  (Valuation.integer.integers (valuation (w.adicCompletion L))).mem_of_integral
    (hx.tower_top (A := 𝒪[w.adicCompletion L]))
omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in

theorem isIntegral_algebraMap_ringOfIntegers (r : 𝓞 L) :
    IsIntegral 𝒪[v.adicCompletion K]
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) := by
  obtain ⟨p, hp, hroot⟩ := RingOfIntegers.isIntegral_coe r
  refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, show (algebraMap 𝒪[v.adicCompletion K] (w.adicCompletion L)).comp
      (Int.castRingHom _) = (algebraMap L (w.adicCompletion L)).comp (algebraMap ℤ L) from
      RingHom.ext_int _ _, ← Polynomial.hom_eval₂]
  exact (congrArg (algebraMap L (w.adicCompletion L)) hroot).trans (map_zero _)
omit [Algebra K L] [w.asIdeal.LiesOver v.asIdeal]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)] in

theorem continuousSMul_integer :
    ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) := by
  refine continuousSMul_of_algebraMap _ _ ?_
  rw [IsScalarTower.algebraMap_eq 𝒪[v.adicCompletion K] (v.adicCompletion K)]
  exact (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).comp
    continuous_subtype_val
theorem isClosed_integralClosure :
    IsClosed ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) := by
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have : ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) :=
    continuousSMul_integer v w
  have hfin : Module.Finite 𝒪[v.adicCompletion K]
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)) :=
    IsIntegralClosure.finite 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' 𝒪[v.adicCompletion K]
    (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L))
  let g := (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)).val.toLinearMap ∘ₗ f
  have hg : Continuous g := LinearMap.continuous_on_pi g
  have : ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) = Set.range g := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := hf ⟨y, hy⟩
      exact ⟨c, by simp [g, hc]⟩
    · rintro ⟨c, rfl⟩
      exact (f c).2
  rw [this]
  exact (isCompact_range hg).isClosed
theorem isIntegral_of_mem_integer {x : w.adicCompletion L} (hx : x ∈ 𝒪[w.adicCompletion L]) :
    IsIntegral 𝒪[v.adicCompletion K] x := by
  have hx' : x ∈ w.adicCompletionIntegers L := (mem_valuationInteger_iff w x).1 hx
  have hsub : (Set.range fun r : 𝓞 L ↦
      algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) ⊆
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) : Set (w.adicCompletion L)) := by
    rintro _ ⟨r, rfl⟩
    exact isIntegral_algebraMap_ringOfIntegers v w r
  exact closure_minimal hsub (isClosed_integralClosure v w)
    (adicCompletionIntegers_subset_closure_ringOfIntegers w hx')
instance isIntegralClosure_integer :
    IsIntegralClosure 𝒪[w.adicCompletion L] 𝒪[v.adicCompletion K] (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun hx ↦ ⟨⟨x, mem_integer_of_isIntegral v w hx⟩, rfl⟩,
    fun ⟨y, hy⟩ ↦ hy ▸ isIntegral_of_mem_integer v w y.2⟩
end IntegralClosure
section MaximalIdeal
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
end MaximalIdeal
section Degree
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
instance charZero_adicCompletion {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) : CharZero (u.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (u.adicCompletion F)).injective
end Degree
end GroundTheory.Global


