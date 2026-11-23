-- Prove2me | Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
-- name    : GroundTheory_LocalFields_ExamplesCharZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:32.733914+00:00
-- url     : https://prove2.me/theorems/5601ae9b-1698-4d29-b19d-9cb1bea35070
-- title:
--   Examples Char Zero
-- statement:
--   Definitions and structural lemmas for Examples Char Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel WithZero Topology
namespace CharZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
instance fact_prime_ringChar : Fact (ringChar 𝓀[K]).Prime :=
  ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
variable (p : ℕ) [CharP 𝓀[K] p]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem valuation_intCast_le_one (n : ℤ) : valuation K (n : K) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (intCast_mem _ n)
theorem valuation_intCast_eq_one_iff (n : ℤ) : valuation K (n : K) = 1 ↔ ¬ (p : ℤ) ∣ n := by
  have hres : IsLocalRing.residue 𝒪[K] (n : 𝒪[K]) = (n : 𝓀[K]) := map_intCast _ n
  rw [← CharP.intCast_eq_zero_iff 𝓀[K] p n, ← hres, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  push_cast
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm (valuation_intCast_le_one K n) (not_lt.mp h)
variable [Fact p.Prime]
omit [Fact p.Prime] in

theorem valuation_p_lt_one : valuation K (p : K) < 1 := by
  refine lt_of_le_of_ne (by exact_mod_cast valuation_intCast_le_one K p) fun h => ?_
  have := (valuation_intCast_eq_one_iff K p p).mp (by exact_mod_cast h)
  exact this dvd_rfl
variable [CharZero K]
theorem valuation_ratCast_le_one_iff (q : ℚ) : valuation K (q : K) ≤ 1 ↔ ¬ p ∣ q.den := by
  have hden : (q.den : K) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q : K) = (q.num : K) / (q.den : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hvden : valuation K (q.den : K) ≠ 0 := by simp
  rw [hq, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvden)]
  constructor
  · intro h hp
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hn
      rw [Int.natCast_dvd] at hn
      exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt Fact.out) hn hp q.reduced
    have h1 := (valuation_intCast_eq_one_iff K p q.num).mpr hnum
    obtain ⟨m, hm⟩ := hp
    have h2 : valuation K (q.den : K) < 1 := by
      rw [hm, Nat.cast_mul, map_mul]
      calc valuation K (p : K) * valuation K (m : K)
          ≤ valuation K (p : K) * 1 := by
            gcongr
            exact_mod_cast valuation_intCast_le_one K m
        _ < 1 := by simp [valuation_p_lt_one K p]
    rw [h1] at h
    exact absurd h (not_le.mpr h2)
  · intro hp
    have h1 : valuation K (q.den : K) = 1 := by
      have := (valuation_intCast_eq_one_iff K p q.den).mpr (by exact_mod_cast hp)
      exact_mod_cast this
    rw [h1]
    exact valuation_intCast_le_one K q.num
theorem isEquiv_comap_ratCast :
    ((valuation K).comap (Rat.castHom K)).IsEquiv (Rat.padicValuation p) :=
  Valuation.isEquiv_of_val_le_one fun q => by
    simp [valuation_ratCast_le_one_iff K p, Rat.padicValuation_le_one_iff]
section Embedding
noncomputable abbrev ratHom : WithVal (Rat.padicValuation p) →+* K :=
  (Rat.castHom K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom
theorem continuousAt_ratHom : ContinuousAt (ratHom K p) 0 := by
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' K)).mpr fun γ hγ => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (valuation_p_lt_one K p) (Units.mk0 γ hγ)
  set v := Rat.padicValuation p
  set t : WithVal v := (WithVal.equiv v).symm ((p : ℚ) ^ n)
  refine ⟨valuation (WithVal v) t, ?_, fun x hx => ?_⟩
  · simp [t, Nat.Prime.ne_zero Fact.out]
  · simp only [Set.mem_ofPred_eq] at hx ⊢
    have h1 := (ValuativeRel.isEquiv (valuation (WithVal v)) (WithVal.valuation v)).lt_iff_lt.mp hx
    have h2 : v (WithVal.equiv v x) < v ((p : ℚ) ^ n) := by simpa [t] using h1
    have h3 := (isEquiv_comap_ratCast K p).lt_iff_lt.mpr h2
    simp only [Valuation.comap_apply, Rat.coe_castHom] at h3
    calc valuation K (ratHom K p x) = valuation K ((WithVal.equiv v x : ℚ) : K) := rfl
      _ < valuation K (((p : ℚ) ^ n : ℚ) : K) := h3
      _ = valuation K (p : K) ^ n := by simp
      _ < γ := hn
section Uniform
local instance uniformSpaceK : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
local instance isUniformAddGroupK : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
theorem uniformContinuous_ratHom : UniformContinuous (ratHom K p) :=
  uniformContinuous_of_continuousAt_zero (ratHom K p) (continuousAt_ratHom K p)
noncomputable def padicHom : ℚ_[p] →+* K :=
  IsDenseInducing.extendRingHom Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)
end Uniform
end Embedding
end CharZero
end GroundTheory.LocalField


