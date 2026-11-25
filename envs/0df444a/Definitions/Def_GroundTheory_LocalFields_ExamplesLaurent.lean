-- Prove2me | Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent
-- name    : GroundTheory_LocalFields_ExamplesLaurent
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:49.333528+00:00
-- url     : https://prove2.me/theorems/38bc1c3c-700d-4c81-b0a1-32b980a33ded
-- title:
--   Examples Laurent
-- statement:
--   Definitions and structural lemmas for Examples Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesLaurent.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Theorems.Thm_GroundTheory_LocalField_EqualChar_residue_teichmullerHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
namespace GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
namespace EqualChar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
noncomputable def uniformizer : 𝒪[K] :=
  (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose
theorem irreducible_uniformizer : Irreducible (uniformizer K) :=
  (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
theorem uniformizer_ne_zero : (uniformizer K : K) ≠ 0 := fun h =>
  (irreducible_uniformizer K).ne_zero (Subtype.ext h)
theorem valuation_uniformizer_lt_one : valuation K (uniformizer K : K) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp (irreducible_uniformizer K).not_isUnit
def ballIdeal (γ : (ValueGroupWithZero K)ˣ) : Ideal 𝒪[K] where
  carrier := {x | valuation K (x : K) < γ}
  add_mem' {a b} ha hb := by
    change valuation K ((a : K) + (b : K)) < γ
    exact lt_of_le_of_lt ((valuation K).map_add _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    change valuation K ((c : K) * (x : K)) < γ
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).mp c.2)) hx
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_ballIdeal {γ : (ValueGroupWithZero K)ˣ} {x : 𝒪[K]} :
    x ∈ ballIdeal K γ ↔ valuation K (x : K) < γ := Iff.rfl
theorem hasBasis_nhds_zero_integer :
    (𝓝 (0 : 𝒪[K])).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero K)ˣ => ((ballIdeal K γ : Ideal 𝒪[K]) : Set 𝒪[K]) := by
  rw [nhds_subtype_eq_comap, ZeroMemClass.coe_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero K).comap Subtype.val).congr
    (fun _ => Iff.rfl) fun γ _ => ?_
  ext x
  simp [mem_ballIdeal]
instance : IsLinearTopology 𝒪[K] 𝒪[K] :=
  IsLinearTopology.mk_of_hasBasis' 𝒪[K] (hasBasis_nhds_zero_integer K)
    fun I r _ hx => I.mul_mem_left r hx
theorem isTopologicallyNilpotent_uniformizer : IsTopologicallyNilpotent (uniformizer K) := by
  refine (hasBasis_nhds_zero_integer K).tendsto_right_iff.mpr fun γ _ => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one K) γ
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [SetLike.mem_coe, mem_ballIdeal, Subring.coe_pow, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_of_le_one zero_le
    (valuation_uniformizer_lt_one K).le hn) hN
variable (p : ℕ) [Fact p.Prime] [CharP K p]
section Uniform
local instance uniformSpaceK : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
local instance isUniformAddGroupK : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
local instance uniformSpaceResidue : UniformSpace 𝓀[K] := ⊥
local instance discreteUniformityResidue : DiscreteUniformity 𝓀[K] := ⟨rfl⟩
noncomputable def powerSeriesHom : PowerSeries 𝓀[K] →+* 𝒪[K] :=
  PowerSeries.eval₂Hom (φ := teichmullerHom K p) continuous_of_discreteTopology
    (isTopologicallyNilpotent_uniformizer K)
theorem powerSeriesHom_apply (F : PowerSeries 𝓀[K]) :
    powerSeriesHom K p F = PowerSeries.eval₂ (teichmullerHom K p) (uniformizer K) F := by
  rw [powerSeriesHom, PowerSeries.coe_eval₂Hom]
theorem powerSeriesHom_X : powerSeriesHom K p PowerSeries.X = uniformizer K := by
  rw [powerSeriesHom_apply, PowerSeries.eval₂_X]
theorem hasSum_powerSeriesHom (F : PowerSeries 𝓀[K]) :
    HasSum (fun d => teichmullerHom K p (PowerSeries.coeff d F) * uniformizer K ^ d)
      (powerSeriesHom K p F) := by
  rw [powerSeriesHom_apply]
  exact PowerSeries.hasSum_eval₂ continuous_of_discreteTopology
    (isTopologicallyNilpotent_uniformizer K) F
theorem powerSeriesHom_surjective : Function.Surjective (powerSeriesHom K p) := by
  intro y
  have hstep : ∀ z : 𝒪[K], ∃ w : 𝒪[K],
      z = teichmullerHom K p (residue 𝒪[K] z) + uniformizer K * w := by
    intro z
    have hm : z - teichmullerHom K p (residue 𝒪[K] z) ∈ maximalIdeal 𝒪[K] := by
      rw [← residue_eq_zero_iff, map_sub, residue_teichmullerHom, sub_self]
    rw [(irreducible_uniformizer K).maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, by rw [mul_comm, hw]; ring⟩
  choose next hnext using hstep
  obtain ⟨rem, hrem0, hremS⟩ : ∃ rem : ℕ → 𝒪[K], rem 0 = y ∧ ∀ n, rem (n + 1) = next (rem n) :=
    ⟨fun n => next^[n] y, rfl, fun n => Function.iterate_succ_apply' next n y⟩
  refine ⟨PowerSeries.mk fun n => residue 𝒪[K] (rem n), ?_⟩
  have hpartial : ∀ n, y = (∑ d ∈ Finset.range n,
      teichmullerHom K p (residue 𝒪[K] (rem d)) * uniformizer K ^ d) +
        rem n * uniformizer K ^ n := by
    intro n
    induction n with
    | zero => simp [hrem0]
    | succ n ih =>
      rw [Finset.sum_range_succ, hremS]
      linear_combination ih + uniformizer K ^ n * hnext (rem n)
  have hT1 := (hasSum_powerSeriesHom K p
    (PowerSeries.mk fun n => residue 𝒪[K] (rem n))).tendsto_sum_nat
  simp only [PowerSeries.coeff_mk] at hT1
  have h0 : Tendsto (fun n => rem n * uniformizer K ^ n) atTop (𝓝 0) :=
    IsLinearTopology.tendsto_mul_zero_of_right rem (fun n => uniformizer K ^ n)
      (isTopologicallyNilpotent_uniformizer K)
  have hT2 : Tendsto (fun n => ∑ d ∈ Finset.range n,
      teichmullerHom K p (residue 𝒪[K] (rem d)) * uniformizer K ^ d) atTop (𝓝 y) := by
    have he : (fun n => ∑ d ∈ Finset.range n,
        teichmullerHom K p (residue 𝒪[K] (rem d)) * uniformizer K ^ d) =
          fun n => y - rem n * uniformizer K ^ n :=
      funext fun n => by rw [eq_sub_iff_add_eq, ← hpartial n]
    rw [he]
    simpa using (tendsto_const_nhds (x := y)).sub h0
  exact tendsto_nhds_unique hT1 hT2
end Uniform
noncomputable def laurentHom : 𝓀[K]⸨X⸩ →+* K :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : PowerSeries 𝓀[K]))
    (g := (Subring.subtype 𝒪[K]).comp (powerSeriesHom K p)) (by
      rintro ⟨_, n, rfl⟩
      simp only [RingHom.comp_apply, map_pow, powerSeriesHom_X, Subring.subtype_apply]
      exact (pow_ne_zero n (uniformizer_ne_zero K)).isUnit)
theorem laurentHom_coe (F : PowerSeries 𝓀[K]) :
    laurentHom K p (F : 𝓀[K]⸨X⸩) = powerSeriesHom K p F :=
  IsLocalization.lift_eq (M := Submonoid.powers (PowerSeries.X : PowerSeries 𝓀[K])) _ F
theorem laurentHom_single (n : ℤ) :
    laurentHom K p (single n 1) = (uniformizer K : K) ^ n := by
  rw [RatFunc.single_zpow, map_zpow₀, ← HahnSeries.ofPowerSeries_X, laurentHom_coe,
    powerSeriesHom_X]
theorem laurentHom_surjective : Function.Surjective (laurentHom K p) := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, map_zero _⟩
  have hvx : 0 < valuation K x := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one K)
    (Units.mk0 (valuation K x)⁻¹ (inv_ne_zero hvx.ne'))
  have hy : valuation K ((uniformizer K : K) ^ m * x) ≤ 1 := by
    rw [map_mul, map_pow]
    have h := mul_lt_mul_of_pos_right hm hvx
    rw [Units.val_mk0, inv_mul_cancel₀ hvx.ne'] at h
    exact h.le
  obtain ⟨F, hF⟩ := powerSeriesHom_surjective K p
    ⟨(uniformizer K : K) ^ m * x, (Valuation.mem_integer_iff _ _).mpr hy⟩
  refine ⟨single (-(m : ℤ)) 1 * (F : 𝓀[K]⸨X⸩), ?_⟩
  rw [map_mul, laurentHom_single, laurentHom_coe, hF, zpow_neg, zpow_natCast, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero K)), one_mul]
noncomputable def laurentEquiv : 𝓀[K]⸨X⸩ ≃+* K :=
  RingEquiv.ofBijective (laurentHom K p) ⟨(laurentHom K p).injective, laurentHom_surjective K p⟩
end EqualChar
end GroundTheory.LocalField


