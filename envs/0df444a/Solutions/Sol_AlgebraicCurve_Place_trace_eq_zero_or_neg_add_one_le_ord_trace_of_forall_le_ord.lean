-- Prove2me | solution 1 for AlgebraicCurve.Place.trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6ab3c84e-97c3-561e-ab81-1ff8f62bdeaa

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve ModularCurve

namespace TraceCeil

set_option linter.unusedSectionVars false

open IsDedekindDomain IsLocalRing

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end Generic

section Fibre

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (v : Place K F)

scoped instance instFreeIntegralClosureAt : Module.Free v.toValuationSubring (Place.integralClosureAt F' v) :=
  Module.free_of_finite_type_torsion_free'

abbrev conductorIdeal : Ideal (Place.integralClosureAt F' v) :=
  (maximalIdeal v.toValuationSubring).map (algebraMap v.toValuationSubring (Place.integralClosureAt F' v))

noncomputable scoped instance conductorQuotientAlgebra :
    Algebra (ResidueField v.toValuationSubring) (Place.integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

scoped instance instIsScalarTowerConductorQuot :
    IsScalarTower v.toValuationSubring (ResidueField v.toValuationSubring)
      (Place.integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  IsScalarTower.of_algebraMap_eq' rfl

scoped instance instFiniteConductorQuot :
    Module.Finite (ResidueField v.toValuationSubring) (Place.integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  Module.Finite.of_restrictScalars_finite v.toValuationSubring _ _

scoped instance instIsArtinianConductorQuot : IsArtinianRing (Place.integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  IsArtinianRing.of_finite (ResidueField v.toValuationSubring) _

theorem residue_trace_eq_trace_mk (c : Place.integralClosureAt F' v) :
    residue v.toValuationSubring (Algebra.trace v.toValuationSubring (Place.integralClosureAt F' v) c)
      = Algebra.trace (ResidueField v.toValuationSubring) (Place.integralClosureAt F' v ⧸ conductorIdeal (F' := F') v)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) :=
  (Algebra.trace_quotient_mk (R := v.toValuationSubring) (S := Place.integralClosureAt F' v) c).symm

theorem not_isField_integralClosureAt : ¬ IsField (Place.integralClosureAt F' v) := by
  intro hC
  have hinj : Function.Injective (algebraMap v.toValuationSubring (Place.integralClosureAt F' v)) :=
    Place.algebraMap_integralClosureAt_injective v
  have hO : IsField v.toValuationSubring :=
    ((Algebra.IsIntegral.isField_iff_isField (R := v.toValuationSubring)
      (S := Place.integralClosureAt F' v) hinj).mpr hC)
  exact ValuationSubring.not_isField_of_ne_top F v.ne_top' hO

theorem trace_mem_maximalIdeal_of_forall_ord_pos (c : Place.integralClosureAt F' v)
    (hc : ∀ w : Place K F', w.restrict F = v → 0 < w.ord (algebraMap (Place.integralClosureAt F' v) F' c)) :
    Algebra.trace v.toValuationSubring (Place.integralClosureAt F' v) c ∈ maximalIdeal v.toValuationSubring := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [map_zero]; exact Ideal.zero_mem _

  have hmax : ∀ M : Ideal (Place.integralClosureAt F' v), M.IsMaximal → c ∈ M := by
    intro M hM
    have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (not_isField_integralClosureAt v)
    let P : HeightOneSpectrum (Place.integralClosureAt F' v) := ⟨M, hM.isPrime, hM0⟩
    have hw := Place.restrict_placeOfPrime P
    have hmem := (Place.mem_fiberCenter_iff_ord_pos hw hc0).mpr (hc _ hw)
    rwa [Place.fiberCenter_placeOfPrime] at hmem

  set Q := Place.integralClosureAt F' v ⧸ conductorIdeal (F' := F') v
  have hjac : Ideal.Quotient.mk (conductorIdeal (F' := F') v) c ∈ (⊥ : Ideal Q).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJ⟩
    have := hmax (J.comap (Ideal.Quotient.mk (conductorIdeal (F' := F') v)))
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    exact Ideal.mem_comap.mp this
  have hnil : IsNilpotent (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Q)
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hjac n
    rw [hn] at this
    exact Ideal.mem_bot.mp this

  have htr0 := (Algebra.isNilpotent_trace_of_isNilpotent (R := ResidueField v.toValuationSubring) (S := Q) hnil).eq_zero
  rw [← residue_eq_zero_iff, residue_trace_eq_trace_mk v c]
  exact htr0

theorem trace_eq_zero_or_lt_ord_trace (z : F') (hz0 : z ≠ 0)
    (hz : ∀ w : Place K F', w.restrict F = v → 0 < w.ord z) :
    Algebra.trace F F' z = 0 ∨ 0 < v.ord (Algebra.trace F F' z) := by

  have hrange : z ∈ (algebraMap (Place.integralClosureAt F' v) F').range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := Place.integralClosureAt F' v) (K := F') z fun P => ?_
    have hmem : z ∈ (Place.placeOfPrime P).toValuationSubring :=
      mem_of_ord_nonneg _ hz0 (hz _ (Place.restrict_placeOfPrime P)).le
    rw [Place.placeOfPrime_toValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff] at hmem
    exact hmem
  obtain ⟨c, rfl⟩ := hrange
  have htrace : Algebra.trace F F' (algebraMap (Place.integralClosureAt F' v) F' c)
      = algebraMap v.toValuationSubring F
          (Algebra.trace v.toValuationSubring (Place.integralClosureAt F' v) c) := by
    rw [← Algebra.algebraMap_intTrace (A := v.toValuationSubring) (K := F) (L := F')
      (B := Place.integralClosureAt F' v), Algebra.intTrace_eq_trace]
  by_cases htr : Algebra.trace F F' (algebraMap (Place.integralClosureAt F' v) F' c) = 0
  · exact Or.inl htr
  right
  rw [htrace] at htr ⊢
  have hr0 : Algebra.trace v.toValuationSubring (Place.integralClosureAt F' v) c ≠ 0 := by
    intro h; exact htr (by rw [h, map_zero])
  exact (Place.mem_maximalIdeal_iff_ord_pos' hr0).mp (trace_mem_maximalIdeal_of_forall_ord_pos v c hz)

end Fibre

end TraceCeil
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord.TraceCeil"

open TraceCeil in
theorem solution
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [IsAlgClosed k]
    [IsCurveOver k F] [IsCurveOver k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong k φ) (hsep : SeparableAlong k φ)
    (x : Place k F) (S : Finset (Place k F')) (hS : ∀ y : Place k F', y ∈ S ↔ y.restrictAlong φ hφ = x)
    (a : ℤ) (g : F') (hg : ∀ y ∈ S, -((Place.ramificationIndexAlong φ y : ℤ) * a) + 1 ≤ y.ord g) :
    letI := AlgebraicCurve.algebraAlong φ;
    Algebra.trace F F' g = 0 ∨ -a + 1 ≤ x.ord (Algebra.trace F F' g) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  show Algebra.trace F F' g = 0 ∨ -a + 1 ≤ x.ord (Algebra.trace F F' g)
  by_cases htrg : Algebra.trace F F' g = 0
  · exact Or.inl htrg
  right
  have hg0 : g ≠ 0 := by rintro rfl; exact htrg (map_zero _)

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hordπ : x.ord (π : F) = 1 := x.ord_coe_irreducible hπ

  set z : F' := algebraMap F F' ((π : F) ^ a) * g with hz_def
  have hta0 : ((π : F) ^ a) ≠ 0 := zpow_ne_zero _ hπ0
  have hta0' : algebraMap F F' ((π : F) ^ a) ≠ 0 := (map_ne_zero (algebraMap F F')).mpr hta0
  have hz0 : z ≠ 0 := mul_ne_zero hta0' hg0
  have hzpos : ∀ w : Place k F', w.restrict F = x → 0 < w.ord z := by
    intro w hw
    have hwS : w ∈ S := (hS w).mpr hw
    have hgw := hg w hwS
    have he : (Place.ramificationIndexAlong φ w : ℤ) = (w.ramificationIndex F : ℤ) := rfl
    rw [he] at hgw
    rw [hz_def, w.ord_mul hta0' hg0, map_zpow₀, w.ord_zpow, w.ord_restrict, hw, hordπ]
    nlinarith [hgw]
  have hlin : Algebra.trace F F' z = (π : F) ^ a * Algebra.trace F F' g := by
    rw [hz_def, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rcases trace_eq_zero_or_lt_ord_trace x z hz0 hzpos with h0 | hpos
  · exfalso
    rw [hlin] at h0
    exact htrg ((mul_eq_zero.mp h0).resolve_left hta0)
  · rw [hlin, x.ord_mul hta0 htrg, x.ord_zpow, hordπ] at hpos
    omega

end S_AlgebraicCurve_Place_trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord
end P2MW
export P2MW.S_AlgebraicCurve_Place_trace_eq_zero_or_neg_add_one_le_ord_trace_of_forall_le_ord (solution)
