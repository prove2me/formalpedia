-- Prove2me | solution 1 for AlgebraicCurve.Place.ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5717aec6-f8df-5a74-b9ca-acde804f0de6

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Galois.Basic
import Theorems.Thm_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped Pointwise

namespace GR

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem ord_coe_eq_of_eq_unit_mul_pow (w : Place K F') {x ϖ : w.toValuationSubring}
    (hϖ : Irreducible ϖ) {u : w.toValuationSubringˣ} {m : ℕ} (hx : x = u * ϖ ^ m) :
    w.ord (x : F') = m := by
  have h := w.ord_unit_smul_zpow u hϖ (m : ℤ)
  rw [zpow_natCast] at h
  rw [hx]
  push_cast
  exact h

theorem mem_maximalIdeal_pow_iff (w : Place K F') {x : w.toValuationSubring} (hx : x ≠ 0) (n : ℕ) :
    x ∈ maximalIdeal w.toValuationSubring ^ n ↔ (n : ℤ) ≤ w.ord (x : F') := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨m, u, hxeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_coe_eq_of_eq_unit_mul_pow w hϖ hxeq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, hxeq, Units.dvd_mul_left, Nat.cast_le]
  exact pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit

theorem one_le_ord_of_mem_maximalIdeal (w : Place K F') {x : w.toValuationSubring} (hx0 : x ≠ 0)
    (hx : x ∈ maximalIdeal w.toValuationSubring) : 1 ≤ w.ord (x : F') := by
  have h := (mem_maximalIdeal_pow_iff w hx0 1).mp (by rwa [pow_one])
  exact_mod_cast h

variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']

theorem restrictInclusion_ne_zero (w : Place K F') {r : (w.restrict F).toValuationSubring} (hr : r ≠ 0) :
    Place.restrictInclusion F w r ≠ 0 := by
  intro h
  apply hr
  have h1 : ((Place.restrictInclusion F w r : w.toValuationSubring) : F') = 0 := by
    rw [h]; rfl
  rw [Place.coe_restrictInclusion, map_eq_zero_iff _ (algebraMap F F').injective] at h1
  exact Subtype.ext h1

theorem ramificationIdx_eq_ramificationIndex (w : Place K F') :
    @Ideal.ramificationIdx' _ _ _ _ (Place.restrictInclusion F w).toAlgebra
        (maximalIdeal (w.restrict F).toValuationSubring) (maximalIdeal w.toValuationSubring) =
      w.ramificationIndex F := by
  letI := (Place.restrictInclusion F w).toAlgebra
  have hepos := w.ramificationIndex_pos (F := F)
  apply Ideal.ramificationIdx_spec
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap]
    by_cases hr0 : r = 0
    · rw [hr0, map_zero]; exact Ideal.zero_mem _
    have h1 : 1 ≤ (w.restrict F).ord (r : F) := one_le_ord_of_mem_maximalIdeal _ hr0 hr
    change Place.restrictInclusion F w r ∈ maximalIdeal w.toValuationSubring ^ w.ramificationIndex F
    rw [mem_maximalIdeal_pow_iff w (restrictInclusion_ne_zero w hr0)]
    show ((w.ramificationIndex F : ℕ) : ℤ) ≤ w.ord (algebraMap F F' (r : F))
    rw [w.ord_restrict]
    nlinarith
  · intro hle
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (w.restrict F).toValuationSubring
    have hmem : ϖ ∈ maximalIdeal (w.restrict F).toValuationSubring := by
      rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
    have h := hle (Ideal.mem_map_of_mem (algebraMap _ w.toValuationSubring) hmem)
    change Place.restrictInclusion F w ϖ ∈ maximalIdeal w.toValuationSubring ^ (w.ramificationIndex F + 1) at h
    rw [mem_maximalIdeal_pow_iff w (restrictInclusion_ne_zero w hϖ.ne_zero)] at h
    have h2 : w.ord ((Place.restrictInclusion F w ϖ : w.toValuationSubring) : F') = w.ramificationIndex F := by
      rw [Place.coe_restrictInclusion, w.ord_restrict, (w.restrict F).ord_coe_irreducible hϖ, mul_one]
    rw [h2] at h
    push_cast at h
    omega

theorem inertiaDeg_eq_inertiaDeg (w : Place K F') :
    @Ideal.inertiaDeg' _ _ _ _ (Place.restrictInclusion F w).toAlgebra
        (maximalIdeal (w.restrict F).toValuationSubring) (maximalIdeal w.toValuationSubring) =
      w.inertiaDeg F := by
  letI := (Place.restrictInclusion F w).toAlgebra
  haveI hlo : (maximalIdeal w.toValuationSubring).LiesOver (maximalIdeal (w.restrict F).toValuationSubring) :=
    ⟨(IsLocalRing.maximalIdeal_comap (Place.restrictInclusion F w)).symm⟩
  rw [Ideal.inertiaDeg_algebraMap]
  have h : (inferInstance : Algebra ((w.restrict F).toValuationSubring ⧸ maximalIdeal (w.restrict F).toValuationSubring)
      (w.toValuationSubring ⧸ maximalIdeal w.toValuationSubring)) =
      ((Place.restrictResidueMap F w).toAlgebra : Algebra (w.restrict F).ResidueField w.ResidueField) := by
    refine Algebra.algebra_ext _ _ fun x => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  unfold Place.inertiaDeg
  exact congrArg (fun I : Algebra ((w.restrict F).toValuationSubring ⧸ maximalIdeal (w.restrict F).toValuationSubring)
      (w.toValuationSubring ⧸ maximalIdeal w.toValuationSubring) => @Module.finrank _ _ _ _ (@Algebra.toModule _ _ _ _ I)) h

theorem stab_iff {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M] [Algebra L M]
    [IsScalarTower k L M] (c : Place k M) (σ : M ≃ₐ[L] M) :
    SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c ↔
      σ ∈ c.toValuationSubring.decompositionSubgroup L := by
  have key : SemilinearAut.ofAlgAut (σ.restrictScalars k) • c.toValuationSubring = σ • c.toValuationSubring := by
    ext x
    simp only [ValuationSubring.mem_smul_pointwise_iff_exists, SemilinearAut.ofAlgAut_smul,
      AlgEquiv.restrictScalars_apply, AlgEquiv.smul_def]
  rw [MulAction.mem_stabilizer_iff, ← key, ← SemilinearAut.smul_toValuationSubring]
  exact ⟨fun h => congrArg Place.toValuationSubring h, fun h => Place.ext h⟩

theorem card_stab_eq {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M] [Algebra L M]
    [IsScalarTower k L M] (c : Place k M) :
    Nat.card {σ : M ≃ₐ[L] M // SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c} =
      Nat.card ↥(c.toValuationSubring.decompositionSubgroup L) :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun σ => stab_iff c σ))

theorem tower_bridge (w : Place K F') {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [iRS : Algebra (w.restrict F).toValuationSubring w.toValuationSubring]
    [iST : Algebra w.toValuationSubring T] [iRT : Algebra (w.restrict F).toValuationSubring T]
    (hRS : iRS = (Place.restrictInclusion F w).toAlgebra)
    (hloc : IsLocalHom (algebraMap w.toValuationSubring T))
    (hinj : Function.Injective (algebraMap w.toValuationSubring T))
    (htower : ∀ r, algebraMap _ T r = algebraMap _ T (Place.restrictInclusion F w r)) :
    (maximalIdeal (w.restrict F).toValuationSubring).ramificationIdx' (maximalIdeal T) *
        (maximalIdeal (w.restrict F).toValuationSubring).inertiaDeg' (maximalIdeal T) =
      (w.ramificationIndex F * w.inertiaDeg F) *
        ((maximalIdeal w.toValuationSubring).ramificationIdx' (maximalIdeal T) *
          (maximalIdeal w.toValuationSubring).inertiaDeg' (maximalIdeal T)) := by
  haveI := hloc
  have e1 := ramificationIdx_eq_ramificationIndex (F := F) w
  have f1 := inertiaDeg_eq_inertiaDeg (F := F) w
  rw [← hRS] at e1 f1
  have halgRS : ∀ r, algebraMap (w.restrict F).toValuationSubring w.toValuationSubring r = Place.restrictInclusion F w r := by
    intro r; rw [hRS]; rfl
  haveI : IsScalarTower (w.restrict F).toValuationSubring w.toValuationSubring T :=
    IsScalarTower.of_algebraMap_eq fun r => by rw [halgRS]; exact htower r
  haveI : IsLocalHom (algebraMap (w.restrict F).toValuationSubring w.toValuationSubring) := by
    have : algebraMap (w.restrict F).toValuationSubring w.toValuationSubring = Place.restrictInclusion F w :=
      RingHom.ext halgRS
    rw [this]; infer_instance
  haveI : (maximalIdeal w.toValuationSubring).LiesOver (maximalIdeal (w.restrict F).toValuationSubring) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap (w.restrict F).toValuationSubring w.toValuationSubring)).symm⟩
  haveI : (maximalIdeal T).LiesOver (maximalIdeal w.toValuationSubring) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap w.toValuationSubring T)).symm⟩
  haveI : Module.IsTorsionFree (w.restrict F).toValuationSubring w.toValuationSubring :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (fun a b h => by_contra fun hab => restrictInclusion_ne_zero w (sub_ne_zero.mpr hab)
        (by rw [← halgRS, map_sub]; exact sub_eq_zero.mpr h))
  haveI : Module.IsTorsionFree w.toValuationSubring T := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  rw [Ideal.ramificationIdx_algebra_tower' (maximalIdeal (w.restrict F).toValuationSubring)
        (maximalIdeal w.toValuationSubring) (maximalIdeal T),
    Ideal.inertiaDeg_algebra_tower (maximalIdeal (w.restrict F).toValuationSubring)
        (maximalIdeal w.toValuationSubring) (maximalIdeal T),
    e1, f1]
  ring

end GR

open GR in
theorem solution
    {k F F' M : Type*} [Field k] [Field F] [Field F'] [Field M]
    [Algebra k F] [Algebra k F'] [Algebra k M] [Algebra F F'] [Algebra F M] [Algebra F' M]
    [IsScalarTower k F F'] [IsScalarTower k F M] [IsScalarTower k F' M] [IsScalarTower F F' M]
    [FiniteDimensional F F'] [FiniteDimensional F' M] [FiniteDimensional F M] [IsGalois F M]
    (c : Place k M) :
    (c.restrict F').ramificationIndex F * (c.restrict F').inertiaDeg F *
        Nat.card {σ : M ≃ₐ[F'] M // SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c} =
      Nat.card {σ : M ≃ₐ[F] M // SemilinearAut.ofAlgAut (σ.restrictScalars k) • c = c} := by
  classical
  haveI : IsGalois F' M := IsGalois.tower_top_of_isGalois F F' M
  rw [card_stab_eq c, card_stab_eq c]

  letI algRM : Algebra ((c.restrict F').restrict F).toValuationSubring M :=
    ((algebraMap F M).comp (algebraMap ((c.restrict F').restrict F).toValuationSubring F)).toAlgebra
  haveI : IsScalarTower ((c.restrict F').restrict F).toValuationSubring F M :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  letI algSM : Algebra (c.restrict F').toValuationSubring M :=
    ((algebraMap F' M).comp (algebraMap (c.restrict F').toValuationSubring F')).toAlgebra
  haveI : IsScalarTower (c.restrict F').toValuationSubring F' M :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  have hRT : ∀ r : ((c.restrict F').restrict F).toValuationSubring,
      algebraMap _ M r ∈ c.toValuationSubring := by
    intro r
    show algebraMap F M (r : F) ∈ c.toValuationSubring
    rw [IsScalarTower.algebraMap_apply F F' M]
    exact r.2
  have hST : ∀ s : (c.restrict F').toValuationSubring, algebraMap _ M s ∈ c.toValuationSubring := fun s => s.2
  have hxR : ∀ r : ((c.restrict F').restrict F).toValuationSubring,
      (⟨algebraMap _ M r, hRT r⟩ : c.toValuationSubring) =
        Place.restrictInclusion F' c (Place.restrictInclusion F (c.restrict F') r) := by
    intro r
    apply Subtype.ext
    show algebraMap F M (r : F) = algebraMap F' M (algebraMap F F' (r : F))
    exact IsScalarTower.algebraMap_apply F F' M (r : F)
  have hxS : ∀ s : (c.restrict F').toValuationSubring,
      (⟨algebraMap _ M s, hST s⟩ : c.toValuationSubring) = Place.restrictInclusion F' c s := fun s => rfl
  have hRTmax : ∀ r : ((c.restrict F').restrict F).toValuationSubring,
      algebraMap _ M r ∈ c.toValuationSubring.nonunits ↔ r ∈ maximalIdeal _ := by
    intro r
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    constructor
    · rintro ⟨_, h⟩
      rwa [hxR, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, isUnit_map_iff, ← mem_nonunits_iff,
        ← IsLocalRing.mem_maximalIdeal] at h
    · intro h
      refine ⟨hRT r, ?_⟩
      rw [hxR, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, isUnit_map_iff, ← mem_nonunits_iff,
        ← IsLocalRing.mem_maximalIdeal]
      exact h
  have hSTmax : ∀ s : (c.restrict F').toValuationSubring,
      algebraMap _ M s ∈ c.toValuationSubring.nonunits ↔ s ∈ maximalIdeal _ := by
    intro s
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    constructor
    · rintro ⟨_, h⟩
      rwa [hxS, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
        ← IsLocalRing.mem_maximalIdeal] at h
    · intro h
      refine ⟨hST s, ?_⟩
      rw [hxS, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
        ← IsLocalRing.mem_maximalIdeal]
      exact h
  obtain ⟨-, h1⟩ := ValuationSubring.exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    F c.toValuationSubring hRT hRTmax
  obtain ⟨-, h2⟩ := ValuationSubring.exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    F' c.toValuationSubring hST hSTmax
  rw [h1, h2]
  have hloc : IsLocalHom ((algebraMap (c.restrict F').toValuationSubring M).codRestrict c.toValuationSubring hST) := by
    have : (algebraMap (c.restrict F').toValuationSubring M).codRestrict c.toValuationSubring hST =
        Place.restrictInclusion F' c := RingHom.ext fun s => rfl
    rw [this]; infer_instance
  have hinj : Function.Injective ((algebraMap (c.restrict F').toValuationSubring M).codRestrict c.toValuationSubring hST) := by
    intro a b h
    have h' : algebraMap F' M (a : F') = algebraMap F' M (b : F') := congrArg Subtype.val h
    exact Subtype.ext ((algebraMap F' M).injective h')
  have key := tower_bridge (F := F) (c.restrict F') (T := c.toValuationSubring)
    (iRS := (Place.restrictInclusion F (c.restrict F')).toAlgebra)
    (iST := ((algebraMap (c.restrict F').toValuationSubring M).codRestrict c.toValuationSubring hST).toAlgebra)
    (iRT := ((algebraMap ((c.restrict F').restrict F).toValuationSubring M).codRestrict c.toValuationSubring hRT).toAlgebra)
    rfl hloc hinj (fun r => hxR r)
  rw [key]

#print axioms solution

end S_AlgebraicCurve_Place_ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer
end P2MW
export P2MW.S_AlgebraicCurve_Place_ramificationIndex_mul_inertiaDeg_mul_natCard_stabilizer_eq_natCard_stabilizer (solution)
