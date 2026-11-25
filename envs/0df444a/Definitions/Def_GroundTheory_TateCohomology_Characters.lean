-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_Characters
-- name    : GroundTheory_TateCohomology_Characters
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:00:13.610998+00:00
-- url     : https://prove2.me/theorems/a8518d42-d5e4-4284-8b52-efec3843054a
-- title:
--   Characters
-- statement:
--   Definitions and structural lemmas for Characters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Characters.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Theorems.Thm_GroundTheory_GroupCoh_isZero_groupCohomology_trivial_rat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
section Exactness
universe u
variable {k G : Type u} [CommRing k] [Group G]
theorem shortComplex_exact_of_forall {S : ShortComplex (Rep.{u} k G)}
    (h : ∀ x : S.X₂, S.g.hom x = 0 → ∃ y : S.X₁, S.f.hom y = x) : S.Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
    ShortComplex.moduleCat_exact_iff]
  exact h
end Exactness
section Sequence
variable (G : Type) [Group G]
noncomputable def intToRat : Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom ⟨(Int.castAddHom ℚ).toIntLinearMap, fun _ => rfl⟩
noncomputable def ratToRatModInt : Rep.trivial ℤ G ℚ ⟶ Rep.trivial ℤ G (AddCircle (1 : ℚ)) :=
  Rep.ofHom ⟨(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).toIntLinearMap, fun _ => rfl⟩
noncomputable def ratSES : ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (intToRat G) (ratToRatModInt G) (by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun n => ?_))
    change ((n : ℚ) : AddCircle (1 : ℚ)) = 0
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩)
theorem ratSES_shortExact : (ratSES G).ShortExact where
  mono_f := (Rep.mono_iff_injective _).2 fun a b h => Int.cast_injective (α := ℚ) h
  epi_g := (Rep.epi_iff_surjective _).2 fun x => QuotientAddGroup.mk_surjective x
  exact := by
    refine shortComplex_exact_of_forall fun q hq => ?_
    have hq' : ((show ℚ from q) : AddCircle (1 : ℚ)) = 0 := hq
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hq'
    exact ⟨n, by change ((n : ℤ) : ℚ) = (show ℚ from q); rw [← hn, zsmul_one]⟩
end Sequence
section H2
variable (G : Type) [Group G] [Fintype G]
noncomputable def h1RatModIntIso :
    H1 (Rep.trivial ℤ G (AddCircle (1 : ℚ))) ≅ ModuleCat.of ℤ (Additive G →+ AddCircle (1 : ℚ)) :=
  H1IsoOfIsTrivial _
theorem isIso_δ_ratSES : IsIso (groupCohomology.δ (ratSES_shortExact G) 1 2 rfl) :=
  isIso_δ_of_isZero (ratSES_shortExact G) 1 (isZero_groupCohomology_trivial_rat 1)
    (isZero_groupCohomology_trivial_rat 2)
noncomputable def h1RatModIntIsoH2Int :
    H1 (Rep.trivial ℤ G (AddCircle (1 : ℚ))) ≅ H2 (Rep.trivial ℤ G ℤ) :=
  @asIso _ _ _ _ (groupCohomology.δ (ratSES_shortExact G) 1 2 rfl) (isIso_δ_ratSES G)
noncomputable def h2IntIsoHom :
    H2 (Rep.trivial ℤ G ℤ) ≅ ModuleCat.of ℤ (Additive G →+ AddCircle (1 : ℚ)) :=
  (h1RatModIntIsoH2Int G).symm ≪≫ h1RatModIntIso G
noncomputable def h2IntAddEquiv :
    H2 (Rep.trivial ℤ G ℤ) ≃+ (Additive G →+ AddCircle (1 : ℚ)) :=
  (h2IntIsoHom G).toLinearEquiv.toAddEquiv
end H2
section Cyclic
variable {G : Type} [Group G] [Fintype G] (σ : G) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ)
omit [Fintype G] in
include hσ in

theorem forall_mem_zmultiples_ofMul :
    ∀ x : Additive G, x ∈ AddSubgroup.zmultiples (Additive.ofMul σ) := by
  intro x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ x.toMul)
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨k, by rw [← ofMul_zpow, hk, ofMul_toMul]⟩
include hσ in

theorem orderOf_ofAdd_div_card_dvd :
    orderOf (Multiplicative.ofAdd (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ))) ∣
      orderOf σ := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  rw [orderOf_ofAdd_eq_addOrderOf, AddCircle.addOrderOf_period_div Nat.card_pos,
    orderOf_eq_card_of_forall_mem_zpowers hσ]
noncomputable def cyclicChar : Additive G →+ AddCircle (1 : ℚ) :=
  MonoidHom.toAdditiveLeft (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ))
theorem cyclicChar_apply_gen :
    cyclicChar σ hσ (Additive.ofMul σ) = (((1 : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ)) := by
  change Multiplicative.toAdd
    (monoidHomOfForallMemZpowers hσ (orderOf_ofAdd_div_card_dvd σ hσ) σ) = _
  rw [monoidHomOfForallMemZpowers_apply_gen]
  rfl
theorem zmultiples_cyclicChar : AddSubgroup.zmultiples (cyclicChar σ hσ) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  set n := Nat.card G
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective (f (Additive.ofMul σ))
  have h0 : n • f (Additive.ofMul σ) = 0 := by
    have hpow : σ ^ n = 1 := by
      rw [show n = orderOf σ from (orderOf_eq_card_of_forall_mem_zpowers hσ).symm]
      exact pow_orderOf_eq_one σ
    rw [← map_nsmul, ← ofMul_pow, hpow, ofMul_one, map_zero]
  rw [← hq] at h0
  have h1 : (((n : ℚ) * q : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [← nsmul_eq_mul]; exact h0
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).1 h1
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨m, ?_⟩
  refine ((AddMonoidHom.eq_iff_eq_on_generator (forall_mem_zmultiples_ofMul σ hσ) _ _).2 ?_)
  rw [AddMonoidHom.zsmul_apply, cyclicChar_apply_gen, ← hq]
  have hq' : q = m • ((1 : ℚ) / n) := by
    rw [zsmul_one] at hm
    rw [zsmul_eq_mul, hm]; field_simp
  rw [hq']
  rfl
theorem addOrderOf_cyclicChar : addOrderOf (cyclicChar σ hσ) = Nat.card G := by
  have : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  let ev : (Additive G →+ AddCircle (1 : ℚ)) →+ AddCircle (1 : ℚ) :=
    AddMonoidHom.mk' (fun f => f (Additive.ofMul σ)) fun _ _ => rfl
  have hev : Function.Injective ev := fun f g h =>
    (AddMonoidHom.eq_iff_eq_on_generator (forall_mem_zmultiples_ofMul σ hσ) _ _).2 h
  rw [← addOrderOf_injective ev hev]
  change addOrderOf (cyclicChar σ hσ (Additive.ofMul σ)) = _
  rw [cyclicChar_apply_gen, AddCircle.addOrderOf_period_div Nat.card_pos]
noncomputable def cyclicH2Gen : H2 (Rep.trivial ℤ G ℤ) :=
  (h2IntAddEquiv G).symm (cyclicChar σ hσ)
theorem zmultiples_cyclicH2Gen : AddSubgroup.zmultiples (cyclicH2Gen σ hσ) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : h2IntAddEquiv G x ∈ AddSubgroup.zmultiples (cyclicChar σ hσ) := by
    rw [zmultiples_cyclicChar]; trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨m, ?_⟩
  rw [cyclicH2Gen, ← map_zsmul, hm, AddEquiv.symm_apply_apply]
theorem addOrderOf_cyclicH2Gen : addOrderOf (cyclicH2Gen σ hσ) = Nat.card G :=
  (addOrderOf_injective (h2IntAddEquiv G).symm.toAddMonoidHom
    (h2IntAddEquiv G).symm.injective (cyclicChar σ hσ)).trans (addOrderOf_cyclicChar σ hσ)
include hσ in

theorem card_h2Int_of_cyclic : Nat.card (H2 (Rep.trivial ℤ G ℤ)) = Nat.card G := by
  rw [← addOrderOf_cyclicH2Gen σ hσ, ← Nat.card_zmultiples, zmultiples_cyclicH2Gen,
    AddSubgroup.card_top]
noncomputable def zmodAddEquivH2Int : ZMod (Nat.card G) ≃+ H2 (Rep.trivial ℤ G ℤ) :=
  zmodAddEquivOfGenerator (g := cyclicH2Gen σ hσ)
    (fun x => by rw [zmultiples_cyclicH2Gen]; trivial) (card_h2Int_of_cyclic σ hσ)
end Cyclic
end GroundTheory.GroupCoh


