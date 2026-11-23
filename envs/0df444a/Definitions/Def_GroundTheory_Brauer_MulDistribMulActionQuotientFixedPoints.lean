-- Prove2me | Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
-- name    : GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:35.122187+00:00
-- url     : https://prove2.me/theorems/cd326f81-0bcb-4449-aaab-6c48bcf813fd
-- title:
--   Mul Distrib Mul Action Quotient Fixed Points
-- statement:
--   Definitions and structural lemmas for Mul Distrib Mul Action Quotient Fixed Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open groupCohomology
universe u v u' v'
section Cochains
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
def mulCocycles₂ : Subgroup (G × G → M) where
  carrier := {f | IsMulCocycle₂ f}
  one_mem' := by
    intro g h j
    simp
  mul_mem' := by
    intro f k hf hk g h j
    simp only [Pi.mul_apply]
    rw [mul_mul_mul_comm, hf g h j, hk g h j, smul_mul', mul_mul_mul_comm]
  inv_mem' := by
    intro f hf g h j
    simp only [Pi.inv_apply]
    rw [← mul_inv, hf g h j, mul_inv, smul_inv']
def mulCoboundaries₂ : Subgroup (G × G → M) where
  carrier := {f | IsMulCoboundary₂ f}
  one_mem' := ⟨1, fun g h => by simp⟩
  mul_mem' := by
    rintro f k ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, fun g h => ?_⟩
    simp only [Pi.mul_apply, ← hx g h, ← hy g h, smul_mul']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  inv_mem' := by
    rintro f ⟨x, hx⟩
    refine ⟨x⁻¹, fun g h => ?_⟩
    simp only [Pi.inv_apply, ← hx g h, smul_inv']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel
variable {G M}
@[simp]
theorem mem_mulCocycles₂_iff (f : G × G → M) : f ∈ mulCocycles₂ G M ↔ IsMulCocycle₂ f :=
  Iff.rfl
@[simp]
theorem mem_mulCoboundaries₂_iff (f : G × G → M) :
    f ∈ mulCoboundaries₂ G M ↔ IsMulCoboundary₂ f :=
  Iff.rfl
end Cochains
section H2mul
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
abbrev H2mul : Type (max u v) :=
  mulCocycles₂ G M ⧸ (mulCoboundaries₂ G M).subgroupOf (mulCocycles₂ G M)
namespace H2mul
def mk : mulCocycles₂ G M →* H2mul G M :=
  QuotientGroup.mk' ((mulCoboundaries₂ G M).subgroupOf (mulCocycles₂ G M))
variable {G M}
theorem mk_surjective : Function.Surjective (mk G M) :=
  QuotientGroup.mk'_surjective _
@[elab_as_elim]
theorem induction_on {C : H2mul G M → Prop} (x : H2mul G M) (h : ∀ f, C (mk G M f)) : C x := by
  obtain ⟨f, rfl⟩ := mk_surjective x
  exact h f
theorem mk_eq_one_iff (f : mulCocycles₂ G M) :
    mk G M f = 1 ↔ IsMulCoboundary₂ (f : G × G → M) := by
  rw [mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl
section Functoriality
variable {G' : Type u'} {M' : Type v'} [Group G'] [CommGroup M'] [MulDistribMulAction G' M']
def mapCocycles₂ (f : G' →* G) (φ : M →* M') (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) :
    mulCocycles₂ G M →* mulCocycles₂ G' M' where
  toFun c := ⟨fun p => φ ((c : G × G → M) (f p.1, f p.2)), by
    intro g h j
    simp only [map_mul, ← hφ]
    rw [← map_mul, c.2 (f g) (f h) (f j), map_mul]⟩
  map_one' := by
    ext p
    simp
  map_mul' c c' := by
    ext p
    simp
@[simp]
theorem mapCocycles₂_apply (f : G' →* G) (φ : M →* M')
    (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) (c : mulCocycles₂ G M) (p : G' × G') :
    (mapCocycles₂ f φ hφ c : G' × G' → M') p = φ ((c : G × G → M) (f p.1, f p.2)) :=
  rfl
def mapPair (f : G' →* G) (φ : M →* M') (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) :
    H2mul G M →* H2mul G' M' :=
  QuotientGroup.map _ _ (mapCocycles₂ f φ hφ) (by
    rintro c ⟨x, hx⟩
    refine ⟨fun g => φ (x (f g)), fun g h => ?_⟩
    have hxgh := hx (f g) (f h)
    change _ = (c : G × G → M) (f g, f h) at hxgh
    change _ = φ ((c : G × G → M) (f g, f h))
    rw [← hxgh]
    simp only [map_mul, map_div, hφ])
@[simp]
theorem mapPair_mk (f : G' →* G) (φ : M →* M') (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m)
    (c : mulCocycles₂ G M) :
    mapPair f φ hφ (mk G M c) = mk G' M' (mapCocycles₂ f φ hφ c) :=
  rfl
variable {N : Type v'} [CommGroup N] [MulDistribMulAction G N]
def map (φ : M →*[G] N) : H2mul G M →* H2mul G N :=
  mapPair (MonoidHom.id G) (φ : M →* N) (fun g m => by simp)
@[simp]
theorem map_mk (φ : M →*[G] N) (c : mulCocycles₂ G M) :
    map φ (mk G M c) =
      mk G N (mapCocycles₂ (MonoidHom.id G) (φ : M →* N) (fun g m => by simp) c) :=
  rfl
end Functoriality
section ResInf
def res (H : Subgroup G) : H2mul G M →* H2mul H M :=
  mapPair H.subtype (MonoidHom.id M) (fun _ _ => rfl)
@[simp]
theorem res_mk (H : Subgroup G) (c : mulCocycles₂ G M) :
    res H (mk G M c) = mk H M (mapCocycles₂ H.subtype (MonoidHom.id M) (fun _ _ => rfl) c) :=
  rfl
variable (N : Subgroup G) [N.Normal]
theorem smul_mem_fixedPoints_of_normal (g : G) {m : M}
    (hm : m ∈ FixedPoints.subgroup N M) : g • m ∈ FixedPoints.subgroup N M := by
  intro n
  have hn : g⁻¹ * (n : G) * g ∈ N := by
    simpa using ‹N.Normal›.conj_mem _ n.2 g⁻¹
  have := hm ⟨_, hn⟩
  change (g⁻¹ * (n : G) * g) • m = m at this
  change (n : G) • g • m = g • m
  calc (n : G) • g • m = g • (g⁻¹ * (n : G) * g) • m := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • m := by rw [this]
instance mulDistribMulActionQuotientFixedPoints :
    MulDistribMulAction (G ⧸ N) (FixedPoints.subgroup N M) where
  smul q m := Quotient.liftOn' q
    (fun g => (⟨g • (m : M), smul_mem_fixedPoints_of_normal N g m.2⟩ :
      FixedPoints.subgroup N M)) (by
    intro g g' h
    apply Subtype.ext
    rw [QuotientGroup.leftRel_apply] at h
    have := m.2 ⟨_, h⟩
    change (g⁻¹ * g') • (m : M) = m at this
    change g • (m : M) = g' • (m : M)
    conv_lhs => rw [← this]
    rw [← mul_smul, mul_inv_cancel_left])
  one_smul m := Subtype.ext (one_smul G (m : M))
  mul_smul q q' m := by
    induction q using QuotientGroup.induction_on
    induction q' using QuotientGroup.induction_on
    exact Subtype.ext (mul_smul _ _ (m : M))
  smul_mul q m m' := by
    induction q using QuotientGroup.induction_on
    exact Subtype.ext (smul_mul' _ (m : M) m')
  smul_one q := by
    induction q using QuotientGroup.induction_on
    exact Subtype.ext (smul_one _)
@[simp]
theorem coe_mk_smul_fixedPoints (g : G) (m : FixedPoints.subgroup N M) :
    (((g : G ⧸ N) • m : FixedPoints.subgroup N M) : M) = g • (m : M) :=
  rfl
def inf : H2mul (G ⧸ N) (FixedPoints.subgroup N M) →* H2mul G M :=
  mapPair (QuotientGroup.mk' N) (FixedPoints.subgroup N M).subtype (fun _ _ => rfl)
@[simp]
theorem inf_mk (c : mulCocycles₂ (G ⧸ N) (FixedPoints.subgroup N M)) :
    inf N (mk _ _ c) =
      mk G M (mapCocycles₂ (QuotientGroup.mk' N) (FixedPoints.subgroup N M).subtype
        (fun _ _ => rfl) c) :=
  rfl
end ResInf
end H2mul
end H2mul
section Bridge
variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
namespace H2mul
noncomputable def toH2Cocycles :
    mulCocycles₂ G M →* Multiplicative (H2 (Rep.ofMulDistribMulAction G M)) where
  toFun c := Multiplicative.ofAdd (H2π (Rep.ofMulDistribMulAction G M)
    (cocyclesOfIsMulCocycle₂ (f := (c : G × G → M)) c.2))
  map_one' := by
    have h0 : cocyclesOfIsMulCocycle₂ (f := ((1 : mulCocycles₂ G M) : G × G → M))
        (1 : mulCocycles₂ G M).2 = 0 := Subtype.ext rfl
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    rw [h0, map_zero]
  map_mul' c c' := by
    rw [← ofAdd_add]
    congr 1
    rw [← map_add]
    rfl
theorem toH2Cocycles_eq_one_iff (c : mulCocycles₂ G M) :
    toH2Cocycles c = 1 ↔ IsMulCoboundary₂ (c : G × G → M) := by
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, H2π_eq_zero_iff]
  constructor
  · intro h
    exact isMulCoboundary₂_of_mem_coboundaries₂ _ h
  · intro h
    exact (coboundariesOfIsMulCoboundary₂ h).2
noncomputable def mulEquivH2 :
    H2mul G M ≃* Multiplicative (H2 (Rep.ofMulDistribMulAction G M)) :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ toH2Cocycles (fun c hc => (toH2Cocycles_eq_one_iff c).2 hc)) (by
    constructor
    · rw [injective_iff_map_eq_one]
      intro x
      induction x using induction_on with
      | h c =>
        intro hx
        exact (mk_eq_one_iff c).2 ((toH2Cocycles_eq_one_iff c).1 hx)
    · intro y
      induction y using Multiplicative.rec with
      | ofAdd y =>
      induction y using H2_induction_on with
      | h y =>
      exact ⟨mk G M ⟨Additive.toMul ∘ (y : G × G → Rep.ofMulDistribMulAction G M),
        isMulCocycle₂_of_mem_cocycles₂ _ y.2⟩, rfl⟩)
end H2mul
end Bridge
end GroundTheory.Brauer


