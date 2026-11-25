-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BdRField
-- name    : GroundTheory_PAdicHodge_BdRField
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:01.537744+00:00
-- url     : https://prove2.me/theorems/9c1118ab-fda2-4376-8e35-df8eaee7f212
-- title:
--   Bd RField
-- statement:
--   Definitions and structural lemmas for Bd RField, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRField.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRGalois
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_irreducible_wittToBDeRhamPlus
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_map_ker_fontaineThetaInvertP
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_maximalIdeal_bDeRhamPlus_eq_span
import Theorems.Thm_GroundTheory_PAdicHodge_irreducible_wittToBDeRhamPlus
import Theorems.Thm_GroundTheory_PAdicHodge_maximalIdeal_bDeRhamPlus_eq_span
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Ideal WittVector IsLocalRing
noncomputable section
namespace GroundTheory.PAdicHodge
section General
variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]
def bDeRhamSubmonoid : Submonoid (BDeRhamPlus R p) :=
  Submonoid.closure <| AdicCompletion.of (RingHom.ker (fontaineThetaInvertP R p)) _ ''
    {a | RingHom.ker (fontaineThetaInvertP R p) = span {a}}
instance instCommRingBDeRham : CommRing (BDeRham R p) :=
  inferInstanceAs (CommRing (Localization (bDeRhamSubmonoid R p)))
instance instAlgebraBDeRham : Algebra (BDeRhamPlus R p) (BDeRham R p) :=
  inferInstanceAs (Algebra (BDeRhamPlus R p) (Localization (bDeRhamSubmonoid R p)))
instance isLocalization_bDeRham : IsLocalization (bDeRhamSubmonoid R p) (BDeRham R p) :=
  inferInstanceAs (IsLocalization (bDeRhamSubmonoid R p) (Localization (bDeRhamSubmonoid R p)))
end General
namespace IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt (normInteger K) p))
local notation "𝔹" => BDeRhamPlus (normInteger K) p
local notation "𝔹dR" => BDeRham (normInteger K) p
local notation "J" => RingHom.ker (fontaineThetaInvertP (normInteger K) p)
theorem maximalIdeal_eq_span_of_ker_eq_span {a : 𝔸} (ha : J = span {a}) :
    maximalIdeal 𝔹 = span {toBDeRhamPlus 𝒪 p a} := by
  rw [← map_ker_fontaineThetaInvertP K p, ha, Ideal.map_span, Set.image_singleton]
variable (K p) in

def varpi : 𝔹 := wittToBDeRhamPlus 𝒪 p (kerThetaGenerator K p)
variable (K p) in
theorem maximalIdeal_eq_span_varpi : maximalIdeal 𝔹 = span {varpi K p} :=
  maximalIdeal_bDeRhamPlus_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
theorem ne_zero_of_maximalIdeal_eq_span {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) : π ≠ 0 := by
  rintro rfl
  rw [span_singleton_eq_bot.2 rfl] at hπ
  exact IsDiscreteValuationRing.not_a_field 𝔹 hπ
variable (K p) in
theorem varpi_mem_bDeRhamSubmonoid : varpi K p ∈ bDeRhamSubmonoid 𝒪 p := by
  refine Submonoid.subset_closure ⟨algebraMap _ 𝔸 (kerThetaGenerator K p), ?_, rfl⟩
  exact ker_fontaineThetaInvertP (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
variable (K p) in
theorem bDeRhamSubmonoid_le_nonZeroDivisors : bDeRhamSubmonoid 𝒪 p ≤ nonZeroDivisors 𝔹 := by
  refine Submonoid.closure_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (ne_zero_of_maximalIdeal_eq_span
    (maximalIdeal_eq_span_of_ker_eq_span ha))
theorem isUnit_algebraMap_bDeRham {x : 𝔹} (hx : x ≠ 0) : IsUnit (algebraMap 𝔹 𝔹dR x) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx
    (irreducible_wittToBDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p))
  rw [map_mul, map_pow]
  exact (u.isUnit.map _).mul ((IsLocalization.map_units (M := bDeRhamSubmonoid 𝒪 p) 𝔹dR
    ⟨varpi K p, varpi_mem_bDeRhamSubmonoid K p⟩).pow n)
instance isFractionRing_bDeRham : IsFractionRing 𝔹 𝔹dR := by
  have hS := bDeRhamSubmonoid_le_nonZeroDivisors K p
  have hL : IsLocalization (bDeRhamSubmonoid 𝒪 p) 𝔹dR := inferInstance
  rw [IsFractionRing, isLocalization_iff] at *
  refine ⟨fun y => isUnit_algebraMap_bDeRham (nonZeroDivisors.coe_ne_zero y), fun z => ?_,
    fun {x y} h => ?_⟩
  · obtain ⟨⟨x, s⟩, hs⟩ := hL.2.1 z
    exact ⟨⟨x, ⟨s, hS s.2⟩⟩, hs⟩
  · obtain ⟨c, hc⟩ := hL.2.2 h
    exact ⟨⟨c, hS c.2⟩, hc⟩
instance instFieldBDeRham : Field 𝔹dR := IsFractionRing.toField 𝔹
theorem algebraMap_bDeRham_injective : Function.Injective (algebraMap 𝔹 𝔹dR) :=
  IsFractionRing.injective 𝔹 𝔹dR
theorem algebraMap_ne_zero_of_maximalIdeal_eq_span {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) :
    algebraMap 𝔹 𝔹dR π ≠ 0 :=
  (map_ne_zero_iff _ algebraMap_bDeRham_injective).2 (ne_zero_of_maximalIdeal_eq_span hπ)
variable (K p) in

def fil (i : ℤ) : Submodule 𝔹 𝔹dR := Submodule.span 𝔹 {algebraMap 𝔹 𝔹dR (varpi K p) ^ i}
theorem algebraMap_units_zpow (u : 𝔹ˣ) (i : ℤ) :
    algebraMap 𝔹 𝔹dR (↑u) ^ i = algebraMap 𝔹 𝔹dR ↑(u ^ i) := by
  rcases i with n | n
  · simp only [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  · rw [zpow_negSucc, zpow_negSucc, ← map_pow, ← Units.val_pow_eq_pow_val]
    exact (map_units_inv (algebraMap 𝔹 𝔹dR) _).symm
theorem fil_eq_span {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    fil K p i = Submodule.span 𝔹 {algebraMap 𝔹 𝔹dR π ^ i} := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1
    (hπ.symm.trans (maximalIdeal_eq_span_varpi K p))
  rw [fil, ← hu, map_mul, mul_zpow, algebraMap_units_zpow, mul_comm (algebraMap 𝔹 𝔹dR π ^ i),
    ← Algebra.smul_def, Submodule.span_singleton_smul_eq (Units.isUnit _)]
theorem mem_fil_iff {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} {x : 𝔹dR} :
    x ∈ fil K p i ↔ ∃ b : 𝔹, x = algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b := by
  rw [fil_eq_span hπ, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩
def filMk {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) : 𝔹 →ₗ[𝔹] fil K p i where
  toFun b := ⟨algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR b, (mem_fil_iff hπ).2 ⟨b, rfl⟩⟩
  map_add' a b := Subtype.ext (by simp only [map_add, mul_add, Submodule.coe_add])
  map_smul' c b := Subtype.ext (by
    simp only [smul_eq_mul, map_mul, Submodule.coe_smul, RingHom.id_apply, Algebra.smul_def]
    ring)
theorem filMk_bijective {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    Function.Bijective (filMk (K := K) hπ i) := by
  have hne := zpow_ne_zero i (algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hπ)
  refine ⟨fun a b h => algebraMap_bDeRham_injective (mul_left_cancel₀ hne
    (congrArg Subtype.val h)), fun x => ?_⟩
  obtain ⟨b, hb⟩ := (mem_fil_iff hπ).1 x.2
  exact ⟨b, Subtype.ext hb.symm⟩
def filEquiv {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) : fil K p i ≃ₗ[𝔹] 𝔹 :=
  (LinearEquiv.ofBijective (filMk hπ i) (filMk_bijective hπ i)).symm
theorem coe_eq_filEquiv {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    (x : 𝔹dR) = algebraMap 𝔹 𝔹dR π ^ i * algebraMap 𝔹 𝔹dR (filEquiv hπ i x) :=
  (congrArg Subtype.val
    ((LinearEquiv.ofBijective (filMk hπ i) (filMk_bijective hπ i)).apply_symm_apply x)).symm
def grMap {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) : fil K p i →+ K :=
  (thetaBDeRhamPlusField p).toAddMonoidHom.comp (filEquiv hπ i).toLinearMap.toAddMonoidHom
theorem grMap_apply {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    grMap hπ i x = thetaBDeRhamPlusField p (filEquiv hπ i x) := rfl
theorem grMap_surjective {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    Function.Surjective (grMap (K := K) hπ i) :=
  (surjective_thetaBDeRhamPlusField p).comp (filEquiv hπ i).surjective
theorem grMap_eq_zero_iff {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) {i : ℤ} (x : fil K p i) :
    grMap hπ i x = 0 ↔ (x : 𝔹dR) ∈ fil K p (i + 1) := by
  have hne := algebraMap_ne_zero_of_maximalIdeal_eq_span (K := K) hπ
  rw [grMap_apply, ← RingHom.mem_ker, ← maximalIdeal_bDeRhamPlus (K := K) (p := p), hπ,
    mem_span_singleton, mem_fil_iff hπ, coe_eq_filEquiv hπ x]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, map_mul, zpow_add_one₀ hne]; ring⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, algebraMap_bDeRham_injective ?_⟩
    rw [zpow_add_one₀ hne, mul_assoc] at hc
    rw [map_mul]
    exact mul_left_cancel₀ (zpow_ne_zero i hne) hc
theorem ker_grMap {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    (grMap hπ i).ker = ((fil K p (i + 1)).comap (fil K p i).subtype).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, grMap_eq_zero_iff]
  rfl
def grEquiv {π : 𝔹} (hπ : maximalIdeal 𝔹 = span {π}) (i : ℤ) :
    (fil K p i) ⧸ ((fil K p (i + 1)).comap (fil K p i).subtype) ≃+ K :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_grMap hπ i).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (grMap_surjective hπ i))
end IsPerfectoidField
section Galois
variable {p : ℕ} [Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p
def galBdRField (σ : Gal(PadicAlgCl p/L)) : 𝔹dR ≃+* 𝔹dR :=
  IsFractionRing.ringEquivOfRingEquiv (galBdR σ)
theorem galBdRField_algebraMap (σ : Gal(PadicAlgCl p/L)) (b : 𝔹) :
    galBdRField σ (algebraMap 𝔹 𝔹dR b) = algebraMap 𝔹 𝔹dR (σ • b) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
theorem galBdRField_one : galBdRField (1 : Gal(PadicAlgCl p/L)) = RingEquiv.refl 𝔹dR := by
  refine RingEquiv.toRingHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors 𝔹)
    (RingHom.ext fun b => ?_))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    galBdRField_algebraMap, one_smul, RingEquiv.coe_ringHom_refl, RingHom.id_apply]
theorem galBdRField_mul (σ τ : Gal(PadicAlgCl p/L)) :
    galBdRField (σ * τ) = (galBdRField τ).trans (galBdRField σ) := by
  refine RingEquiv.toRingHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors 𝔹)
    (RingHom.ext fun b => ?_))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    galBdRField_algebraMap, mul_smul, RingEquiv.coe_trans, Function.comp_apply]
instance instMulSemiringActionBdRField : MulSemiringAction Gal(PadicAlgCl p/L) 𝔹dR where
  smul σ x := galBdRField σ x
  one_smul x := by
    change galBdRField 1 x = x
    rw [galBdRField_one]
    rfl
  mul_smul σ τ x := by
    change galBdRField (σ * τ) x = galBdRField σ (galBdRField τ x)
    rw [galBdRField_mul]
    rfl
  smul_zero σ := map_zero (galBdRField σ)
  smul_add σ := map_add (galBdRField σ)
  smul_one σ := map_one (galBdRField σ)
  smul_mul σ := map_mul (galBdRField σ)
end Galois
end GroundTheory.PAdicHodge


