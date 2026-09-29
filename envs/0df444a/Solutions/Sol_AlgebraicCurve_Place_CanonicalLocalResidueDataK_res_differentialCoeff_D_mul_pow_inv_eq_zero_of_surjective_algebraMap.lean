-- Prove2me | solution 1 for AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f7c0b7c2-b1fc-5281-8f22-645d80861f46

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue

import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "IsDedekindDomain WithZero Module IsLocalRing Module.IsLocalRing KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.CanonicalLocalResidueDataK Place.poleSubmodule"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation adicValuation_ne_zero ord ord_zero ord_one ord_mul ord_inv ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK uniformizer_mem poleSubmodule mem_poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow coe_poleSubmodule_zero laurentTailCoeff laurentTail_remainder_mem_poleSubmodule exists_mem_poleSubmodule"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩

private theorem _root_.AlgebraicCurve.Place.ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f ≠ v.ord g) :
    v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon
    exact h (by simp only [ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, _root_.map_zero] at h1
    rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
      rw [hmax] at h1
    · exact v.adicValuation_ne_zero hf h1.symm
    · exact v.adicValuation_ne_zero hg h1.symm
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩ <;>
    rw [hmax] at h1
  ·
    have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    have h2 : v.ord (f + g) = v.ord f := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    have h2 : v.ord (f + g) = v.ord g := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega

p2m_export "AlgebraicCurve.Place" "ord_add_eq_min"
end Place

theorem D_pow_succ_inv (f : F) (m : ℕ) :
    KaehlerDifferential.D K F ((f ^ (m + 1))⁻¹)
      = (-((m + 1 : ℕ) : F) * (f ^ (m + 2))⁻¹) • KaehlerDifferential.D K F f := by
  rw [← inv_pow f (m + 1), Derivation.leibniz_pow, Derivation.leibniz_inv, Nat.add_sub_cancel,
    smul_smul, ← Nat.cast_smul_eq_nsmul F (m + 1), smul_smul, ← inv_pow f (m + 2)]
  congr 1
  push_cast
  ring

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation adicValuation_ne_zero ord ord_zero ord_one ord_mul ord_inv ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK uniformizer_mem poleSubmodule mem_poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow coe_poleSubmodule_zero laurentTailCoeff laurentTail_remainder_mem_poleSubmodule exists_mem_poleSubmodule"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_add'' [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (ω₁ ω₂ : Ω[F⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique (by
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

p2m_export "AlgebraicCurve.Place" "differentialCoeff_add''"
private theorem _root_.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_inv [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (m : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K F ((v.uniformizer ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (v.uniformizer ^ (m + 2))⁻¹ := by
  rw [D_pow_succ_inv, show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
    v.differentialCoeff_smul, v.differentialCoeff_dCoord, mul_one]

p2m_export "AlgebraicCurve.Place" "differentialCoeff_D_uniformizer_pow_inv"
end Place

namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField adicValuation adicValuation_ne_zero ord ord_zero ord_one ord_mul ord_inv ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_dCoord differentialCoeff_zero differentialCoeff_smul uniformizer ord_uniformizer uniformizer_ne_zero CanonicalLocalResidueDataK uniformizer_mem poleSubmodule mem_poleSubmodule uniformizer_pow_ne_zero ord_uniformizer_pow coe_poleSubmodule_zero laurentTailCoeff laurentTail_remainder_mem_poleSubmodule exists_mem_poleSubmodule"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

namespace CanonicalLocalResidueDataK p2m_export "AlgebraicCurve.Place.CanonicalLocalResidueDataK" "res_higherPoleMonomial res_algebraMap_mul_uniformizer_pow_inv" end CanonicalLocalResidueDataK
p2m_open_scoped "AlgebraicCurve.Place.CanonicalLocalResidueDataK" in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (N : ℕ) {g : F} (hg : g ∈ v.poleSubmodule N) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F g)) = 0 := by
  induction N generalizing g with
  | zero =>

    have hg' : g ∈ v.toValuationSubring := by
      have h := (v.mem_poleSubmodule (n := 0) (f := g)).mp hg
      rwa [pow_zero, one_mul] at h
    exact R.res_of_mem _ (hint g hg')
  | succ N ih =>

    obtain ⟨c, hc⟩ := hsurj (v.laurentTailCoeff (N + 1) ⟨g, hg⟩)
    have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring c)
        = v.laurentTailCoeff (N + 1) ⟨g, hg⟩ := by
      rw [← hc, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hrem : g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ ∈ v.poleSubmodule N := by
      have h := v.laurentTail_remainder_mem_poleSubmodule hg hclift
      rwa [v.coe_algebraMap] at h

    have hpeel : R.res (v.differentialCoeff (KaehlerDifferential.D K F
        (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) = 0 := by
      rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
        v.differentialCoeff_smul, v.differentialCoeff_D_uniformizer_pow_inv,
        show algebraMap K F c * (-((N + 1 : ℕ) : F) * (v.uniformizer ^ (N + 2))⁻¹)
            = algebraMap K F (c * -((N + 1 : ℕ) : K)) * (v.uniformizer ^ ((N + 1) + 1))⁻¹ by
          rw [map_mul, _root_.map_neg, map_natCast]; ring]
      exact R.res_algebraMap_mul_uniformizer_pow_inv v (Nat.le_add_left 1 N) _

    have hsplit : R.res (v.differentialCoeff (KaehlerDifferential.D K F g))
        = R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)))
          + R.res (v.differentialCoeff (KaehlerDifferential.D K F
            (algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹))) := by
      conv_lhs => rw [show g = (g - algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹)
          + algebraMap K F c * (v.uniformizer ^ (N + 1))⁻¹ by ring]
      rw [map_add, v.differentialCoeff_add'', map_add]
    rw [hsplit, ih hrem, hpeel, add_zero]

p2m_open_scoped "AlgebraicCurve.Place.CanonicalLocalResidueDataK" in
theorem CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (g : F) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F g)) = 0 := by
  obtain ⟨N, hN⟩ := v.exists_mem_poleSubmodule g
  exact CanonicalLocalResidueDataK.res_differentialCoeff_D_of_mem_poleSubmodule v hsurj hint
    R N hN

end Place

end AlgebraicCurve

namespace ModularCurve
p2m_open "ModularCurve"

namespace MilneAvAg9bRd13T2CoordIndepChar3

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.AlgebraicCurve"

private theorem _root_.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) (π' : F) {n : ℕ} (hn : 1 ≤ n)
    (hnK : (n : K) ≠ 0) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hmK : ((m + 1 : ℕ) : K) ≠ 0 := by
    rwa [show m + 1 = 1 + m from by omega]

  have hres : R.res (v.differentialCoeff
      (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))) = 0 :=
    Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_of_surj v hsurj hint R _

  have hpow : v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹))
      = -((m + 1 : ℕ) : F) * (((π') ^ (m + 2))⁻¹
          * v.differentialCoeff (KaehlerDifferential.D K F π')) := by
    rw [D_pow_succ_inv, v.differentialCoeff_smul]
    ring

  have hne : -(((m + 1 : ℕ) : F)) ≠ 0 := by
    rw [neg_ne_zero, ← map_natCast (algebraMap K F) (m + 1)]
    exact (map_ne_zero_iff _ (algebraMap K F).injective).mpr hmK

  have hkey : v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (1 + m + 1))⁻¹
      = (-((m + 1 : ℕ) : K))⁻¹
          • v.differentialCoeff (KaehlerDifferential.D K F (((π') ^ (m + 1))⁻¹)) := by
    rw [Algebra.smul_def, map_inv₀, _root_.map_neg, map_natCast, hpow,
      show 1 + m + 1 = m + 2 from by omega, inv_mul_cancel_left₀ hne]
    ring
  rw [hkey, map_smul, hres, smul_zero]

p2m_export "ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3" "ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero"
end MilneAvAg9bRd13T2CoordIndepChar3

namespace MilneAvAg9bRd15UnitNormalFormLaurentSeed

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.AlgebraicCurve"

open scoped Polynomial

private theorem _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {g : F} (hg : g ∈ v.toValuationSubring)
    (h0 : IsLocalRing.residue _ (⟨g, hg⟩ : v.toValuationSubring) = 0) :
    g = 0 ∨ 1 ≤ v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg0
  · exact Or.inl rfl
  right
  have hnn : 0 ≤ v.ord g := v.ord_nonneg_of_mem hg
  rcases eq_or_ne (v.ord g) 0 with hz | hnz
  · exfalso
    have hmemi : g⁻¹ ∈ v.toValuationSubring := by
      refine v.mem_of_ord_nonneg (inv_ne_zero hg0) ?_
      rw [v.ord_inv, hz, _root_.neg_zero]
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hmemi⟩, Subtype.ext (mul_inv_cancel₀ hg0),
      Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩
  · omega

p2m_export "ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed" "ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero"
private theorem _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_unit_normal_form_of_surj
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {w : F} (hw0 : w ≠ 0) (hw : v.ord w = 0) :
    ∃ (c : K) (s : F), c ≠ 0 ∧ (s = 0 ∨ 1 ≤ v.ord s) ∧
      w = algebraMap K F c * (1 + s) := by
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hw.ge
  have hwinv : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hw, _root_.neg_zero]
  have hres0 : IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring) ≠ 0 := by
    intro h0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h0
    exact h0 ⟨⟨⟨w, hwmem⟩, ⟨w⁻¹, hwinv⟩, Subtype.ext (mul_inv_cancel₀ hw0),
      Subtype.ext (inv_mul_cancel₀ hw0)⟩, rfl⟩
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero] at hc
    exact hres0 hc.symm
  have ha0 : algebraMap K F c ≠ 0 :=
    fun h => hc0 ((algebraMap K F).injective (h.trans (_root_.map_zero _).symm))
  refine ⟨c, w * (algebraMap K F c)⁻¹ - 1, hc0, ?_, ?_⟩
  · have hainv : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
      rw [← map_inv₀]
      exact v.algebraMap_mem' c⁻¹
    have hsmem : w * (algebraMap K F c)⁻¹ - 1 ∈ v.toValuationSubring :=
      sub_mem (mul_mem hwmem hainv) (one_mem _)
    refine ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero v hsmem ?_
    have hfact : (⟨w * (algebraMap K F c)⁻¹ - 1, hsmem⟩ : v.toValuationSubring)
        = ⟨w, hwmem⟩ * ⟨(algebraMap K F c)⁻¹, hainv⟩ - 1 :=
      Subtype.ext (by push_cast; ring)
    have hainv_res : IsLocalRing.residue _
        ((⟨(algebraMap K F c)⁻¹, hainv⟩ : v.toValuationSubring))
        = (IsLocalRing.residue _ (⟨w, hwmem⟩ : v.toValuationSubring))⁻¹ := by
      have h1 : (⟨(algebraMap K F c)⁻¹, hainv⟩ : v.toValuationSubring)
          = algebraMap K v.toValuationSubring c⁻¹ :=
        Subtype.ext (by rw [v.coe_algebraMap, map_inv₀])
      rw [h1, ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        map_inv₀, hc, IsLocalRing.ResidueField.algebraMap_eq]
    rw [hfact, map_sub, map_mul, map_one, hainv_res, mul_inv_cancel₀ hres0, sub_self]
  · have hrw : (1 : F) + (w * (algebraMap K F c)⁻¹ - 1) = w * (algebraMap K F c)⁻¹ := by
      ring
    rw [hrw, mul_comm w (algebraMap K F c)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ ha0, one_mul]

p2m_export "ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed" "ag9b15u_exists_unit_normal_form_of_surj"
private theorem _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_K_truncation_of_mem_poleSubmodule
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (n : ℕ) {f : F} (hf : f ∈ v.poleSubmodule n) :
    ∃ c : ℕ → K,
      f - ∑ j ∈ Finset.range n, algebraMap K F (c j) * (v.uniformizer ^ (j + 1))⁻¹
        ∈ v.toValuationSubring := by
  induction n generalizing f with
  | zero =>
    refine ⟨0, ?_⟩
    rw [Finset.range_zero, Finset.sum_empty, sub_zero]
    rwa [← SetLike.mem_coe, v.coe_poleSubmodule_zero] at hf
  | succ n ih =>
    obtain ⟨ctop, hctop⟩ := hsurj (v.laurentTailCoeff (n + 1) ⟨f, hf⟩)
    have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring ctop)
        = v.laurentTailCoeff (n + 1) ⟨f, hf⟩ := by
      rw [← hctop, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    have hrem : f - algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹
        ∈ v.poleSubmodule n := by
      have h := v.laurentTail_remainder_mem_poleSubmodule hf hclift
      rwa [v.coe_algebraMap] at h
    obtain ⟨c', hc'⟩ := ih hrem
    refine ⟨fun j => if j = n then ctop else c' j, ?_⟩
    have hstep : ∑ j ∈ Finset.range (n + 1),
        algebraMap K F (if j = n then ctop else c' j) * (v.uniformizer ^ (j + 1))⁻¹
        = (∑ j ∈ Finset.range n, algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹)
          + algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹ := by
      rw [Finset.sum_range_succ, if_pos rfl]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_neg (Finset.mem_range.mp hj).ne]
    rw [hstep, show f - ((∑ j ∈ Finset.range n,
          algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹)
          + algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹)
        = f - algebraMap K F ctop * (v.uniformizer ^ (n + 1))⁻¹
          - ∑ j ∈ Finset.range n,
              algebraMap K F (c' j) * (v.uniformizer ^ (j + 1))⁻¹ from by ring]
    exact hc'

p2m_export "ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed" "ag9b15u_exists_K_truncation_of_mem_poleSubmodule"
private theorem _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_differentialCoeff_D_unit_mul_uniformizer
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] (w : F) :
    v.differentialCoeff (KaehlerDifferential.D K F (w * v.uniformizer))
      = w + v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w) := by
  refine v.differentialCoeff_unique ?_
  calc KaehlerDifferential.D K F (w * v.uniformizer)
      = w • KaehlerDifferential.D K F v.uniformizer
        + v.uniformizer • KaehlerDifferential.D K F w := by
        rw [Derivation.leibniz]
    _ = w • v.dCoord + v.uniformizer •
          (v.differentialCoeff (KaehlerDifferential.D K F w) • v.dCoord) := by
        rw [show KaehlerDifferential.D K F v.uniformizer = v.dCoord from rfl,
          v.differentialCoeff_smul_dCoord]
    _ = (w + v.uniformizer * v.differentialCoeff (KaehlerDifferential.D K F w))
          • v.dCoord := by
        rw [smul_smul, add_smul]

p2m_export "ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed" "ag9b15u_differentialCoeff_D_unit_mul_uniformizer"
end MilneAvAg9bRd15UnitNormalFormLaurentSeed

namespace MilneAvAg9bRd14CubeRowCartierSliceStart

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.AlgebraicCurve"

private theorem _root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (R : v.CanonicalLocalResidueDataK)
    {j : ℤ} (hj : j ≠ -1) :
    R.res (v.uniformizer ^ j) = 0 := by
  by_cases h0 : 0 ≤ j
  · refine R.res_of_mem _ (v.mem_of_ord_nonneg (zpow_ne_zero j v.uniformizer_ne_zero) ?_)
    rw [v.ord_zpow, v.ord_uniformizer, mul_one]
    exact h0
  · have hn1 : 1 ≤ (-j - 1).toNat := by omega
    have hjn : j = -(((-j - 1).toNat + 1 : ℕ) : ℤ) := by omega
    rw [hjn, _root_.zpow_neg, zpow_natCast]
    exact R.res_higherPoleMonomial _ hn1

p2m_export "ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart" "ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one"
end MilneAvAg9bRd14CubeRowCartierSliceStart

end ModularCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.CanonicalLocalResidueDataK Place.poleSubmodule"
p2m_open "AlgebraicCurve"

theorem gate_canonicalLocalResidueDataK_uniformizer_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (R : v.CanonicalLocalResidueDataK) : R.res v.uniformizer⁻¹ = 1 := by
  have hmem : v.uniformizer * v.uniformizer⁻¹ ∈ v.toValuationSubring := by
    rw [mul_inv_cancel₀ v.uniformizer_ne_zero]; exact one_mem _
  rw [R.res_simplePole _ hmem]
  have h1 : (⟨v.uniformizer * v.uniformizer⁻¹, hmem⟩ : v.toValuationSubring) = 1 :=
    Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
  rw [h1, map_one]

section CharFreeToolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem p0n22_cpf_uniformizer_pow_mul_mem_cases
    (v : Place K F)
    {σ : F} (hσ : σ ∈ v.toValuationSubring) {k : ℕ} (hk : 1 ≤ k) :
    v.uniformizer ^ k * σ = 0 ∨ 1 ≤ v.ord (v.uniformizer ^ k * σ) := by
  rcases eq_or_ne σ 0 with rfl | hσ0
  · exact Or.inl (mul_zero _)
  · right
    rw [v.ord_mul (v.uniformizer_pow_ne_zero k) hσ0, v.ord_uniformizer_pow]
    have := v.ord_nonneg_of_mem hσ
    omega

theorem p0n22_cpf_one_add_ne_zero
    (v : Place K F)
    {g : F} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    (1 : F) + g ≠ 0 := by
  rcases hg with rfl | hord
  · simp
  · intro h
    rw [eq_neg_of_add_eq_zero_right h] at hord
    have hneg : v.ord (-1 : F) = 0 := by
      have h2 : v.ord ((-1 : F) * (-1)) = v.ord (-1 : F)
          + v.ord (-1 : F) :=
        v.ord_mul (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
      rw [neg_mul_neg, one_mul, v.ord_one] at h2
      omega
    omega

theorem p0n22_cpf_ord_one_add_eq_zero
    (v : Place K F)
    {g : F} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    v.ord ((1 : F) + g) = 0 := by
  rcases hg with rfl | hord
  · rw [add_zero, v.ord_one]
  · have hg0 : g ≠ 0 := by
      intro h
      rw [h, v.ord_zero] at hord
      omega
    have h1 := v.ord_add_eq_min (f := (1 : F)) (g := g) one_ne_zero hg0
      (by rw [v.ord_one]; omega)
    rw [v.ord_one] at h1
    omega

theorem p0n22_cpf_one_add_inv_mem
    (v : Place K F)
    {g : F} (hg : g = 0 ∨ 1 ≤ v.ord g) :
    ((1 : F) + g)⁻¹ ∈ v.toValuationSubring := by
  refine v.mem_of_ord_nonneg (inv_ne_zero (p0n22_cpf_one_add_ne_zero v hg)) ?_
  rw [v.ord_inv, p0n22_cpf_ord_one_add_eq_zero v hg, _root_.neg_zero]

theorem p0n22_cpf_logDeriv_mul
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    {w₁ w₂ : F} (h1 : w₁ ≠ 0) (h2 : w₂ ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K F (w₁ * w₂))
        * (w₁ * w₂)⁻¹
      = v.differentialCoeff (KaehlerDifferential.D K F w₁) * w₁⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K F w₂)
            * w₂⁻¹ := by
  rw [Derivation.leibniz, v.differentialCoeff_add'', v.differentialCoeff_smul,
    v.differentialCoeff_smul]
  have hc1 : w₁ * w₁⁻¹ = 1 := mul_inv_cancel₀ h1
  have hc2 : w₂ * w₂⁻¹ = 1 := mul_inv_cancel₀ h2
  linear_combination
    (v.differentialCoeff (KaehlerDifferential.D K F w₂) * w₂⁻¹)
      * hc1
    + (v.differentialCoeff (KaehlerDifferential.D K F w₁) * w₁⁻¹)
      * hc2

theorem p0n22_cpf_logDeriv_mem
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    {w : F} (hw0 : w ≠ 0) (hword : v.ord w = 0) :
    v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹
      ∈ v.toValuationSubring := by
  have hwmem : w ∈ v.toValuationSubring := v.mem_of_ord_nonneg hw0 hword.ge
  have hwinv : w⁻¹ ∈ v.toValuationSubring := by
    refine v.mem_of_ord_nonneg (inv_ne_zero hw0) ?_
    rw [v.ord_inv, hword, _root_.neg_zero]
  exact mul_mem (hint _ hwmem) hwinv

theorem p0n22_cpf_differentialCoeff_D_one_add_algebraMap_mul_pow
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] (a : K) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K F
        ((1 : F)
          + algebraMap K F a * v.uniformizer ^ k))
      = algebraMap K F a
        * (((k : ℕ) : F) * v.uniformizer ^ (k - 1)) := by
  refine v.differentialCoeff_unique ?_
  rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Derivation.map_algebraMap, smul_zero, add_zero, Derivation.leibniz_pow,
    show KaehlerDifferential.D K F v.uniformizer = v.dCoord from
      rfl,
    ← Nat.cast_smul_eq_nsmul F k, smul_smul, smul_smul, mul_assoc]

theorem p0n22_cpf_differentialCoeff_D_one_add_pow_mul
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] (σ : F) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K F
        ((1 : F) + v.uniformizer ^ k * σ))
      = v.uniformizer ^ k
          * v.differentialCoeff (KaehlerDifferential.D K F σ)
        + σ * (((k : ℕ) : F) * v.uniformizer ^ (k - 1)) := by
  refine v.differentialCoeff_unique ?_
  conv_lhs => rw [map_add, Derivation.map_one_eq_zero, zero_add, Derivation.leibniz,
    Derivation.leibniz_pow,
    show KaehlerDifferential.D K F v.uniformizer = v.dCoord from
      rfl,
    ← Nat.cast_smul_eq_nsmul F k,
    ← v.differentialCoeff_smul_dCoord
      (KaehlerDifferential.D K F σ),
    smul_smul, smul_smul, smul_smul, ← add_smul]
  exact congrArg (· • v.dCoord) (by ring)

theorem p0n22_cpf_exists_residue_lift_decomp
    (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {r : F} (hr : r ∈ v.toValuationSubring) :
    ∃ (d : K) (r' : F), r' ∈ v.toValuationSubring ∧
      r = algebraMap K F d + v.uniformizer * r' := by
  obtain ⟨d, hd⟩ := hsurj (IsLocalRing.residue _ (⟨r, hr⟩ : v.toValuationSubring))
  have hxmem : r - algebraMap K F d ∈ v.toValuationSubring :=
    sub_mem hr (v.algebraMap_mem' d)
  have hres0 : IsLocalRing.residue _
      (⟨r - algebraMap K F d, hxmem⟩ : v.toValuationSubring)
      = 0 := by
    have hfact : (⟨r - algebraMap K F d, hxmem⟩
        : v.toValuationSubring)
        = ⟨r, hr⟩ - algebraMap K v.toValuationSubring d :=
      Subtype.ext (by push_cast [v.coe_algebraMap]; ring)
    have h2 : IsLocalRing.residue _ (algebraMap K v.toValuationSubring d)
        = IsLocalRing.residue _ (⟨r, hr⟩ : v.toValuationSubring) := by
      rw [← hd, IsScalarTower.algebraMap_apply K v.toValuationSubring
        v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq]
    rw [hfact, map_sub, h2, sub_self]
  rcases _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero
      v hxmem hres0 with hx0 | hxord
  · exact ⟨d, 0, zero_mem _, by rw [mul_zero, add_zero]; exact (sub_eq_zero.mp hx0)⟩
  · have hxne : r - algebraMap K F d ≠ 0 := by
      intro h0
      rw [h0, v.ord_zero] at hxord
      omega
    refine ⟨d, v.uniformizer⁻¹ * (r - algebraMap K F d), ?_, ?_⟩
    · refine v.mem_of_ord_nonneg
        (mul_ne_zero (inv_ne_zero v.uniformizer_ne_zero) hxne) ?_
      rw [v.ord_mul (inv_ne_zero v.uniformizer_ne_zero) hxne, v.ord_inv,
        v.ord_uniformizer]
      omega
    · rw [← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
      ring

theorem p0n22_cpf_exists_elementary_peel
    (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    {k : ℕ} (hk : 1 ≤ k) {σ : F} (hσ : σ ∈ v.toValuationSubring) :
    ∃ (a : K) (τ : F), τ ∈ v.toValuationSubring ∧
      (1 : F) + v.uniformizer ^ k * σ
        = ((1 : F)
              + algebraMap K F a * v.uniformizer ^ k)
          * ((1 : F) + v.uniformizer ^ (k + 1) * τ) := by
  obtain ⟨a, σ', hσ', hdec⟩ := p0n22_cpf_exists_residue_lift_decomp v hsurj hσ
  have hgcase : algebraMap K F a * v.uniformizer ^ k = 0
      ∨ 1 ≤ v.ord (algebraMap K F a * v.uniformizer ^ k) := by
    rw [mul_comm]
    exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
  have he0 : (1 : F)
      + algebraMap K F a * v.uniformizer ^ k ≠ 0 :=
    p0n22_cpf_one_add_ne_zero v hgcase
  have heinv : ((1 : F)
      + algebraMap K F a * v.uniformizer ^ k)⁻¹
      ∈ v.toValuationSubring :=
    p0n22_cpf_one_add_inv_mem v hgcase
  refine ⟨a, σ' * ((1 : F)
    + algebraMap K F a * v.uniformizer ^ k)⁻¹,
    mul_mem hσ' heinv, ?_⟩
  have hce : ((1 : F)
      + algebraMap K F a * v.uniformizer ^ k)
      * ((1 : F)
          + algebraMap K F a * v.uniformizer ^ k)⁻¹ = 1 :=
    mul_inv_cancel₀ he0
  rw [hdec]
  linear_combination (-(v.uniformizer ^ (k + 1) * σ')) * hce

theorem p0n22_cpf_exists_laurent_expansion_one
    (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (f : F) :
    ∃ (s : Finset ℤ) (c : ℤ → K) (r : F),
      r ∈ v.toValuationSubring ∧
      f = (∑ j ∈ s, c j • v.uniformizer ^ j) + v.uniformizer * r := by
  obtain ⟨N, hN⟩ := v.exists_mem_poleSubmodule f
  obtain ⟨c0, hc0⟩ :=
    _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_K_truncation_of_mem_poleSubmodule
      v hsurj N hN
  obtain ⟨d, r, hr, hdec⟩ := p0n22_cpf_exists_residue_lift_decomp v hsurj hc0
  refine ⟨insert (0 : ℤ) ((Finset.range N).image fun j : ℕ => -((j : ℤ) + 1)),
    fun t => if t = 0 then d else c0 (-(t + 1)).toNat, r, hr, ?_⟩
  have h0not : (0 : ℤ) ∉ (Finset.range N).image (fun j : ℕ => -((j : ℤ) + 1)) := by
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨j, _, hj⟩
    omega
  have hinj : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N,
      -((x : ℤ) + 1) = -((y : ℤ) + 1) → x = y := fun x _ y _ h => by omega
  have himg : ∀ j ∈ Finset.range N,
      (if -((j : ℤ) + 1) = 0 then d else c0 (-(-((j : ℤ) + 1) + 1)).toNat)
          • v.uniformizer ^ (-((j : ℤ) + 1))
        = algebraMap K F (c0 j)
            * (v.uniformizer ^ (j + 1))⁻¹ := by
    intro j _
    rw [if_neg (by omega : ¬(-((j : ℤ) + 1) = (0 : ℤ))),
      show (-(-((j : ℤ) + 1) + 1)).toNat = j from by omega,
      Algebra.smul_def, _root_.zpow_neg,
      show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
  rw [Finset.sum_insert h0not, Finset.sum_image hinj, Finset.sum_congr rfl himg,
    show ((fun t : ℤ => if t = 0 then d else c0 (-(t + 1)).toNat) 0) = d from by simp,
    zpow_zero, Algebra.smul_def, mul_one]
  linear_combination hdec

theorem p0n22_cpf_res_geom_core
    (v : Place K F) (R : v.CanonicalLocalResidueDataK)
    (a : K) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) :
    R.res (algebraMap K F a * v.uniformizer ^ (k - 1)
        * ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹)
      = if k ∣ q
        then algebraMap K v.ResidueField (a * (-a) ^ (q / k - 1))
        else 0 := by
  have hπ0 : (v.uniformizer : F) ≠ 0 := v.uniformizer_ne_zero
  have hgcase : algebraMap K F a * v.uniformizer ^ k = 0
      ∨ 1 ≤ v.ord (algebraMap K F a * v.uniformizer ^ k) := by
    rw [mul_comm]
    exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
  have hu0 : (1 : F)
      + algebraMap K F a * v.uniformizer ^ k ≠ 0 :=
    p0n22_cpf_one_add_ne_zero v hgcase
  have huinv : ((1 : F)
      + algebraMap K F a * v.uniformizer ^ k)⁻¹
      ∈ v.toValuationSubring :=
    p0n22_cpf_one_add_inv_mem v hgcase
  have hgeom : ((1 : F)
      + algebraMap K F a * v.uniformizer ^ k)⁻¹
      = (∑ t ∈ Finset.range q,
          (-(algebraMap K F a * v.uniformizer ^ k)) ^ t)
        + (-(algebraMap K F a * v.uniformizer ^ k)) ^ q
          * ((1 : F)
              + algebraMap K F a * v.uniformizer ^ k)⁻¹ := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
    have hgs := geom_sum_mul
      (-(algebraMap K F a * v.uniformizer ^ k)) q
    linear_combination -hgs
  rw [hgeom, mul_add, add_mul, map_add]
  have htail : R.res ((algebraMap K F a * v.uniformizer ^ (k - 1)
      * ((-(algebraMap K F a * v.uniformizer ^ k)) ^ q
          * ((1 : F)
              + algebraMap K F a * v.uniformizer ^ k)⁻¹))
      * (v.uniformizer ^ q)⁻¹) = 0 := by
    apply R.res_of_mem
    have hqle : q ≤ k * q := Nat.le_of_dvd (Nat.mul_pos hk hq) (dvd_mul_left q k)
    have hpowsplit : (v.uniformizer : F) ^ (k * q)
        = v.uniformizer ^ (k * q - q) * v.uniformizer ^ q := by
      rw [← pow_add, Nat.sub_add_cancel hqle]
    have hxq : (-(algebraMap K F a * v.uniformizer ^ k)) ^ q
        = algebraMap K F ((-a) ^ q)
          * (v.uniformizer ^ (k * q - q) * v.uniformizer ^ q) := by
      rw [map_pow, _root_.map_neg,
        show -(algebraMap K F a * v.uniformizer ^ k)
            = -algebraMap K F a * v.uniformizer ^ k from
          (neg_mul _ _).symm,
        mul_pow, ← pow_mul, hpowsplit]
    have hcc : (v.uniformizer : F) ^ q
        * ((v.uniformizer : F) ^ q)⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hπ0)
    have heq : (algebraMap K F a * v.uniformizer ^ (k - 1)
        * ((-(algebraMap K F a * v.uniformizer ^ k)) ^ q
            * ((1 : F)
                + algebraMap K F a * v.uniformizer ^ k)⁻¹))
        * (v.uniformizer ^ q)⁻¹
        = algebraMap K F a * v.uniformizer ^ (k - 1)
          * (algebraMap K F ((-a) ^ q)
              * v.uniformizer ^ (k * q - q)
              * ((1 : F)
                  + algebraMap K F a * v.uniformizer ^ k)⁻¹) := by
      rw [hxq]
      linear_combination (algebraMap K F a
        * v.uniformizer ^ (k - 1)
        * (algebraMap K F ((-a) ^ q)
            * v.uniformizer ^ (k * q - q)
            * ((1 : F)
                + algebraMap K F a * v.uniformizer ^ k)⁻¹)) * hcc
    rw [heq]
    exact mul_mem (mul_mem (v.algebraMap_mem' a) (pow_mem v.uniformizer_mem _))
      (mul_mem (mul_mem (v.algebraMap_mem' _) (pow_mem v.uniformizer_mem _)) huinv)
  have hterm : (algebraMap K F a * v.uniformizer ^ (k - 1)
      * (∑ t ∈ Finset.range q,
          (-(algebraMap K F a * v.uniformizer ^ k)) ^ t))
      * (v.uniformizer ^ q)⁻¹
      = ∑ t ∈ Finset.range q, (a * (-a) ^ t)
          • v.uniformizer ^ ((k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hxt : (-(algebraMap K F a * v.uniformizer ^ k)) ^ t
        = algebraMap K F ((-a) ^ t)
          * v.uniformizer ^ (k * t) := by
      rw [map_pow, _root_.map_neg,
        show -(algebraMap K F a * v.uniformizer ^ k)
            = -algebraMap K F a * v.uniformizer ^ k from
          (neg_mul _ _).symm,
        mul_pow, ← pow_mul]
    rw [hxt, Algebra.smul_def, map_mul, map_pow, _root_.map_neg,
      show (k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ)
          = ((k - 1 : ℕ) : ℤ) + ((k * t : ℕ) : ℤ) + -((q : ℕ) : ℤ) from by
        push_cast [Nat.cast_sub hk]
        ring,
      zpow_add₀ hπ0, zpow_add₀ hπ0, zpow_natCast, zpow_natCast, _root_.zpow_neg, zpow_natCast]
    ring
  rw [hterm, map_sum]
  simp only [map_smul]
  by_cases hdvd : k ∣ q
  · rw [if_pos hdvd, htail, add_zero]
    obtain ⟨e, rfl⟩ := hdvd
    rcases Nat.eq_zero_or_pos e with rfl | he1
    · simp at hq
    · rw [Nat.mul_div_cancel_left e hk]
      have he_lt : e - 1 < k * e := by
        have h1 : e ≤ k * e := Nat.le_of_dvd (Nat.mul_pos hk he1) (dvd_mul_left e k)
        omega
      have hother : ∀ t ∈ Finset.range (k * e), t ≠ e - 1 →
          (a * (-a) ^ t) • R.res ((v.uniformizer : F)
            ^ ((k : ℤ) * ((t : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ))) = 0 := by
        intro t _ htne
        have hne : (k : ℤ) * ((t : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ) ≠ -1 := by
          intro hcontra
          have h2 : (k : ℤ) * ((t : ℤ) + 1) = (k : ℤ) * (e : ℤ) := by
            push_cast at hcontra
            linarith
          have hk0 : (k : ℤ) ≠ 0 := by omega
          have h3 : (t : ℤ) + 1 = (e : ℤ) := mul_left_cancel₀ hk0 h2
          omega
        rw [_root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R hne, smul_zero]
      rw [Finset.sum_eq_single_of_mem (e - 1) (Finset.mem_range.mpr he_lt) hother,
        show (k : ℤ) * (((e - 1 : ℕ) : ℤ) + 1) - 1 - ((k * e : ℕ) : ℤ) = -1 from by
          push_cast [Nat.cast_sub he1]
          ring,
        _root_.zpow_neg, zpow_one, gate_canonicalLocalResidueDataK_uniformizer_inv v R,
        ← Algebra.algebraMap_eq_smul_one]
  · rw [if_neg hdvd, htail, add_zero]
    refine Finset.sum_eq_zero fun t _ => ?_
    have hne : (k : ℤ) * ((t : ℤ) + 1) - 1 - (q : ℤ) ≠ -1 := by
      intro hcontra
      have h2 : (k : ℤ) * ((t : ℤ) + 1) = (q : ℤ) := by linarith
      have h3 : k * (t + 1) = q := by exact_mod_cast h2
      exact hdvd ⟨t + 1, h3.symm⟩
    rw [_root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
      v R hne, smul_zero]

theorem p0n22_cpf_res_logDeriv_elementary
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (R : v.CanonicalLocalResidueDataK) (a : K) {k q : ℕ} (hk : 1 ≤ k) (hq : 1 ≤ q) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F
          ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k))
        * ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹)
      = ((k : ℕ) : K) • (if k ∣ q
          then algebraMap K v.ResidueField (a * (-a) ^ (q / k - 1))
          else 0) := by
  rw [p0n22_cpf_differentialCoeff_D_one_add_algebraMap_mul_pow v a k]
  have hsplit : algebraMap K F a
        * (((k : ℕ) : F) * v.uniformizer ^ (k - 1))
        * ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ q)⁻¹
      = ((k : ℕ) : K) • (algebraMap K F a
          * v.uniformizer ^ (k - 1)
          * ((1 : F)
              + algebraMap K F a * v.uniformizer ^ k)⁻¹
          * (v.uniformizer ^ q)⁻¹) := by
    rw [Algebra.smul_def, map_natCast]
    ring
  rw [hsplit, map_smul, p0n22_cpf_res_geom_core v R a hk hq]

theorem p0n22_cpf_res_logDeriv_highLevel_vanish
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK)
    {σ : F} (hσ : σ ∈ v.toValuationSubring)
    {k q : ℕ} (hbig : q + 1 ≤ k) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F
          ((1 : F) + v.uniformizer ^ k * σ))
        * ((1 : F) + v.uniformizer ^ k * σ)⁻¹
        * (v.uniformizer ^ q)⁻¹) = 0 := by
  have hπ0 : (v.uniformizer : F) ≠ 0 := v.uniformizer_ne_zero
  have hgcase := p0n22_cpf_uniformizer_pow_mul_mem_cases v hσ
    (show 1 ≤ k by omega)
  have huinv := p0n22_cpf_one_add_inv_mem v hgcase
  have hσ' : v.differentialCoeff (KaehlerDifferential.D K F σ)
      ∈ v.toValuationSubring :=
    hint _ hσ
  have hkF : ((k : ℕ) : F) ∈ v.toValuationSubring := by
    rw [← map_natCast (algebraMap K F)]
    exact v.algebraMap_mem' _
  obtain ⟨e, rfl⟩ : ∃ e, k = q + 1 + e := ⟨k - (q + 1), by omega⟩
  apply R.res_of_mem
  rw [p0n22_cpf_differentialCoeff_D_one_add_pow_mul v σ (q + 1 + e)]
  have hcc : (v.uniformizer : F) ^ q
      * ((v.uniformizer : F) ^ q)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hπ0)
  have heq : (v.uniformizer ^ (q + 1 + e)
        * v.differentialCoeff (KaehlerDifferential.D K F σ)
        + σ * (((q + 1 + e : ℕ) : F) * v.uniformizer ^ (q + 1 + e - 1)))
        * ((1 : F) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹
        * (v.uniformizer ^ q)⁻¹
      = (v.uniformizer ^ (1 + e)
          * v.differentialCoeff (KaehlerDifferential.D K F σ)
          + σ * (((q + 1 + e : ℕ) : F) * v.uniformizer ^ e))
        * ((1 : F) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹ := by
    rw [show q + 1 + e - 1 = q + e from by omega]
    linear_combination ((v.uniformizer ^ (1 + e)
        * v.differentialCoeff (KaehlerDifferential.D K F σ)
        + σ * (((q + 1 + e : ℕ) : F) * v.uniformizer ^ e))
      * ((1 : F) + v.uniformizer ^ (q + 1 + e) * σ)⁻¹) * hcc
  rw [heq]
  exact mul_mem (add_mem (mul_mem (pow_mem v.uniformizer_mem _) hσ')
    (mul_mem hσ (mul_mem hkF (pow_mem v.uniformizer_mem _)))) huinv

theorem p0n22_cpf_row_integrand_eq_pow_mul_dlog
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    {w : F} (hw0 : w ≠ 0) (k : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K F
        (w * v.uniformizer))
        * ((w * v.uniformizer) ^ (k + 1))⁻¹
      = (w ^ k * v.uniformizer ^ k)⁻¹
        * ((v.uniformizer)⁻¹
            + v.differentialCoeff (KaehlerDifferential.D K F w)
                * w⁻¹) := by
  rw [_root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_differentialCoeff_D_unit_mul_uniformizer
    v w]
  have hπ0 : (v.uniformizer : F) ≠ 0 := v.uniformizer_ne_zero
  have hcw : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hcπ : (v.uniformizer : F) * (v.uniformizer)⁻¹ = 1 :=
    mul_inv_cancel₀ hπ0
  linear_combination ((w ^ k)⁻¹ * (v.uniformizer ^ (k + 1))⁻¹) * hcw
    + (v.differentialCoeff (KaehlerDifferential.D K F w)
        * (w ^ (k + 1))⁻¹ * (v.uniformizer ^ k)⁻¹) * hcπ

end CharFreeToolkit

section CharPCartier

variable {p : ℕ} [hp : Fact p.Prime]
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [hKp : CharP K p]

theorem p0n22_cpf_res_logDeriv_elementary_cartier
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (R : v.CanonicalLocalResidueDataK) (a : K) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F
          ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k))
        * ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ (p * n))⁻¹)
      = (R.res (v.differentialCoeff (KaehlerDifferential.D K F
          ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k))
        * ((1 : F)
            + algebraMap K F a * v.uniformizer ^ k)⁻¹
        * (v.uniformizer ^ n)⁻¹)) ^ p := by
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  rw [p0n22_cpf_res_logDeriv_elementary v R a hk (Nat.mul_pos hp.out.pos hn),
    p0n22_cpf_res_logDeriv_elementary v R a hk hn]
  by_cases hdn : k ∣ n
  · rw [if_pos (hdn.mul_left p), if_pos hdn]
    obtain ⟨e, rfl⟩ := hdn
    rcases Nat.eq_zero_or_pos e with rfl | he1
    · simp at hn
    · rw [show p * (k * e) / k = p * e from by
          rw [show p * (k * e) = k * (p * e) from by ring, Nat.mul_div_cancel_left _ hk],
        Nat.mul_div_cancel_left e hk]
      have key : ∀ m : ℕ, 1 ≤ m → a * (-a) ^ (m - 1) = -((-a) ^ m) := by
        intro m hm
        obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
        rw [show 1 + m' - 1 = m' from by omega, show 1 + m' = m' + 1 from by omega,
          pow_succ]
        ring
      have hneg : (-((-a) ^ e) : K) ^ p = -(((-a) ^ e) ^ p) := by
        rw [neg_eq_neg_one_mul, mul_pow, neg_one_pow_char K p, neg_one_mul]
      have hxp : (a * (-a) ^ (e - 1)) ^ p = a * (-a) ^ (p * e - 1) := by
        rw [key e he1, key (p * e) (Nat.mul_pos hp.out.pos he1), hneg, ← pow_mul,
          mul_comm e p]
      have hfix : ((k : ℕ) : v.ResidueField) ^ p = ((k : ℕ) : v.ResidueField) := by
        have h := map_natCast (frobenius v.ResidueField p) k
        rwa [frobenius_def] at h
      rw [Algebra.smul_def, Algebra.smul_def, map_natCast (algebraMap K v.ResidueField) k,
        mul_pow, hfix, ← map_pow, hxp]
  · by_cases hdp : k ∣ p * n
    · have hpk : p ∣ k := by
        by_contra hpk
        exact hdn ((((hp.out.coprime_iff_not_dvd).mpr hpk).symm).dvd_mul_left.mp hdp)
      have hk0 : ((k : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K p k).mpr hpk
      rw [hk0, zero_smul, zero_smul, zero_pow hp.out.ne_zero]
    · rw [if_neg hdp, if_neg hdn, smul_zero, zero_pow hp.out.ne_zero]

theorem p0n22_cpf_res_logDeriv_principalUnit_cartier_aux
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    ∀ d k : ℕ, 1 ≤ k → p * n + 1 ≤ k + d →
      ∀ σ : F, σ ∈ v.toValuationSubring →
        R.res (v.differentialCoeff (KaehlerDifferential.D K F
              ((1 : F) + v.uniformizer ^ k * σ))
            * ((1 : F) + v.uniformizer ^ k * σ)⁻¹
            * (v.uniformizer ^ (p * n))⁻¹)
          = (R.res (v.differentialCoeff (KaehlerDifferential.D K F
              ((1 : F) + v.uniformizer ^ k * σ))
            * ((1 : F) + v.uniformizer ^ k * σ)⁻¹
            * (v.uniformizer ^ n)⁻¹)) ^ p := by
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  intro d
  induction d with
  | zero =>
    intro k hk hbound σ hσ
    have hnp : n ≤ p * n := Nat.le_mul_of_pos_left n hp.out.pos
    rw [p0n22_cpf_res_logDeriv_highLevel_vanish v hint R hσ (show p * n + 1 ≤ k by omega),
      p0n22_cpf_res_logDeriv_highLevel_vanish v hint R hσ (show n + 1 ≤ k by omega),
      zero_pow hp.out.ne_zero]
  | succ d ihd =>
    intro k hk hbound σ hσ
    obtain ⟨a, τ, hτ, hfac⟩ := p0n22_cpf_exists_elementary_peel v hsurj hk hσ
    have hgcase1 : algebraMap K F a * v.uniformizer ^ k = 0
        ∨ 1 ≤ v.ord (algebraMap K F a * v.uniformizer ^ k) := by
      rw [mul_comm]
      exact p0n22_cpf_uniformizer_pow_mul_mem_cases v (v.algebraMap_mem' a) hk
    have h1 : (1 : F)
        + algebraMap K F a * v.uniformizer ^ k ≠ 0 :=
      p0n22_cpf_one_add_ne_zero v hgcase1
    have hgcase2 := p0n22_cpf_uniformizer_pow_mul_mem_cases v hτ
      (show 1 ≤ k + 1 by omega)
    have h2 : (1 : F) + v.uniformizer ^ (k + 1) * τ ≠ 0 :=
      p0n22_cpf_one_add_ne_zero v hgcase2
    rw [hfac, p0n22_cpf_logDeriv_mul v h1 h2, add_mul, add_mul, LinearMap.map_add,
      LinearMap.map_add, p0n22_cpf_res_logDeriv_elementary_cartier v R a hk hn,
      ihd (k + 1) (by omega) (by omega) τ hτ, ← add_pow_char]

theorem p0n22_cpf_res_zpow_mul_logDeriv_cartier
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : F} (hw0 : w ≠ 0) (hword : v.ord w = 0) (j : ℤ) :
    R.res (v.uniformizer ^ ((p : ℤ) * j)
        * (v.differentialCoeff (KaehlerDifferential.D K F w)
            * w⁻¹))
      = (R.res (v.uniformizer ^ j
        * (v.differentialCoeff (KaehlerDifferential.D K F w)
            * w⁻¹))) ^ p := by
  have hπ0 : (v.uniformizer : F) ≠ 0 := v.uniformizer_ne_zero
  have hL := p0n22_cpf_logDeriv_mem v hint hw0 hword
  rcases le_or_gt 0 j with hj | hj
  · have hmem : ∀ i : ℤ, 0 ≤ i → v.uniformizer ^ i
        * (v.differentialCoeff (KaehlerDifferential.D K F w)
            * w⁻¹) ∈ v.toValuationSubring := by
      intro i hi
      refine mul_mem ?_ hL
      refine v.mem_of_ord_nonneg (zpow_ne_zero i hπ0) ?_
      rw [v.ord_zpow, v.ord_uniformizer, mul_one]
      exact hi
    rw [R.res_of_mem _ (hmem _ (mul_nonneg (Int.natCast_nonneg p) hj)),
      R.res_of_mem _ (hmem _ hj), zero_pow hp.out.ne_zero]
  · obtain ⟨c, s, hc0, hs, hwfac⟩ :=
      _root_.ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_exists_unit_normal_form_of_surj
        v hsurj hw0 hword
    have hcF : algebraMap K F c ≠ 0 := fun h =>
      hc0 ((algebraMap K F).injective
        (h.trans (_root_.map_zero _).symm))
    have h1s : (1 : F) + s ≠ 0 := by
      intro h0
      exact hw0 (by rw [hwfac, h0, mul_zero])
    have hLw : v.differentialCoeff (KaehlerDifferential.D K F w)
        * w⁻¹
        = v.differentialCoeff (KaehlerDifferential.D K F
            ((1 : F) + s)) * ((1 : F) + s)⁻¹ := by
      rw [hwfac, p0n22_cpf_logDeriv_mul v hcF h1s, Derivation.map_algebraMap,
        v.differentialCoeff_zero, zero_mul, zero_add]
    rcases hs with rfl | hsord
    · rw [hLw, add_zero, Derivation.map_one_eq_zero, v.differentialCoeff_zero, zero_mul,
        mul_zero, mul_zero, _root_.map_zero, zero_pow hp.out.ne_zero]
    · have hs0 : s ≠ 0 := by
        intro h
        rw [h, v.ord_zero] at hsord
        omega
      have hσmem : v.uniformizer⁻¹ * s ∈ v.toValuationSubring := by
        refine v.mem_of_ord_nonneg (mul_ne_zero (inv_ne_zero hπ0) hs0) ?_
        rw [v.ord_mul (inv_ne_zero hπ0) hs0, v.ord_inv, v.ord_uniformizer]
        omega
      obtain ⟨n', rfl⟩ : ∃ n' : ℕ, j = -(n' : ℤ) := ⟨(-j).toNat, by omega⟩
      have hn1 : 1 ≤ n' := by omega
      rw [hLw, show (p : ℤ) * -(n' : ℤ) = -((p * n' : ℕ) : ℤ) from by push_cast; ring,
        _root_.zpow_neg, zpow_natCast, _root_.zpow_neg, zpow_natCast,
        show s = v.uniformizer ^ 1 * (v.uniformizer⁻¹ * s) from by
          rw [pow_one, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul],
        mul_comm ((v.uniformizer ^ (p * n') : F)⁻¹) _,
        mul_comm ((v.uniformizer ^ n' : F)⁻¹) _]
      exact p0n22_cpf_res_logDeriv_principalUnit_cartier_aux v hint hsurj R hn1 (p * n') 1
        le_rfl (by omega) _ hσmem

theorem p0n22_cpf_res_pow_mul_dlog_unit
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : F} (hw0 : w ≠ 0) (hword : v.ord w = 0) (f : F) :
    R.res (f ^ p * ((v.uniformizer)⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K F w)
            * w⁻¹))
      = (R.res (f * ((v.uniformizer)⁻¹
        + v.differentialCoeff (KaehlerDifferential.D K F w)
            * w⁻¹))) ^ p := by
  haveI : CharP F p :=
    charP_of_injective_algebraMap (algebraMap K F).injective p
  haveI : CharP v.ResidueField p :=
    charP_of_injective_ringHom (algebraMap K v.ResidueField).injective p
  have hπ0 : (v.uniformizer : F) ≠ 0 := v.uniformizer_ne_zero
  have hL := p0n22_cpf_logDeriv_mem v hint hw0 hword
  obtain ⟨s, c, r, hr, hf⟩ := p0n22_cpf_exists_laurent_expansion_one v hsurj f
  have hππ : (v.uniformizer : F) * (v.uniformizer)⁻¹ = 1 :=
    mul_inv_cancel₀ hπ0
  have hLHS : f ^ p * ((v.uniformizer)⁻¹
      + v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹)
      = (∑ j ∈ s, c j • v.uniformizer ^ j) ^ p * (v.uniformizer)⁻¹
        + ((∑ j ∈ s, c j • v.uniformizer ^ j) ^ p
            * (v.differentialCoeff (KaehlerDifferential.D K F w)
                * w⁻¹)
          + (v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹
            + v.uniformizer ^ p * r ^ p
                * (v.differentialCoeff
                    (KaehlerDifferential.D K F w) * w⁻¹))) := by
    rw [hf, add_pow_char, mul_pow]
    ring
  have hRHS : f * ((v.uniformizer)⁻¹
      + v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹)
      = (∑ j ∈ s, c j • v.uniformizer ^ j) * (v.uniformizer)⁻¹
        + ((∑ j ∈ s, c j • v.uniformizer ^ j)
            * (v.differentialCoeff (KaehlerDifferential.D K F w)
                * w⁻¹)
          + (r + v.uniformizer * r
              * (v.differentialCoeff
                  (KaehlerDifferential.D K F w) * w⁻¹))) := by
    rw [hf]
    linear_combination r * hππ
  have hπp : (v.uniformizer : F) ^ p
      = v.uniformizer ^ (p - 1) * v.uniformizer := by
    conv_lhs => rw [show p = (p - 1) + 1 from by have h2 := hp.out.two_le; omega]
    rw [pow_succ]
  have hm1 : v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹ ∈ v.toValuationSubring := by
    have heq : v.uniformizer ^ p * r ^ p * (v.uniformizer)⁻¹
        = v.uniformizer ^ (p - 1) * r ^ p := by
      rw [hπp]
      linear_combination v.uniformizer ^ (p - 1) * r ^ p * hππ
    rw [heq]
    exact mul_mem (pow_mem v.uniformizer_mem _) (pow_mem hr _)
  have hm2 : v.uniformizer ^ p * r ^ p
      * (v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹)
      ∈ v.toValuationSubring :=
    mul_mem (mul_mem (pow_mem v.uniformizer_mem _) (pow_mem hr _)) hL
  have hm3 : v.uniformizer * r
      * (v.differentialCoeff (KaehlerDifferential.D K F w) * w⁻¹)
      ∈ v.toValuationSubring :=
    mul_mem (mul_mem v.uniformizer_mem hr) hL
  have hpowp : ∀ j : ℤ, ((v.uniformizer : F) ^ j) ^ p
      = v.uniformizer ^ ((p : ℤ) * j) := by
    intro j
    rw [← zpow_natCast ((v.uniformizer : F) ^ j) p, ← zpow_mul,
      mul_comm j (p : ℤ)]
  have hPp : (∑ j ∈ s, c j • (v.uniformizer : F) ^ j) ^ p
      = ∑ j ∈ s, (c j ^ p) • (v.uniformizer : F) ^ ((p : ℤ) * j) := by
    rw [sum_pow_char]
    exact Finset.sum_congr rfl fun j _ => by rw [_root_.smul_pow, hpowp j]
  rw [hLHS, hRHS]
  simp only [map_add]
  rw [R.res_of_mem _ hm1, R.res_of_mem _ hm2, R.res_of_mem _ hr, R.res_of_mem _ hm3]
  simp only [add_zero]
  rw [add_pow_char]
  congr 1
  ·
    rw [hPp, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, map_smul]
    rcases eq_or_ne j 0 with rfl | hj
    · rw [mul_zero, zpow_zero, one_mul,
        gate_canonicalLocalResidueDataK_uniformizer_inv v R,
        ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow]
    · have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
      have h1 : R.res ((v.uniformizer : F) ^ ((p : ℤ) * j)
          * (v.uniformizer)⁻¹) = 0 := by
        rw [← zpow_sub_one₀ hπ0]
        refine _root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R ?_
        intro hcontra
        have hpj : (p : ℤ) * j = 0 := by linarith
        rcases mul_eq_zero.mp hpj with h | h
        · exact hp0 h
        · exact hj h
      have h2 : R.res ((v.uniformizer : F) ^ j * (v.uniformizer)⁻¹) = 0 := by
        rw [← zpow_sub_one₀ hπ0]
        exact _root_.ModularCurve.MilneAvAg9bRd14CubeRowCartierSliceStart.ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one
          v R (by omega)
      rw [h1, h2, smul_zero, smul_zero, zero_pow hp.out.ne_zero]
  ·
    rw [hPp, Finset.sum_mul, Finset.sum_mul, map_sum, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, map_smul,
      p0n22_cpf_res_zpow_mul_logDeriv_cartier v hint hsurj R hw0 hword j,
      Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow]

include hp hKp in

theorem p0n22_cpf_res_row_at_unit_mul_uniformizer
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R : v.CanonicalLocalResidueDataK)
    {w : F} (hw0 : w ≠ 0) (hword : v.ord w = 0) :
    ∀ n : ℕ, 1 ≤ n →
      R.res (v.differentialCoeff (KaehlerDifferential.D K F
          (w * v.uniformizer))
        * ((w * v.uniformizer) ^ (n + 1))⁻¹) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn
        · exact h
      have hmlt : m < p * m := by
        have h2m : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.out.two_le
        omega
      have hstep : R.res (v.differentialCoeff (KaehlerDifferential.D K
            F (w * v.uniformizer))
            * ((w * v.uniformizer) ^ (p * m + 1))⁻¹)
          = (R.res (v.differentialCoeff (KaehlerDifferential.D K F
              (w * v.uniformizer))
            * ((w * v.uniformizer) ^ (m + 1))⁻¹)) ^ p := by
        rw [p0n22_cpf_row_integrand_eq_pow_mul_dlog v hw0 (p * m),
          p0n22_cpf_row_integrand_eq_pow_mul_dlog v hw0 m]
        have hfp : ((w ^ m * v.uniformizer ^ m : F)⁻¹) ^ p
            = (w ^ (p * m) * v.uniformizer ^ (p * m))⁻¹ := by
          rw [inv_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m p]
        rw [← hfp]
        exact p0n22_cpf_res_pow_mul_dlog_unit v hint hsurj R hw0 hword
          ((w ^ m * v.uniformizer ^ m)⁻¹)
      rw [hstep, ih m hmlt hm1, zero_pow hp.out.ne_zero]
    · have hnK : ((n : ℕ) : K) ≠ 0 := fun h =>
        hpn ((CharP.cast_eq_zero_iff K p n).mp h)
      exact _root_.ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero
        v hsurj
        hint
        R (w * v.uniformizer) hn hnK

include hp hKp in

theorem p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj
    (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (π' : F) (hπ' : v.ord π' = 1)
    (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F π')
      * ((π') ^ (n + 1))⁻¹) = 0 := by
  have hπ'0 : π' ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at hπ'
    omega
  have hw0 : π' * (v.uniformizer)⁻¹ ≠ 0 :=
    mul_ne_zero hπ'0 (inv_ne_zero v.uniformizer_ne_zero)
  have hword : v.ord (π' * (v.uniformizer)⁻¹) = 0 := by
    have h1 := v.ord_mul hπ'0 (inv_ne_zero v.uniformizer_ne_zero)
    rw [v.ord_inv, hπ', v.ord_uniformizer] at h1
    omega
  have hrec : π' * (v.uniformizer)⁻¹ * v.uniformizer = π' := by
    rw [mul_assoc, inv_mul_cancel₀ v.uniformizer_ne_zero, mul_one]
  have h := p0n22_cpf_res_row_at_unit_mul_uniformizer v hint hsurj R hw0 hword n hn
  rw [← hrec]
  exact h

end CharPCartier

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.AlgebraicCurve in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {t : F} (ht : v.ord t = 1) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F t) * (t ^ (n + 1))⁻¹) = 0 := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
  · haveI : Fact (ringChar K).Prime := ⟨hprime⟩
    exact p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj (p := ringChar K) v hint hsurj t ht R hn
  · haveI : CharP K 0 := hzero ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    exact ModularCurve.MilneAvAg9bRd13T2CoordIndepChar3.ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero
      v hsurj hint R t hn (by exact_mod_cast (show n ≠ 0 by omega))

end S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap (solution)
