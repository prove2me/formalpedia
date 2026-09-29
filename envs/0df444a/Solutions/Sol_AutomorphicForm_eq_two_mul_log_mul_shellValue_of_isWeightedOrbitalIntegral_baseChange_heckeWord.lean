-- Prove2me | solution 1 for AutomorphicForm.eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/80b01062-d39a-5c7e-a33f-3f833f06bc1b

import Mathlib
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
import Theorems.Thm_LocalGL2_mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular
import Theorems.Thm_HeckeIntegralSeam_IsHeckeCosetSystem_sum_apply_mul_prod_ofFn_eq_of_mem
import Theorems.Thm_AutomorphicForm_eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord

set_option autoImplicit false

section PieceG4

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 HeckeIntegralSeam
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mWInertKV

namespace G4

section NumberFieldPlace

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

local notation "Fu" => u.adicCompletion F
local notation "Ou" => u.adicCompletionIntegers F

theorem valued_uniformiser {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := by

  obtain ⟨p, hp⟩ := HeightOneSpectrum.intValuation_exists_uniformizer u
  have hpv : Valued.v ((p : 𝓞 F) : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, hp]

  set p' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) p with hp'
  have hp'v : Valued.v (p' : u.adicCompletion F) = WithZero.exp (-1 : ℤ) := hpv
  have hp'max : p' ∈ IsLocalRing.maximalIdeal (u.adicCompletionIntegers F) := by
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 F) F u, hp'v, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hp'max
  obtain ⟨a, ha⟩ := hp'max
  have hle : WithZero.exp (-1 : ℤ) ≤ Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) := by
    rw [← hp'v, ← ha]
    push_cast
    rw [map_mul]
    calc Valued.v (a : u.adicCompletion F) * Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F)
        ≤ 1 * Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) :=
          mul_le_mul_of_nonneg_right a.2 zero_le'
      _ = Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) := one_mul _

  have hlt : Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hne : Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (fun h => hϖ.ne_zero (by exact_mod_cast h))
  refine le_antisymm ?_ hle
  rw [← WithZero.log_le_iff_le_exp hne]
  have h0 : WithZero.log (Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F)) < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]; exact hlt
  omega

theorem finite_quotient_span {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Finite (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) :=
  Finite.of_equiv (IsLocalRing.ResidueField (u.adicCompletionIntegers F))
    (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).toEquiv

theorem natCard_quotient_span_uniformiser {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Nat.card (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm u.asIdeal := by
  classical

  have e1 : (u.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) ≃
      IsLocalRing.ResidueField (u.adicCompletionIntegers F) :=
    (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq).symm.toEquiv

  set f : 𝓞 F →+* IsLocalRing.ResidueField (u.adicCompletionIntegers F) :=
    (IsLocalRing.residue (u.adicCompletionIntegers F)).comp (algebraMap (𝓞 F) (u.adicCompletionIntegers F))
    with hf
  have hfs : Function.Surjective f := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 F) F u
  have hker : RingHom.ker f = u.asIdeal := by
    refine (Ideal.IsMaximal.eq_of_le u.isMaximal (RingHom.ker_ne_top f) fun a ha => ?_).symm
    rw [RingHom.mem_ker]
    exact NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 F) F u ha
  have e2 : (𝓞 F ⧸ u.asIdeal) ≃+* IsLocalRing.ResidueField (u.adicCompletionIntegers F) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hfs)
  rw [Nat.card_congr e1, ← Nat.card_congr e2.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem coe_integralSubgroup_eq_localIntegralSet :
    ((integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F) :
        Subgroup (GL (Fin 2) (u.adicCompletion F))) : Set (GL (Fin 2) (u.adicCompletion F))) =
      localIntegralSet F u := by
  ext g
  have hinj : Function.Injective
      (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)) := Subtype.val_injective
  have hrange : Set.range (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)) =
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := Subtype.range_val
  rw [SetLike.mem_coe, FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj, mem_localIntegralSet]
  simp only [hrange, SetLike.mem_coe]

theorem exists_units_coe_eq_mul_zpow_log {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    {x : u.adicCompletion F} (hx : x ≠ 0) :
    ∃ e : (u.adicCompletionIntegers F)ˣ,
      ((e : u.adicCompletionIntegers F) : u.adicCompletion F) =
        x * ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ WithZero.log (Valued.v x) := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hπ := valued_uniformiser F u hϖ
  set L : ℤ := WithZero.log (Valued.v x) with hL
  have hx' : Valued.v x = WithZero.exp L := (WithZero.exp_log hvx).symm
  have hval : Valued.v (x * ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ L) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hx', ← WithZero.exp_zsmul, zsmul_eq_mul, Int.cast_id, mul_neg_one,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hmem : x * ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ L ∈ u.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hval.le
  obtain ⟨e, he⟩ := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    (a := (⟨_, hmem⟩ : u.adicCompletionIntegers F))).2 hval
  exact ⟨e, congrArg Subtype.val he⟩

def scalarGL : Fuˣ →* GL (Fin 2) Fu := Units.map (Matrix.scalar (Fin 2) : Fu →+* Matrix (Fin 2) (Fin 2) Fu).toMonoidHom

theorem scalarGL_coe (t : Fuˣ) : ((scalarGL F u t : GL (Fin 2) Fu) : Matrix (Fin 2) (Fin 2) Fu) = (t : Fu) • 1 := by
  show Matrix.scalar (Fin 2) (t : Fu) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem scalarGL_comm (t : Fuˣ) (g : GL (Fin 2) Fu) : scalarGL F u t * g = g * scalarGL F u t := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (t : Fu) * (g : Matrix (Fin 2) (Fin 2) Fu) = (g : Matrix (Fin 2) (Fin 2) Fu) * Matrix.scalar (Fin 2) (t : Fu)
  exact (Matrix.scalar_commute (t : Fu) (fun r' => mul_comm _ r') _).eq

theorem eq_scalarGL_of_coe {Z : GL (Fin 2) Fu} {c : Fu} (hc : c ≠ 0) (hZ : (Z : Matrix (Fin 2) (Fin 2) Fu) = c • 1) :
    Z = scalarGL F u (Units.mk0 c hc) := by
  apply Units.ext; rw [hZ, scalarGL_coe, Units.val_mk0]

theorem sum_indicator_eq_walk (ϖ₀ : Ou) (hirr : Irreducible ϖ₀) (h0 : algebraMap Ou Fu ϖ₀ ≠ 0)
    {m : ℕ} (r : Fin m → GL (Fin 2) Fu) (hr : IsHeckeCosetSystem (integralSubgroup Ou Fu) (diagPi ϖ₀ h0) r)
    (Z : GL (Fin 2) Fu) (hZ : (Z : Matrix (Fin 2) (Fin 2) Fu) = algebraMap Ou Fu ϖ₀ • (1 : Matrix (Fin 2) (Fin 2) Fu))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2))
    (k j : ℕ) (x : GL (Fin 2) Fu) (a b : ℤ)
    (hx : (Z ^ j)⁻¹ * x ∈ HeckePair.doubleCoset (integralSubgroup Ou Fu) (diagPi ϖ₀ h0 ^ a * localRepInf ϖ₀ h0 ^ b)) :
    ∑ ι : Fin k → Fin m, (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => r (ι i)).prod * Z ^ j)⁻¹ * x) =
      ((if a + b = (k : ℤ) then W k (a - b).natAbs else 0 : ℕ) : ℂ) := by
  classical
  haveI : Finite (Ou ⧸ Ideal.span {ϖ₀}) := finite_quotient_span F u hirr
  have hZeq : Z = scalarGL F u (Units.mk0 _ h0) := eq_scalarGL_of_coe F u h0 hZ
  have hcomm : ∀ g : GL (Fin 2) Fu, Commute (Z ^ j)⁻¹ g := fun g => by
    rw [hZeq, ← map_pow, ← map_inv]; exact scalarGL_comm F u _ g
  have hterm : ∀ ι : Fin k → Fin m,
      ((List.ofFn fun i => r (ι i)).prod * Z ^ j)⁻¹ * x = ((List.ofFn fun i => r (ι i)).prod)⁻¹ * ((Z ^ j)⁻¹ * x) := by
    intro ι
    rw [mul_inv_rev, (hcomm _).eq, mul_assoc]
  simp_rw [hterm, ← coe_integralSubgroup_eq_localIntegralSet F u]
  have hcast : ∀ g : GL (Fin 2) Fu,
      ((integralSubgroup Ou Fu : Subgroup (GL (Fin 2) Fu)) : Set (GL (Fin 2) Fu)).indicator (fun _ => (1 : ℂ)) g =
        ((((integralSubgroup Ou Fu : Subgroup (GL (Fin 2) Fu)) : Set (GL (Fin 2) Fu)).indicator (fun _ => (1 : ℕ)) g : ℕ) : ℂ) := by
    intro g; simp only [Set.indicator_apply]; split_ifs <;> simp
  simp_rw [hcast]
  rw [← Nat.cast_sum]
  congr 1
  have hq := natCard_quotient_span_uniformiser F u hirr
  exact LocalGL2.sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow ϖ₀ h0 hirr r hr
    W h00 h0s (fun k => by rw [hq]; exact hroot k) (fun k d => by rw [hq]; exact hstep k d) k a b _ hx

theorem sum_indicator_heckeWord_diagUnits2_mul_unipotentGL2
    (ϖ : Ou) (hϖ : Irreducible ϖ) (hϖ0 : algebraMap Ou Fu ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) Fu)
    (hrT : IsHeckeCosetSystem (integralSubgroup Ou Fu) (diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) Fu) (hz : (z : Matrix (Fin 2) (Fin 2) Fu) = algebraMap Ou Fu ϖ • (1 : Matrix (Fin 2) (Fin 2) Fu))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2))
    (k j : ℕ) (α β : Fuˣ) (uα uβ : Ouˣ) (ra rb : ℤ)
    (hα : (α : Fu) = algebraMap Ou Fu uα * algebraMap Ou Fu ϖ ^ ra)
    (hβ : (β : Fu) = algebraMap Ou Fu uβ * algebraMap Ou Fu ϖ ^ rb)
    (t : Fu) (m : ℤ) (hm : m ≤ min ra rb)
    (ht1 : ∃ r : Ou, (α : Fu) * t = algebraMap Ou Fu ϖ ^ m * algebraMap Ou Fu r)
    (ht2 : m < min ra rb → ¬ ∃ r : Ou, (α : Fu) * t = algebraMap Ou Fu ϖ ^ (m + 1) * algebraMap Ou Fu r) :
    ∑ ι : Fin k → Fin n, (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (diagUnits2 α β * unipotentGL2 t)) =
      ((if ra + rb = (k : ℤ) + 2 * j then W k (ra + rb - 2 * m).natAbs else 0 : ℕ) : ℂ) := by
  classical
  set π : Fu := algebraMap Ou Fu ϖ with hπ

  set g : GL (Fin 2) Fu := (z ^ j)⁻¹ * (diagUnits2 α β * unipotentGL2 t) with hg
  have hzj : ((z ^ j)⁻¹ : GL (Fin 2) Fu) = scalarGL F u ((Units.mk0 π hϖ0) ^ j)⁻¹ := by
    rw [eq_scalarGL_of_coe F u hϖ0 hz, map_inv, map_pow]
  have hzjc : (((z ^ j)⁻¹ : GL (Fin 2) Fu) : Matrix (Fin 2) (Fin 2) Fu) = (π ^ j)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) Fu) := by
    rw [hzj, scalarGL_coe, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0]
  have hgc : (g : Matrix (Fin 2) (Fin 2) Fu) =
      !![(π ^ j)⁻¹ * (α : Fu), (π ^ j)⁻¹ * ((α : Fu) * t); 0, (π ^ j)⁻¹ * (β : Fu)] := by
    rw [hg, Units.val_mul, Units.val_mul, hzjc, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
    ext i j'
    fin_cases i <;> fin_cases j' <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 : (g : Matrix (Fin 2) (Fin 2) Fu) 0 0 = algebraMap Ou Fu uα * π ^ (ra - j) := by
    rw [hgc]; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    rw [hα, zpow_sub₀ hϖ0, zpow_natCast, div_eq_mul_inv]; ring
  have e11 : (g : Matrix (Fin 2) (Fin 2) Fu) 1 1 = algebraMap Ou Fu uβ * π ^ (rb - j) := by
    rw [hgc]; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    rw [hβ, zpow_sub₀ hϖ0, zpow_natCast, div_eq_mul_inv]; ring
  have e10 : (g : Matrix (Fin 2) (Fin 2) Fu) 1 0 = 0 := by
    rw [hgc]; simp
  have e01 : (g : Matrix (Fin 2) (Fin 2) Fu) 0 1 = (π ^ j)⁻¹ * ((α : Fu) * t) := by
    rw [hgc]; simp

  have hmn : m - j ≤ ra + rb - j - m := by
    have := min_le_left ra rb; have := min_le_right ra rb; omega
  have hcell : g ∈ HeckePair.doubleCoset (integralSubgroup Ou Fu)
      (diagPi ϖ hϖ0 ^ (m - j) * localRepInf ϖ hϖ0 ^ (ra + rb - j - m)) := by
    rw [LocalGL2.mem_doubleCoset_diagPi_zpow_mul_localRepInf_zpow_iff_of_upperTriangular hϖ hϖ0 g uα uβ
      (ra - j) (rb - j) e00 e10 e11 hmn]
    refine ⟨by ring, ?_, ?_, ?_⟩
    · rw [min_sub_sub_right]; exact sub_le_sub_right hm _
    · obtain ⟨r, hr⟩ := ht1
      refine ⟨r, ?_⟩
      rw [e01, hr, zpow_sub₀ hϖ0, zpow_natCast, div_eq_mul_inv]; ring
    · intro hlt hex
      have hlt' : m < min ra rb := by
        rw [min_sub_sub_right] at hlt; exact (sub_lt_sub_iff_right _).1 hlt
      apply ht2 hlt'
      obtain ⟨r, hr⟩ := hex
      refine ⟨r, ?_⟩
      rw [e01, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ hϖ0)] at hr
      rw [hr, ← mul_assoc, ← zpow_natCast π j, ← zpow_add₀ hϖ0]
      congr 2; ring
  rw [sum_indicator_eq_walk F u ϖ hϖ hϖ0 rT hrT z hz W h00 h0s hroot hstep k j _ (m - j) (ra + rb - j - m) hcell]
  congr 1
  have habs : (m - ↑j - (ra + rb - ↑j - m)).natAbs = (ra + rb - 2 * m).natAbs := by
    rw [show m - ↑j - (ra + rb - ↑j - m) = -(ra + rb - 2 * m) by ring, Int.natAbs_neg]
  by_cases h : ra + rb = (k : ℤ) + 2 * j
  · rw [if_pos h, if_pos (by omega), habs]
  · rw [if_neg h, if_neg (by omega)]

theorem norm_eq_zpow_log {x : Fu} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ WithZero.log (Valued.v x) := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
  push_cast
  have hu : WithZero.unzero hv0 = Multiplicative.ofAdd (WithZero.log (Valued.v x)) :=
    WithZero.coe_inj.1 (by rw [WithZero.coe_unzero hv0]; exact (WithZero.exp_log hv0).symm)
  rw [hu]; rfl

private theorem _root_.P2mWInertKV.G4.one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm u.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact u.ne_bot
  have h1 : Ideal.absNorm u.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact u.isPrime.ne_top
  have : (2 : ℝ) ≤ (Ideal.absNorm u.asIdeal : ℝ) := by exact_mod_cast (show 2 ≤ Ideal.absNorm u.asIdeal by omega)
  linarith

p2m_export "P2mWInertKV.G4" "one_lt_absNorm"

theorem exists_unit_eq_mul_zpow_of_norm_eq {ϖ : Ou} (hϖ : Irreducible ϖ) (hϖ0 : algebraMap Ou Fu ϖ ≠ 0) {x : Fu} {r : ℤ}
    (hx : ‖x‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-r)) :
    ∃ e : Ouˣ, x = algebraMap Ou Fu (e : Ou) * algebraMap Ou Fu ϖ ^ r := by
  have hN := one_lt_absNorm F u
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; exact (zpow_pos (by linarith) _).ne' hx.symm |>.elim
  have hlog : WithZero.log (Valued.v x) = -r := by
    have h := (norm_eq_zpow_log F u hx0).symm.trans hx
    exact zpow_right_injective₀ (by linarith) hN.ne' h
  obtain ⟨e, he⟩ := exists_units_coe_eq_mul_zpow_log F u hϖ hx0
  refine ⟨e, ?_⟩
  have hπ0 : ((ϖ : Ou) : Fu) ≠ 0 := hϖ0
  show x = ((e : Ou) : Fu) * ((ϖ : Ou) : Fu) ^ r
  rw [he, hlog, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]

theorem valued_coe_unit (e : Ouˣ) : Valued.v (((e : Ou) : Fu)) = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 e.isUnit

theorem sum_indicator_heckeWord_diagUnits2_of_norm_eq
    (ϖ : Ou) (hϖ : Irreducible ϖ) (hϖ0 : algebraMap Ou Fu ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) Fu)
    (hrT : IsHeckeCosetSystem (integralSubgroup Ou Fu) (diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) Fu) (hz : (z : Matrix (Fin 2) (Fin 2) Fu) = algebraMap Ou Fu ϖ • (1 : Matrix (Fin 2) (Fin 2) Fu))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2))
    (k j : ℕ) (α β : Fuˣ) (ra rb : ℤ)
    (hα : ‖(α : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-ra))
    (hβ : ‖(β : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-rb)) :
    ∑ ι : Fin k → Fin n, (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (diagUnits2 α β * unipotentGL2 (0 : Fu))) =
      ((if ra + rb = (k : ℤ) + 2 * j then W k (ra + rb - 2 * min ra rb).natAbs else 0 : ℕ) : ℂ) := by
  obtain ⟨uα, huα⟩ := exists_unit_eq_mul_zpow_of_norm_eq F u hϖ hϖ0 hα
  obtain ⟨uβ, huβ⟩ := exists_unit_eq_mul_zpow_of_norm_eq F u hϖ hϖ0 hβ
  exact sum_indicator_heckeWord_diagUnits2_mul_unipotentGL2 F u ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep k j
    α β uα uβ ra rb huα huβ 0 (min ra rb) le_rfl ⟨0, by rw [mul_zero, map_zero, mul_zero]⟩
    (fun h => absurd h (lt_irrefl _))

theorem sum_indicator_heckeWord_diagUnits2_mul_unipotentGL2_of_norm_eq
    (ϖ : Ou) (hϖ : Irreducible ϖ) (hϖ0 : algebraMap Ou Fu ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) Fu)
    (hrT : IsHeckeCosetSystem (integralSubgroup Ou Fu) (diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) Fu) (hz : (z : Matrix (Fin 2) (Fin 2) Fu) = algebraMap Ou Fu ϖ • (1 : Matrix (Fin 2) (Fin 2) Fu))
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2))
    (k j : ℕ) (α β : Fuˣ) (ra rb : ℤ)
    (hα : ‖(α : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-ra))
    (hβ : ‖(β : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-rb))
    (t : Fu) (s : ℤ) (ht : ‖t‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-s)) :
    ∑ ι : Fin k → Fin n, (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (diagUnits2 α β * unipotentGL2 t)) =
      ((if ra + rb = (k : ℤ) + 2 * j then W k (ra + rb - 2 * min (min ra rb) (ra + s)).natAbs else 0 : ℕ) : ℂ) := by
  obtain ⟨uα, huα⟩ := exists_unit_eq_mul_zpow_of_norm_eq F u hϖ hϖ0 hα
  obtain ⟨uβ, huβ⟩ := exists_unit_eq_mul_zpow_of_norm_eq F u hϖ hϖ0 hβ
  obtain ⟨e, he⟩ := exists_unit_eq_mul_zpow_of_norm_eq F u hϖ hϖ0 ht
  set π : Fu := algebraMap Ou Fu ϖ with hπ
  set m : ℤ := min (min ra rb) (ra + s) with hmdef
  have hm : m ≤ min ra rb := min_le_left _ _
  have hm2 : m ≤ ra + s := min_le_right _ _
  have hαt : (α : Fu) * t = algebraMap Ou Fu (uα * e : Ou) * π ^ (ra + s) := by
    rw [huα, he, map_mul, zpow_add₀ hϖ0]; ring
  refine sum_indicator_heckeWord_diagUnits2_mul_unipotentGL2 F u ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep k j
    α β uα uβ ra rb huα huβ t m hm ?_ ?_
  · refine ⟨uα * e * ϖ ^ (ra + s - m).toNat, ?_⟩
    rw [hαt]
    simp only [map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg (show 0 ≤ ra + s - m by omega)]
    rw [show ra + s = m + (ra + s - m) by ring, zpow_add₀ hϖ0]
    rw [← hπ]
    ring
  · intro hlt ⟨r, hr⟩
    have hms : m = ra + s := by
      rcases le_total (min ra rb) (ra + s) with h | h
      · exfalso; rw [hmdef, min_eq_left h] at hlt; exact lt_irrefl _ hlt
      · rw [hmdef, min_eq_right h]
    rw [hαt, hms, zpow_add_one₀ hϖ0] at hr

    have hπs : π ^ (ra + s) ≠ 0 := zpow_ne_zero _ hϖ0
    have hue : algebraMap Ou Fu (uα * e : Ou) = π * algebraMap Ou Fu r := by
      have := hr
      rw [mul_comm (algebraMap Ou Fu (↑uα * ↑e)) (π ^ (ra + s)), mul_assoc] at this
      exact mul_left_cancel₀ hπs this
    have hv1 : Valued.v (algebraMap Ou Fu (uα * e : Ou)) = 1 := valued_coe_unit F u (uα * e)
    have hvπ : Valued.v (algebraMap Ou Fu ϖ) = WithZero.exp (-1 : ℤ) := valued_uniformiser F u hϖ
    have hv2 : Valued.v (π * algebraMap Ou Fu r) < 1 := by
      rw [map_mul, hπ, hvπ]
      calc WithZero.exp (-1 : ℤ) * Valued.v (algebraMap Ou Fu r) ≤ WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul_of_nonneg_left r.2 zero_le'
        _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    rw [hue] at hv1
    exact absurd hv1 hv2.ne

theorem eq_zero_or_exists_norm_eq_zpow (t : Fu) : t = 0 ∨ ∃ s : ℤ, ‖t‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-s) := by
  by_cases ht : t = 0
  · exact Or.inl ht
  · right
    have hv0 : (Valued.v t : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 ht
    refine ⟨-WithZero.log (Valued.v t), ?_⟩
    rw [neg_neg]; exact norm_eq_zpow_log F u ht

theorem sum_indicator_heckeWord_diagUnits2_mul_unipotentGL2_eq_zero_of_ne
    (ϖ : Ou) (hϖ : Irreducible ϖ) (hϖ0 : algebraMap Ou Fu ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) Fu)
    (hrT : IsHeckeCosetSystem (integralSubgroup Ou Fu) (diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) Fu) (hz : (z : Matrix (Fin 2) (Fin 2) Fu) = algebraMap Ou Fu ϖ • (1 : Matrix (Fin 2) (Fin 2) Fu))
    (k j : ℕ) (α β : Fuˣ) (ra rb : ℤ)
    (hα : ‖(α : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-ra))
    (hβ : ‖(β : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-rb))
    (hne : ra + rb ≠ (k : ℤ) + 2 * j) (t : Fu) :
    ∑ ι : Fin k → Fin n, (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * (diagUnits2 α β * unipotentGL2 t)) = 0 := by
  classical

  let W : ℕ → ℕ → ℕ := fun k d => Nat.rec (motive := fun _ => ℕ → ℕ) (fun d => if d = 0 then 1 else 0)
    (fun _ Wk d => if d = 0 then (Ideal.absNorm u.asIdeal + 1) * Wk 1 else Wk (d - 1) + Ideal.absNorm u.asIdeal * Wk (d + 1)) k d
  have h00 : W 0 0 = 1 := rfl
  have h0s : ∀ d : ℕ, W 0 (d + 1) = 0 := fun d => rfl
  have hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm u.asIdeal + 1) * W k 1 := fun k => rfl
  have hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm u.asIdeal * W k (d + 2) := fun k d => rfl
  rcases eq_zero_or_exists_norm_eq_zpow F u t with rfl | ⟨s, hs⟩
  · rw [sum_indicator_heckeWord_diagUnits2_of_norm_eq F u ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep k j α β ra rb hα hβ,
      if_neg hne, Nat.cast_zero]
  · rw [sum_indicator_heckeWord_diagUnits2_mul_unipotentGL2_of_norm_eq F u ϖ hϖ hϖ0 n rT hrT z hz W h00 h0s hroot hstep
      k j α β ra rb hα hβ t s hs, if_neg hne, Nat.cast_zero]

theorem norm_units_div_eq_zpow (α β : Fuˣ) (ra rb : ℤ)
    (hα : ‖(α : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-ra))
    (hβ : ‖(β : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-rb)) :
    ‖((β * α⁻¹ : Fuˣ) : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (ra - rb) := by
  have hN : (0 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := by have := one_lt_absNorm F u; linarith
  rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hα, hβ, ← zpow_neg, neg_neg,
    ← zpow_add₀ hN.ne', show -rb + ra = ra - rb by ring]

theorem norm_units_div_eq_one_iff (α β : Fuˣ) (ra rb : ℤ)
    (hα : ‖(α : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-ra))
    (hβ : ‖(β : Fu)‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ (-rb)) :
    ‖((β * α⁻¹ : Fuˣ) : Fu)‖ = 1 ↔ ra = rb := by
  have hN := one_lt_absNorm F u
  rw [norm_units_div_eq_zpow F u α β ra rb hα hβ, ← zpow_zero (Ideal.absNorm u.asIdeal : ℝ)]
  constructor
  · intro h; have := zpow_right_injective₀ (by linarith) hN.ne' h; omega
  · intro h; rw [h, sub_self]

end NumberFieldPlace

end G4

end P2mWInertKV

end

end PieceG4

section PieceBiInv

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace P2mWInertKV

open AutomorphicForm

section HeckeWordBiInvariant

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

local notation "Fu" => HeightOneSpectrum.adicCompletion F u

theorem mem_localIntegralSet_of_mem_integralSubgroup' {g : GL (Fin 2) Fu}
    (hg : g ∈ LocalGL2.integralSubgroup (u.adicCompletionIntegers F) Fu) : g ∈ localIntegralSet F u := by
  obtain ⟨k, rfl⟩ := hg
  refine (mem_localIntegralSet F u).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((k : Matrix (Fin 2) (Fin 2) (u.adicCompletionIntegers F)) i j).2
  · rw [← map_inv]
    exact (((k⁻¹ : GL (Fin 2) (u.adicCompletionIntegers F)) :
      Matrix (Fin 2) (Fin 2) (u.adicCompletionIntegers F)) i j).2

theorem mem_integralSubgroup_of_mem_localIntegralSet' {g : GL (Fin 2) Fu} (hg : g ∈ localIntegralSet F u) :
    g ∈ LocalGL2.integralSubgroup (u.adicCompletionIntegers F) Fu := by
  obtain ⟨h1, h2⟩ := (mem_localIntegralSet F u).1 hg
  let M : Matrix (Fin 2) (Fin 2) (u.adicCompletionIntegers F) :=
    fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) Fu) i j, h1 i j⟩
  let M' : Matrix (Fin 2) (Fin 2) (u.adicCompletionIntegers F) :=
    fun i j => ⟨((g⁻¹ : GL (Fin 2) Fu) : Matrix (Fin 2) (Fin 2) Fu) i j, h2 i j⟩
  have hM : M.map (algebraMap (u.adicCompletionIntegers F) Fu) = (g : Matrix (Fin 2) (Fin 2) Fu) := by
    ext i j; rfl
  have hM' : M'.map (algebraMap (u.adicCompletionIntegers F) Fu) = ((g⁻¹ : GL (Fin 2) Fu) : Matrix (Fin 2) (Fin 2) Fu) := by
    ext i j; rfl
  have hinj : ∀ A B : Matrix (Fin 2) (Fin 2) (u.adicCompletionIntegers F),
      A.map (algebraMap (u.adicCompletionIntegers F) Fu) = B.map (algebraMap (u.adicCompletionIntegers F) Fu) → A = B := by
    intro A B h
    ext i j
    have h' := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at h'
    exact_mod_cast h'
  have h3 : M * M' = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
      Units.val_one])
  have h4 : M' * M = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, inv_mul_cancel,
      Units.val_one])
  refine ⟨⟨M, M', h3, h4⟩, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_map_apply]
  exact hM

theorem inv_mem_localIntegralSet' {g : GL (Fin 2) Fu} (hg : g ∈ localIntegralSet F u) :
    g⁻¹ ∈ localIntegralSet F u := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem inv_mem_localIntegralSet_iff' (g : GL (Fin 2) Fu) :
    g⁻¹ ∈ localIntegralSet F u ↔ g ∈ localIntegralSet F u := by
  refine ⟨fun h => ?_, inv_mem_localIntegralSet' F u⟩
  have := inv_mem_localIntegralSet' F u h
  rwa [inv_inv] at this

theorem mul_mem_localIntegralSet' {g h : GL (Fin 2) Fu} (hg : g ∈ localIntegralSet F u)
    (hh : h ∈ localIntegralSet F u) : g * h ∈ localIntegralSet F u :=
  mem_localIntegralSet_of_mem_integralSubgroup' F u
    (Subgroup.mul_mem _ (mem_integralSubgroup_of_mem_localIntegralSet' F u hg)
      (mem_integralSubgroup_of_mem_localIntegralSet' F u hh))

theorem mul_mem_localIntegralSet_iff_left' {g h : GL (Fin 2) Fu} (hh : h ∈ localIntegralSet F u) :
    g * h ∈ localIntegralSet F u ↔ g ∈ localIntegralSet F u := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet' F u hg hh⟩
  have := mul_mem_localIntegralSet' F u hgh (inv_mem_localIntegralSet' F u hh)
  rwa [mul_inv_cancel_right] at this

theorem indicator_localIntegralSet_congr {X Y : GL (Fin 2) Fu}
    (h : X ∈ localIntegralSet F u ↔ Y ∈ localIntegralSet F u) :
    (localIntegralSet F u).indicator (fun _ => (1 : ℂ)) X = (localIntegralSet F u).indicator (fun _ => (1 : ℂ)) Y := by
  by_cases hX : X ∈ localIntegralSet F u
  · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (h.1 hX)]
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun hY => hX (h.2 hY))]

theorem mul_eq_mul_of_coe_eq_smul_one (z : GL (Fin 2) Fu) (c : Fu)
    (hz : (z : Matrix (Fin 2) (Fin 2) Fu) = c • (1 : Matrix (Fin 2) (Fin 2) Fu)) (x : GL (Fin 2) Fu) :
    x * z = z * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem indicator_mul_zpow_mul_eq (z : GL (Fin 2) Fu) (hzc : ∀ x : GL (Fin 2) Fu, x * z = z * x) (j : ℕ)
    (x : GL (Fin 2) Fu) (w : GL (Fin 2) Fu) (hw : w ∈ LocalGL2.integralSubgroup (u.adicCompletionIntegers F) Fu) :
    (localIntegralSet F u).indicator (fun _ => (1 : ℂ)) (x * w * z ^ j) =
      (localIntegralSet F u).indicator (fun _ => (1 : ℂ)) (x * z ^ j) := by
  refine indicator_localIntegralSet_congr F u ?_
  rw [mul_assoc, (Commute.pow_right (hzc w) j).eq, ← mul_assoc,
    mul_mem_localIntegralSet_iff_left' F u (mem_localIntegralSet_of_mem_integralSubgroup' F u hw)]

theorem indicator_inv_mul_eq (z P y : GL (Fin 2) Fu) (j : ℕ) :
    (localIntegralSet F u).indicator (fun _ => (1 : ℂ)) ((P * z ^ j)⁻¹ * y) =
      (localIntegralSet F u).indicator (fun _ => (1 : ℂ)) (y⁻¹ * P * z ^ j) := by
  refine indicator_localIntegralSet_congr F u ?_
  rw [← inv_mem_localIntegralSet_iff' F u ((P * z ^ j)⁻¹ * y), mul_inv_rev, inv_inv, mul_assoc]

theorem heckeWord_biInvariant
    {ϖ : u.adicCompletionIntegers F} (hϖ0 : algebraMap (u.adicCompletionIntegers F) Fu ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) Fu)
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (u.adicCompletionIntegers F) Fu) (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) Fu)
    (hz : (z : Matrix (Fin 2) (Fin 2) Fu) =
      algebraMap (u.adicCompletionIntegers F) Fu ϖ • (1 : Matrix (Fin 2) (Fin 2) Fu))
    (k j : ℕ) (g k₁ k₂ : GL (Fin 2) Fu) (hk₁ : k₁ ∈ localIntegralSet F u) (hk₂ : k₂ ∈ localIntegralSet F u) :
    (∑ ι : Fin k → Fin n, (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun m => rT (ι m)).prod * z ^ j)⁻¹ * (k₁ * g * k₂))) =
      ∑ ι : Fin k → Fin n, (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun m => rT (ι m)).prod * z ^ j)⁻¹ * g) := by
  have hzc : ∀ x : GL (Fin 2) Fu, x * z = z * x := mul_eq_mul_of_coe_eq_smul_one F u z _ hz

  have hA : ∀ ι : Fin k → Fin n,
      (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rT (ι m)).prod * z ^ j)⁻¹ * (k₁ * g * k₂)) =
        (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
          (g⁻¹ * k₁⁻¹ * (List.ofFn fun m => rT (ι m)).prod * z ^ j) := by
    intro ι
    rw [← mul_inv_rev, ← indicator_inv_mul_eq F u z _ (k₁ * g) j]
    refine indicator_localIntegralSet_congr F u ?_
    rw [← mul_assoc _ (k₁ * g) k₂, mul_mem_localIntegralSet_iff_left' F u hk₂]
  have hB : ∀ ι : Fin k → Fin n,
      (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun m => rT (ι m)).prod * z ^ j)⁻¹ * g) =
        (localIntegralSet F u).indicator (fun _ => (1 : ℂ))
          (g⁻¹ * (List.ofFn fun m => rT (ι m)).prod * z ^ j) := fun ι =>
    indicator_inv_mul_eq F u z _ g j
  rw [Finset.sum_congr rfl fun ι _ => hA ι, Finset.sum_congr rfl fun ι _ => hB ι]
  exact HeckeIntegralSeam.IsHeckeCosetSystem.sum_apply_mul_prod_ofFn_eq_of_mem hrT
    (fun x => (localIntegralSet F u).indicator (fun _ => (1 : ℂ)) (x * z ^ j))
    (fun x w hw => indicator_mul_zpow_mul_eq F u z hzc j x w hw) k g⁻¹ k₁⁻¹
    (mem_integralSubgroup_of_mem_localIntegralSet' F u (inv_mem_localIntegralSet' F u hk₁))

end HeckeWordBiInvariant

end P2mWInertKV

end PieceBiInv

section PieceG7ab

set_option autoImplicit false

namespace P2mWInertKV
namespace G7

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem measurable_indicator_inv_mul (g : GL (Fin 2) Kv) :
    Measurable[localGLBorel K v] (fun x : GL (Fin 2) Kv => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (g⁻¹ * x)) := by
  letI : MeasurableSpace (GL (Fin 2) Kv) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) Kv) := ⟨rfl⟩
  have h : (fun x : GL (Fin 2) Kv => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (g⁻¹ * x)) =
      ((fun x : GL (Fin 2) Kv => g⁻¹ * x) ⁻¹' localIntegralSet K v).indicator (fun _ => (1 : ℂ)) := by
    funext x
    rfl
  rw [h]
  exact measurable_const.indicator ((isOpen_localIntegralSet K v).preimage (continuous_const_mul _)).measurableSet

theorem fK_measurable (S : Finset (Fin 2 →₀ ℕ)) (coef : (Fin 2 →₀ ℕ) → ℂ) (nK : ℕ)
    (rK : Fin nK → GL (Fin 2) Kv) (zK : GL (Fin 2) Kv) :
    Measurable[localGLBorel K v] (fun x : GL (Fin 2) Kv =>
      ∑ e ∈ S, coef e *
        ∑ ι : Fin (e 0) → Fin nK,
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x)) := by
  letI : MeasurableSpace (GL (Fin 2) Kv) := localGLBorel K v
  refine Finset.measurable_sum S fun e _ => ?_
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun ι _ => ?_
  exact measurable_indicator_inv_mul K v _

theorem fK_bounded (S : Finset (Fin 2 →₀ ℕ)) (coef : (Fin 2 →₀ ℕ) → ℂ) (nK : ℕ)
    (rK : Fin nK → GL (Fin 2) Kv) (zK : GL (Fin 2) Kv) :
    ∃ C : ℝ, ∀ g : GL (Fin 2) Kv,
      ‖∑ e ∈ S, coef e *
          ∑ ι : Fin (e 0) → Fin nK,
            (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
              (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * g)‖ ≤ C := by
  refine ⟨∑ e ∈ S, ‖coef e‖ * ((Finset.univ : Finset (Fin (e 0) → Fin nK)).card : ℝ), fun g => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ι _ => ?_
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

end P2mWInertKV.G7

end PieceG7ab

section PieceG7d

set_option autoImplicit false

namespace P2mWInertKV
namespace G7

open NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped Classical

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) (i j : Fin 2) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1 := by
  rw [mem_localIntegralSet] at hg
  have h := hg.1 i j
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  exact Valued.toNormedField.norm_le_one_iff.2 h

theorem conj_entry01 (a b : Kvˣ) (y : Kv) :
    (((unipotentGL2 y)⁻¹ * diagUnits2 a b * unipotentGL2 y : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 0 1 =
      ((a : Kv) - b) * y := by
  have hinv : (unipotentGL2 y : GL (Fin 2) Kv)⁻¹ = unipotentGL2 (-y) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
  rw [hinv, Units.val_mul, Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem norm_entry01_le_of_inv_mul_mem {h g : GL (Fin 2) Kv} (hk : h⁻¹ * g ∈ localIntegralSet K v) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv) 0 1‖ ≤
      max ‖(h : Matrix (Fin 2) (Fin 2) Kv) 0 0‖ ‖(h : Matrix (Fin 2) (Fin 2) Kv) 0 1‖ := by
  have hg : g = h * (h⁻¹ * g) := by rw [mul_inv_cancel_left]
  set k := h⁻¹ * g with hkdef
  have hk' := norm_entry_le_one_of_mem K v hk
  rw [hg, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hk' 0 1)
  · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hk' 1 1)

theorem fK_support_bound
    (S : Finset (Fin 2 →₀ ℕ)) (coef : (Fin 2 →₀ ℕ) → ℂ)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) Kv) (zK : GL (Fin 2) Kv)
    (fK : GL (Fin 2) Kv → ℂ)
    (hfK : fK = fun x => ∑ e ∈ S, coef e *
      ∑ ι : Fin (e 0) → Fin nK,
        (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
    (a b : Kvˣ) (hab : a ≠ b) :
    ∃ M : ℕ, ∀ y : Kv, fK ((unipotentGL2 y)⁻¹ * diagUnits2 a b * unipotentGL2 y) ≠ 0 →
      ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ M := by

  set row : GL (Fin 2) Kv → ℝ := fun h => max ‖(h : Matrix (Fin 2) (Fin 2) Kv) 0 0‖ ‖(h : Matrix (Fin 2) (Fin 2) Kv) 0 1‖
    with hrow
  set B : ℝ := ∑ e ∈ S, ∑ ι : Fin (e 0) → Fin nK, row ((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1)) with hB
  have hrow0 : ∀ h, 0 ≤ row h := fun h => le_max_of_le_left (norm_nonneg _)
  have hle : ∀ e ∈ S, ∀ ι : Fin (e 0) → Fin nK, row ((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1)) ≤ B := by
    intro e he ι
    rw [hB]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun e' : Fin 2 →₀ ℕ => ∑ ι' : Fin (e' 0) → Fin nK, row ((List.ofFn fun m => rK (ι' m)).prod * zK ^ (e' 1)))
      (fun e' _ => Finset.sum_nonneg fun ι' _ => hrow0 _) he)
    exact Finset.single_le_sum (f := fun ι' : Fin (e 0) → Fin nK => row ((List.ofFn fun m => rK (ι' m)).prod * zK ^ (e 1)))
      (fun ι' _ => hrow0 _) (Finset.mem_univ ι)
  have hab' : (a : Kv) - b ≠ 0 := sub_ne_zero.2 fun h => hab (Units.ext h)
  have hpos : 0 < ‖(a : Kv) - b‖ := norm_pos_iff.2 hab'
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (B / ‖(a : Kv) - b‖) (one_lt_absNorm_real K v)
  refine ⟨M, fun y hy => ?_⟩

  rw [hfK] at hy
  obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have hne' : ∑ ι : Fin (e 0) → Fin nK, (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
      (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ *
        ((unipotentGL2 y)⁻¹ * diagUnits2 a b * unipotentGL2 y)) ≠ 0 := by
    intro h0; exact hne (by rw [h0, mul_zero])
  obtain ⟨ι, -, hι⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hmem : ((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ *
      ((unipotentGL2 y)⁻¹ * diagUnits2 a b * unipotentGL2 y) ∈ localIntegralSet K v := by
    by_contra hc; exact hι (Set.indicator_of_notMem hc _)
  have h1 := norm_entry01_le_of_inv_mul_mem K v hmem
  rw [conj_entry01, norm_mul] at h1
  have h2 : ‖(a : Kv) - b‖ * ‖y‖ ≤ B := h1.trans (hle e he ι)
  have h3 : ‖y‖ ≤ B / ‖(a : Kv) - b‖ := by rw [le_div_iff₀ hpos, mul_comm]; exact h2
  exact h3.trans hM.le

end P2mWInertKV.G7

end PieceG7d

section PieceG7s46

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AutomorphicForm.SatakeCombination (univWord)
open Finset

namespace P2mWInertKV
namespace G7

theorem W_eq_zero_of_lt (q : ℕ) (W : ℕ → ℕ → ℕ) (h0s : ∀ s : ℕ, W 0 (s + 1) = 0)
    (hstep : ∀ n s : ℕ, W (n + 1) (s + 1) = W n s + q * W n (s + 2)) :
    ∀ n s : ℕ, n < s → W n s = 0 := by
  intro n
  induction n with
  | zero =>
    intro s hs
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    exact h0s t
  | succ n ih =>
    intro s hs
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [hstep, ih t (by omega), ih (t + 2) (by omega)]
    simp

theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (u : ℕ → M) (n : ℕ) :
    ∑ i ∈ Icc 1 n, u i = ∑ i ∈ range n, u (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem mass_eq (q : ℕ) (hq : 1 ≤ q) (s : ℕ) :
    ((((s + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (s + 1) - (q : ℝ) ^ s) : ℝ) : ℂ) = ((s + 1 : ℕ) : ℂ) * (q : ℂ) ^ (s + 1) * (1 - (q : ℂ)⁻¹) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  push_cast
  rw [pow_succ]
  field_simp

section KSide

variable (q ℓ : ℕ) (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ)
    (Wq : ℕ → ℕ → ℕ)
    (hq00 : Wq 0 0 = 1) (hq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hqroot : ∀ n : ℕ, Wq (n + 1) 0 = (q + 1) * Wq n 1)
    (hqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + q * Wq n (s + 2))
    (k j : ℕ)
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (univWord (ℓ - 1) k j).support,
        (univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0))

include hq0s hqstep hf in

theorem f_neg (a : ℤ) (s : ℕ) (ha : a < 0) : f a s = 0 := by
  rw [hf]
  apply sum_eq_zero
  intro e he
  split_ifs with h
  · have hlt : e 0 < s := by omega
    rw [W_eq_zero_of_lt q Wq hq0s hqstep (e 0) s hlt]
    simp
  · simp

include hq hℓ hq00 hq0s hqroot hqstep hf in

theorem shellSum_eq_bracket_of_eq (d ρ M : ℕ) (hM : d + ℓ * ρ ≤ M) (g : ℕ → ℂ)
    (hcell : ∀ s : ℕ, s < M → g s =
      if s + 1 ≤ d then f ((ℓ * ρ : ℕ) : ℤ) 0
      else f (((ℓ * ρ : ℕ) : ℤ) - ((s + 1 - d : ℕ) : ℤ)) (2 * (s + 1 - d))) :
    ∑ s ∈ Finset.range M, ((((s + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (s + 1) - (q : ℝ) ^ s) : ℝ) : ℂ) * g s =
      (f ((ℓ * ρ : ℕ) : ℤ) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (q : ℂ) ^ s * (1 - (q : ℂ)⁻¹) +
          ∑ i ∈ Finset.Icc 1 (ℓ * ρ),
            ((d + i : ℕ) : ℂ) * (q : ℂ) ^ (d + i) * (1 - (q : ℂ)⁻¹) * f (((ℓ * ρ : ℕ) : ℤ) - i) (2 * i)) := by
  obtain ⟨E, rfl⟩ : ∃ E, M = d + (ℓ * ρ + E) := ⟨M - d - ℓ * ρ, by omega⟩
  rw [sum_range_add, sum_range_add]
  have h1 : ∀ s ∈ range d, ((((s + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (s + 1) - (q : ℝ) ^ s) : ℝ) : ℂ) * g s =
      f ((ℓ * ρ : ℕ) : ℤ) 0 * (((s + 1 : ℕ) : ℂ) * (q : ℂ) ^ (s + 1) * (1 - (q : ℂ)⁻¹)) := by
    intro s hs
    have hs' : s < d := mem_range.1 hs
    rw [mass_eq q hq, hcell s (by omega), if_pos (by omega)]
    ring
  have h2 : ∀ x ∈ range (ℓ * ρ),
      ((((d + x + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (d + x + 1) - (q : ℝ) ^ (d + x)) : ℝ) : ℂ) * g (d + x) =
      ((d + (x + 1) : ℕ) : ℂ) * (q : ℂ) ^ (d + (x + 1)) * (1 - (q : ℂ)⁻¹) *
        f (((ℓ * ρ : ℕ) : ℤ) - ((x + 1 : ℕ) : ℤ)) (2 * (x + 1)) := by
    intro x hx
    have hx' : x < ℓ * ρ := mem_range.1 hx
    rw [mass_eq q hq, hcell (d + x) (by omega), if_neg (by omega)]
    have e1 : d + x + 1 - d = x + 1 := by omega
    rw [e1]
    rfl
  have h3 : ∀ y ∈ range E,
      ((((d + (ℓ * ρ + y) + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (d + (ℓ * ρ + y) + 1) - (q : ℝ) ^ (d + (ℓ * ρ + y))) : ℝ) : ℂ) * g (d + (ℓ * ρ + y)) = 0 := by
    intro y hy
    have hy' : y < E := mem_range.1 hy
    rw [hcell (d + (ℓ * ρ + y)) (by omega), if_neg (by omega),
      f_neg q ℓ Wq hq0s hqstep k j f hf _ _ (by push_cast; omega), mul_zero]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_congr rfl h3, sum_const_zero, add_zero, ← mul_sum,
    sum_Icc_one_eq_sum_range, sum_Icc_one_eq_sum_range]

include hq hℓ hq00 hq0s hqroot hqstep hf in

theorem shellSum_eq_sum_of_lt (ρa ρb M : ℕ) (hM : ℓ * ρa ≤ M) (g : ℕ → ℂ)
    (hcell : ∀ s : ℕ, s < M → g s = f (((ℓ * ρa : ℕ) : ℤ) - ((s + 1 : ℕ) : ℤ)) (ℓ * (ρb - ρa) + 2 * (s + 1))) :
    ∑ s ∈ Finset.range M, ((((s + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (s + 1) - (q : ℝ) ^ s) : ℝ) : ℂ) * g s =
      ∑ i ∈ Finset.Icc 1 (ℓ * ρa),
          (i : ℂ) * (q : ℂ) ^ i * (1 - (q : ℂ)⁻¹) * f (((ℓ * ρa : ℕ) : ℤ) - i) (ℓ * (ρb - ρa) + 2 * i) := by
  obtain ⟨E, rfl⟩ : ∃ E, M = ℓ * ρa + E := ⟨M - ℓ * ρa, by omega⟩
  rw [sum_range_add]
  have h1 : ∀ s ∈ range (ℓ * ρa), ((((s + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (s + 1) - (q : ℝ) ^ s) : ℝ) : ℂ) * g s =
      ((s + 1 : ℕ) : ℂ) * (q : ℂ) ^ (s + 1) * (1 - (q : ℂ)⁻¹) *
        f (((ℓ * ρa : ℕ) : ℤ) - ((s + 1 : ℕ) : ℤ)) (ℓ * (ρb - ρa) + 2 * (s + 1)) := by
    intro s hs
    have hs' : s < ℓ * ρa := mem_range.1 hs
    rw [mass_eq q hq, hcell s (by omega)]
  have h2 : ∀ y ∈ range E,
      ((((ℓ * ρa + y + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (ℓ * ρa + y + 1) - (q : ℝ) ^ (ℓ * ρa + y)) : ℝ) : ℂ) * g (ℓ * ρa + y) = 0 := by
    intro y hy
    have hy' : y < E := mem_range.1 hy
    rw [hcell (ℓ * ρa + y) (by omega), f_neg q ℓ Wq hq0s hqstep k j f hf _ _ (by push_cast; omega), mul_zero]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_const_zero, add_zero, sum_Icc_one_eq_sum_range]

include hq hℓ hq00 hq0s hqroot hqstep hf in

theorem shellSum_eq_sum_of_gt (ρa ρb M : ℕ) (hM : ℓ * ρb ≤ M) (g : ℕ → ℂ)
    (hcell : ∀ s : ℕ, s < M → g s = f (((ℓ * ρb : ℕ) : ℤ) - ((s + 1 : ℕ) : ℤ)) (ℓ * (ρa - ρb) + 2 * (s + 1))) :
    ∑ s ∈ Finset.range M, ((((s + 1 : ℕ) : ℝ) * ((q : ℝ) ^ (s + 1) - (q : ℝ) ^ s) : ℝ) : ℂ) * g s =
      ∑ i ∈ Finset.Icc 1 (ℓ * ρb),
          (i : ℂ) * (q : ℂ) ^ i * (1 - (q : ℂ)⁻¹) * f (((ℓ * ρb : ℕ) : ℤ) - i) (ℓ * (ρa - ρb) + 2 * i) :=
  shellSum_eq_sum_of_lt q ℓ hq hℓ Wq hq00 hq0s hqroot hqstep k j f hf ρb ρa M hM g hcell

end KSide

end P2mWInertKV.G7

end PieceG7s46

section PieceG8

set_option autoImplicit false

open AutomorphicForm (satakePow)
open AutomorphicForm.SatakeCombination (univWord)
open MvPolynomial Finset

namespace P2mWInertKV
namespace G8

def wt12 : Fin 2 → ℕ := ![1, 2]

theorem weight_wt12 (e : Fin 2 →₀ ℕ) : Finsupp.weight wt12 e = e 0 + 2 * e 1 := by
  simp [wt12, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two]
  ring

theorem isWeightedHomogeneous_sub {φ ψ : MvPolynomial (Fin 2) ℂ} {n : ℕ}
    (hφ : IsWeightedHomogeneous wt12 φ n) (hψ : IsWeightedHomogeneous wt12 ψ n) :
    IsWeightedHomogeneous wt12 (φ - ψ) n := by
  rw [sub_eq_add_neg, show -ψ = C (-1 : ℂ) * ψ by rw [C_neg, C_1, neg_one_mul]]
  exact hφ.add (by simpa using (isWeightedHomogeneous_C wt12 (-1 : ℂ)).mul hψ)

theorem satakePow_isWeightedHomogeneous_aux : ∀ n : ℕ,
    IsWeightedHomogeneous wt12 (satakePow n (X 0 : MvPolynomial (Fin 2) ℂ) (X 1)) n ∧
      IsWeightedHomogeneous wt12 (satakePow (n + 1) (X 0 : MvPolynomial (Fin 2) ℂ) (X 1)) (n + 1)
  | 0 => by
    refine ⟨?_, ?_⟩
    · rw [AutomorphicForm.satakePow_zero, show (2 : MvPolynomial (Fin 2) ℂ) = C 2 from (map_ofNat C 2).symm]
      exact isWeightedHomogeneous_C wt12 (2 : ℂ)
    · rw [AutomorphicForm.satakePow_one]
      exact isWeightedHomogeneous_X ℂ wt12 0
  | n + 1 => by
    obtain ⟨h0, h1⟩ := satakePow_isWeightedHomogeneous_aux n
    refine ⟨h1, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, AutomorphicForm.satakePow_add_two]
    apply isWeightedHomogeneous_sub
    · have h := (isWeightedHomogeneous_X ℂ wt12 0).mul h1
      have e : wt12 0 + (n + 1) = n + 2 := by simp [wt12]; ring
      rwa [e] at h
    · have h := (isWeightedHomogeneous_X ℂ wt12 1).mul h0
      have e : wt12 1 + n = n + 2 := by simp [wt12]; ring
      rwa [e] at h

theorem univWord_isWeightedHomogeneous (L k j : ℕ) :
    IsWeightedHomogeneous wt12 (univWord L k j) ((L + 1) * (k + 2 * j)) := by
  have hp := (satakePow_isWeightedHomogeneous_aux (L + 1)).1
  have hX : IsWeightedHomogeneous wt12 ((X 1 : MvPolynomial (Fin 2) ℂ) ^ (L + 1)) ((L + 1) * 2) := by
    simpa [wt12] using (isWeightedHomogeneous_X ℂ wt12 1).pow (L + 1)
  have h := (hp.pow k).mul (hX.pow j)
  have e : k • (L + 1) + j • ((L + 1) * 2) = (L + 1) * (k + 2 * j) := by simp only [smul_eq_mul]; ring
  rw [univWord, ← e]
  exact h

theorem weight_eq_of_mem_support_univWord (ℓ k j : ℕ) (hℓ : 1 ≤ ℓ) (e : Fin 2 →₀ ℕ)
    (he : e ∈ (univWord (ℓ - 1) k j).support) : e 0 + 2 * e 1 = ℓ * (k + 2 * j) := by
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  rw [Nat.add_sub_cancel] at he
  have h := univWord_isWeightedHomogeneous L k j (mem_support_iff.mp he)
  rwa [weight_wt12] at h

end P2mWInertKV.G8

end PieceG8

namespace P2mWInertKV

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.CubicInduction (diagUnits2)

section Glue

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem units_mul_one_sub (a b : Kvˣ) :
    (a : Kv) * (1 - ((b * a⁻¹ : Kvˣ) : Kv)) = (a : Kv) - b := by
  rw [mul_sub, mul_one, Units.val_mul, mul_left_comm, Units.mul_inv, mul_one]

theorem conj_diagUnits2_eq (a b : Kvˣ) (y : Kv) :
    (unipotentGL2 y)⁻¹ * diagUnits2 a b * unipotentGL2 y =
      diagUnits2 a b * unipotentGL2 ((1 - ((b * a⁻¹ : Kvˣ) : Kv)) * y) := by
  have hinv : (unipotentGL2 y : GL (Fin 2) Kv)⁻¹ = unipotentGL2 (-y) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
  have key : ∀ c : Kv, (a : Kv) * c = (a : Kv) - b →
      unipotentGL2 (-y) * diagUnits2 a b * unipotentGL2 y = diagUnits2 a b * unipotentGL2 (c * y) := by
    intro c hc
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      unipotentGL2_coe, unipotentGL2_coe, unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination (-y) * hc
  rw [hinv]
  exact key _ (units_mul_one_sub K v a b)

theorem norm_one_sub_units_div (a b : Kvˣ) (A B : ℤ) (hAB : A ≠ B)
    (ha : ‖(a : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-A))
    (hb : ‖(b : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-B)) :
    ‖(1 : Kv) - ((b * a⁻¹ : Kvˣ) : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(min A B - A)) := by
  have hN := G4.one_lt_absNorm K v
  have hx : ‖((b * a⁻¹ : Kvˣ) : Kv)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (A - B) :=
    G4.norm_units_div_eq_zpow K v a b A B ha hb
  rw [sub_eq_add_neg]
  rcases lt_or_gt_of_ne hAB with h | h
  · have hlt : ‖-((b * a⁻¹ : Kvˣ) : Kv)‖ < ‖(1 : Kv)‖ := by
      rw [norm_neg, hx, norm_one]; exact zpow_lt_one_of_neg₀ hN (by omega)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt), max_eq_left hlt.le, norm_one,
      min_eq_left h.le, sub_self, neg_zero, zpow_zero]
  · have hgt : ‖(1 : Kv)‖ < ‖-((b * a⁻¹ : Kvˣ) : Kv)‖ := by
      rw [norm_neg, hx, norm_one]; exact one_lt_zpow₀ hN (by omega)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hgt), max_eq_right hgt.le, norm_neg, hx,
      min_eq_right h.le]
    congr 1; ring

end Glue

end P2mWInertKV

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hinert : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = Module.finrank K L)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
      J)

    (ra rb : ℤ) (ha : ‖(a : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((Module.finrank K L : ℤ) * ra)))
    (hb : ‖(b : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-((Module.finrank K L : ℤ) * rb)))
    (d : ℕ) (hd : ra = rb →
      ‖1 - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))

    (Wq : ℕ → ℕ → ℕ) (hWq00 : Wq 0 0 = 1) (hWq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hWqroot : ∀ n : ℕ, Wq (n + 1) 0 = (Ideal.absNorm v.asIdeal + 1) * Wq n 1)
    (hWqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + Ideal.absNorm v.asIdeal * Wq n (s + 2))
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j).support,
        (AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j).coeff e * (Ideal.absNorm v.asIdeal : ℂ) ^ (e 1) / (Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank K L * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0)) :
    J = ((2 * Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) *
      (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          f ((Module.finrank K L : ℤ) * ra) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ s * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) +
            ∑ i ∈ Finset.Icc 1 (Module.finrank K L * ra.toNat),
              ((d + i : ℕ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (d + i) * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) * f ((Module.finrank K L : ℤ) * ra - i) (2 * i)
        else
          ∑ i ∈ Finset.Icc 1 (Module.finrank K L * (min ra rb).toNat),
            (i : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ i * (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹) *
              f ((Module.finrank K L : ℤ) * min ra rb - i) (Module.finrank K L * (ra - rb).natAbs + 2 * i))
      else 0) := by
  classical

  have hℓ : 1 ≤ Module.finrank K L := Module.finrank_pos
  have hℓpos : (0 : ℤ) < (Module.finrank K L : ℤ) := by exact_mod_cast Module.finrank_pos
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := P2mWInertKV.G4.one_lt_absNorm K v
  have hq : 1 ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast hq1.le
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one hq1

  have hNw : Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm v.asIdeal ^ Module.finrank K L := by
    haveI : (ws v).1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal (ws v).2).symm⟩
    rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver (ws v).1.asIdeal v.asIdeal v.isPrime v.ne_bot, hinert]
  have hslotWord : AutomorphicForm.SatakeCombination.slotWord K L ws v k j =
      AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j := by
    simp only [AutomorphicForm.SatakeCombination.slotWord, AutomorphicForm.SatakeCombination.slotDeg, hinert]
  have hslotCoeff : ∀ r : Fin 2 →₀ ℕ, AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j r =
      (AutomorphicForm.SatakeCombination.univWord (Module.finrank K L - 1) k j).coeff r *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm v.asIdeal : ℂ) ^ (Module.finrank K L * j) := by
    intro r
    simp only [AutomorphicForm.SatakeCombination.slotCoeff, hslotWord, hNw, Nat.cast_pow, pow_mul]

  set fK : GL (Fin 2) (v.adicCompletion K) → ℂ := fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (AutomorphicForm.SatakeCombination.slotWord K L ws v k j).support,
          AutomorphicForm.SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x) with hfK
  have hfKm : Measurable[AutomorphicForm.localGLBorel K v] fK :=
    P2mWInertKV.G7.fK_measurable K v _ _ nK rK zK
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖fK g‖ ≤ C := P2mWInertKV.G7.fK_bounded K v _ _ nK rK zK
  have hfKK : ∀ g k₁ k₂ : GL (Fin 2) (v.adicCompletion K),
      k₁ ∈ AutomorphicForm.localIntegralSet K v → k₂ ∈ AutomorphicForm.localIntegralSet K v →
        fK (k₁ * g * k₂) = fK g := by
    intro g k₁ k₂ hk₁ hk₂
    simp only [hfK]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [P2mWInertKV.heckeWord_biInvariant K v hϖK0 nK rK hrK zK hzK (e 0) (e 1) g k₁ k₂ hk₁ hk₂]
  obtain ⟨M0, hM0⟩ := P2mWInertKV.G7.fK_support_bound K v _ _ nK rK zK fK hfK a b hab
  set M : ℕ := M0 + (d + Module.finrank K L * ra.toNat + Module.finrank K L * rb.toNat) with hMdef
  have hM : ∀ y : v.adicCompletion K,
      fK ((AutomorphicForm.unipotentGL2 y)⁻¹ * diagUnits2 a b * AutomorphicForm.unipotentGL2 y) ≠ 0 →
        ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ M := fun y hy =>
    (hM0 y hy).trans (pow_le_pow_right₀ hq1.le (by omega))

  have hϖ0' : ((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := hϖK0
  have hϖn : ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    rw [P2mWInertKV.G4.norm_eq_zpow_log K v hϖ0', P2mWInertKV.G4.valued_uniformiser K v hϖK, WithZero.log_exp,
      zpow_neg, zpow_one]

  have hJK := AutomorphicForm.eq_two_mul_log_mul_sum_of_isWeightedOrbitalIntegral_diagUnits2_of_biInvariant
    K v a b hab τ hτ hτ1 fK hfKm C hC hfKK _ hϖn M hM J hJ
  rw [hJK]
  congr 1

  have hc0 : (1 : v.adicCompletion K) - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := by
    intro h
    apply hab
    have h1 : ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := (sub_eq_zero.1 h).symm
    exact (mul_inv_eq_one.1 (Units.val_eq_one.1 h1)).symm
  obtain ⟨σ0, hσ0⟩ : ∃ σ0 : ℤ, ‖(1 : v.adicCompletion K) - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ0) :=
    (P2mWInertKV.G4.eq_zero_or_exists_norm_eq_zpow K v _).resolve_left hc0
  have hy : ∀ s : ℕ, ‖(((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K))⁻¹ ^ (s + 1)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (s + 1) := by
    intro s; rw [norm_pow, norm_inv, hϖn, inv_inv]
  have ht : ∀ s : ℕ, ‖((1 : v.adicCompletion K) - ((b * a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) *
      (((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K))⁻¹ ^ (s + 1)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(σ0 - ((s : ℤ) + 1))) := by
    intro s
    rw [norm_mul, hσ0, hy, ← zpow_natCast, ← zpow_add₀ hq0.ne']
    congr 1; push_cast; ring

  have hval : ∀ s : ℕ,
      fK ((AutomorphicForm.unipotentGL2 ((((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K))⁻¹ ^ (s + 1)))⁻¹ *
          diagUnits2 a b *
          AutomorphicForm.unipotentGL2 ((((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K))⁻¹ ^ (s + 1))) =
        f (min (min ((Module.finrank K L : ℤ) * ra) ((Module.finrank K L : ℤ) * rb))
              ((Module.finrank K L : ℤ) * ra + (σ0 - ((s : ℤ) + 1))))
          ((Module.finrank K L : ℤ) * ra + (Module.finrank K L : ℤ) * rb -
            2 * min (min ((Module.finrank K L : ℤ) * ra) ((Module.finrank K L : ℤ) * rb))
              ((Module.finrank K L : ℤ) * ra + (σ0 - ((s : ℤ) + 1)))).natAbs := by
    intro s
    rw [P2mWInertKV.conj_diagUnits2_eq K v]
    simp only [hfK]
    rw [hf, hslotWord]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [P2mWInertKV.G4.sum_indicator_heckeWord_diagUnits2_mul_unipotentGL2_of_norm_eq K v ϖK hϖK hϖK0 nK rK hrK zK hzK
      Wq hWq00 hWq0s hWqroot hWqstep (e 0) (e 1) a b _ _ ha hb _ _ (ht s), hslotCoeff]
    have hnn : 0 ≤ (Module.finrank K L : ℤ) * ra + (Module.finrank K L : ℤ) * rb -
        2 * min (min ((Module.finrank K L : ℤ) * ra) ((Module.finrank K L : ℤ) * rb))
          ((Module.finrank K L : ℤ) * ra + (σ0 - ((s : ℤ) + 1))) := by omega
    rw [Int.natAbs_of_nonneg hnn]
    by_cases hc : (Module.finrank K L : ℤ) * ra + (Module.finrank K L : ℤ) * rb = ((e 0 : ℕ) : ℤ) + 2 * ((e 1 : ℕ) : ℤ)
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc, if_neg (by omega), Nat.cast_zero]
  simp only [hval]

  have f_off : ¬ ra + rb = (k : ℤ) + 2 * j → ∀ (a' : ℤ) (sd : ℕ),
      2 * a' + sd = (Module.finrank K L : ℤ) * ra + (Module.finrank K L : ℤ) * rb → f a' sd = 0 := by
    intro hdet a' sd hsum
    rw [hf]
    refine Finset.sum_eq_zero fun e he => ?_
    have hw := P2mWInertKV.G8.weight_eq_of_mem_support_univWord (Module.finrank K L) k j hℓ e he
    have hw' : ((e 0 : ℕ) : ℤ) + 2 * ((e 1 : ℕ) : ℤ) = (Module.finrank K L : ℤ) * ((k : ℤ) + 2 * (j : ℤ)) := by
      exact_mod_cast hw
    rw [if_neg, mul_zero]
    intro hcond
    apply hdet
    have h1 : (Module.finrank K L : ℤ) * (ra + rb) = (Module.finrank K L : ℤ) * ((k : ℤ) + 2 * j) := by
      linear_combination (-1 : ℤ) * hsum + hcond + hw'
    exact mul_left_cancel₀ hℓpos.ne' h1
  by_cases hdet : ra + rb = (k : ℤ) + 2 * j
  · rw [if_pos hdet]
    by_cases heq : ra = rb
    ·
      rw [if_pos heq]
      have hra0 : 0 ≤ ra := by omega
      obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, ra = ρ := ⟨ra.toNat, (Int.toNat_of_nonneg hra0).symm⟩
      have hσd : σ0 = d := by
        have h1 := hσ0.symm.trans (hd heq)
        have := zpow_right_injective₀ hq0 hq1.ne' h1
        omega
      subst σ0
      have hrb : rb = ρ := heq ▸ hρ
      subst ra rb
      have hMle : d + Module.finrank K L * ρ ≤ M := by
        simp only [hMdef, Int.toNat_natCast]; omega
      have hN : (Module.finrank K L : ℤ) * (ρ : ℤ) = ((Module.finrank K L * ρ : ℕ) : ℤ) := by push_cast; ring
      refine (P2mWInertKV.G7.shellSum_eq_bracket_of_eq (Ideal.absNorm v.asIdeal) (Module.finrank K L) hq hℓ
        Wq hWq00 hWq0s hWqroot hWqstep k j f hf d ρ M hMle _ ?_).trans ?_
      · intro s _
        simp only [hN]
        split_ifs with h
        · congr 1 <;> omega
        · congr 1 <;> omega
      · simp only [Int.toNat_natCast, hN]
    ·
      rw [if_neg heq]
      have hAB : (Module.finrank K L : ℤ) * ra ≠ (Module.finrank K L : ℤ) * rb := fun h =>
        heq (mul_left_cancel₀ hℓpos.ne' h)
      have hσ : σ0 = min ((Module.finrank K L : ℤ) * ra) ((Module.finrank K L : ℤ) * rb) - (Module.finrank K L : ℤ) * ra := by
        have h1 := hσ0.symm.trans (P2mWInertKV.norm_one_sub_units_div K v a b _ _ hAB ha hb)
        have := zpow_right_injective₀ hq0 hq1.ne' h1
        omega
      subst σ0
      by_cases hneg : min ra rb < 0
      ·
        have hmin : min ((Module.finrank K L : ℤ) * ra) ((Module.finrank K L : ℤ) * rb) < 0 := by
          rcases le_total ra rb with h | h
          · rw [min_eq_left h] at hneg
            exact lt_of_le_of_lt (min_le_left _ _) (mul_neg_of_pos_of_neg hℓpos hneg)
          · rw [min_eq_right h] at hneg
            exact lt_of_le_of_lt (min_le_right _ _) (mul_neg_of_pos_of_neg hℓpos hneg)
        rw [Int.toNat_eq_zero.mpr hneg.le, mul_zero, Finset.Icc_eq_empty_of_lt Nat.one_pos, Finset.sum_empty]
        refine Finset.sum_eq_zero fun s _ => ?_
        rw [P2mWInertKV.G7.f_neg (Ideal.absNorm v.asIdeal) (Module.finrank K L) Wq hWq0s hWqstep k j f hf _ _
          (by omega), mul_zero]
      · rw [not_lt] at hneg
        have hra0 : 0 ≤ ra := le_trans hneg (min_le_left _ _)
        have hrb0 : 0 ≤ rb := le_trans hneg (min_le_right _ _)
        obtain ⟨ρa, hρa⟩ : ∃ ρ : ℕ, ra = ρ := ⟨ra.toNat, (Int.toNat_of_nonneg hra0).symm⟩
        obtain ⟨ρb, hρb⟩ : ∃ ρ : ℕ, rb = ρ := ⟨rb.toNat, (Int.toNat_of_nonneg hrb0).symm⟩
        subst ra rb
        have hNa : (Module.finrank K L : ℤ) * (ρa : ℤ) = ((Module.finrank K L * ρa : ℕ) : ℤ) := by push_cast; ring
        have hNb : (Module.finrank K L : ℤ) * (ρb : ℤ) = ((Module.finrank K L * ρb : ℕ) : ℤ) := by push_cast; ring
        have hne : ρa ≠ ρb := fun h => heq (by rw [h])
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : Module.finrank K L * ρa ≤ Module.finrank K L * ρb := Nat.mul_le_mul_left _ hlt.le
          have hsub : Module.finrank K L * (ρb - ρa) = Module.finrank K L * ρb - Module.finrank K L * ρa :=
            Nat.mul_sub _ _ _
          have hMle : Module.finrank K L * ρa ≤ M := by
            simp only [hMdef, Int.toNat_natCast]; omega
          have hmin : min (ρa : ℤ) (ρb : ℤ) = ρa := min_eq_left (by exact_mod_cast hlt.le)
          have habs : ((ρa : ℤ) - (ρb : ℤ)).natAbs = ρb - ρa := by omega
          rw [hmin, habs, Int.toNat_natCast]
          refine (P2mWInertKV.G7.shellSum_eq_sum_of_lt (Ideal.absNorm v.asIdeal) (Module.finrank K L) hq hℓ
            Wq hWq00 hWq0s hWqroot hWqstep k j f hf ρa ρb M hMle _ ?_).trans ?_
          · intro s _
            simp only [hNa, hNb]
            rw [hsub]
            congr 1 <;> omega
          · simp only [hNa]
        · have hle : Module.finrank K L * ρb ≤ Module.finrank K L * ρa := Nat.mul_le_mul_left _ hgt.le
          have hsub : Module.finrank K L * (ρa - ρb) = Module.finrank K L * ρa - Module.finrank K L * ρb :=
            Nat.mul_sub _ _ _
          have hMle : Module.finrank K L * ρb ≤ M := by
            simp only [hMdef, Int.toNat_natCast]; omega
          have hmin : min (ρa : ℤ) (ρb : ℤ) = ρb := min_eq_right (by exact_mod_cast hgt.le)
          have habs : ((ρa : ℤ) - (ρb : ℤ)).natAbs = ρa - ρb := by omega
          rw [hmin, habs, Int.toNat_natCast]
          refine (P2mWInertKV.G7.shellSum_eq_sum_of_gt (Ideal.absNorm v.asIdeal) (Module.finrank K L) hq hℓ
            Wq hWq00 hWq0s hWqroot hWqstep k j f hf ρa ρb M hMle _ ?_).trans ?_
          · intro s _
            simp only [hNa, hNb]
            rw [hsub]
            congr 1 <;> omega
          · simp only [hNb]
  ·
    rw [if_neg hdet]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [f_off hdet _ _ (by omega), mul_zero]

end S_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord
end P2MW
export P2MW.S_AutomorphicForm_eq_two_mul_log_mul_shellValue_of_isWeightedOrbitalIntegral_baseChange_heckeWord (solution)
