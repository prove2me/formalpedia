-- Prove2me | solution 1 for AutomorphicForm.exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4a95b8e2-28fc-5d90-95ae-6bc590c8ecd0

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_IdeleBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

section RINHFold_JE2aFlatLocal

set_option autoImplicit false

noncomputable section

open NumberField.AdelicHeight

namespace P6B
namespace JE2aFlat

section Local

variable {K : Type*} [NormedField K]

private theorem _root_.P6B.JE2aFlat.coe_mul (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

p2m_export "P6B.JE2aFlat" "coe_mul"

theorem upper_mul_apply_one {s : GL (Fin 2) K} (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (g : GL (Fin 2) K) (j : Fin 2) :
    ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j
      = (s : Matrix (Fin 2) (Fin 2) K) 1 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h10, zero_mul, zero_add]

theorem rowMaxNorm_upper_mul {s : GL (Fin 2) K} (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖(s : Matrix (Fin 2) (Fin 2) K) 1 1‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowMaxNorm
  rw [upper_mul_apply_one h10 g 0, upper_mul_apply_one h10 g 1, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg _)]

theorem finLocalHeight_upper_entries_mul {s : GL (Fin 2) K} {a t : K} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = ‖a‖ / ‖t‖ * finLocalHeight g := by
  have ht0 : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  have hr0 : (0 : ℝ) < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := rowMaxNorm_pos g
  unfold finLocalHeight
  rw [AutomorphicForm.SiegelCoordinates.det_upper_entries_mul h00 h10 h11 g,
    rowMaxNorm_upper_mul h10 g, h11, norm_mul, norm_mul, mul_pow]
  field_simp

variable [IsUltrametricDist K]

theorem rowMaxNorm_mul_le (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hentry : ∀ j : Fin 2,
      ‖((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j‖
        ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    intro j
    rw [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (hentry 0) (hentry 1)

theorem rowMaxNorm_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  refine le_antisymm (rowMaxNorm_mul_le g k hk) ?_
  have h := rowMaxNorm_mul_le (g * k) k⁻¹ hk'
  rwa [mul_inv_cancel_right] at h

theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← coe_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
  rw [hprod] at this
  exact lt_irrefl _ this

theorem finLocalHeight_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_mul_integral g k hk hk', coe_mul, Matrix.det_mul, norm_mul,
    norm_det_eq_one_of_integral k hk hk', mul_one]

end Local

end P6B.JE2aFlat

end

end RINHFold_JE2aFlatLocal

section RINHFold_JE2aFlatAdelic

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

namespace P6B
namespace JE2aFlat

variable (F : Type) [Field F] [NumberField F]

def placeModulus (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  (∏ w : InfinitePlace F, ‖(x : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult)
    * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : AdeleRing (𝓞 F) F).2 v‖

variable {F}

theorem finComp_mul_finComp_inv (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : ((x : AdeleRing (𝓞 F) F) * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v = 1 := by
    rw [x.mul_inv]; rfl
  exact h

theorem finComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  intro h0
  have h := finComp_mul_finComp_inv x v
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem archComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (x : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h0
  have h : ((x : AdeleRing (𝓞 F) F) * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 w = 1 := by
    rw [x.mul_inv]; rfl
  rw [show ((x : AdeleRing (𝓞 F) F) * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 w
      = (x : AdeleRing (𝓞 F) F).1 w * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      from rfl, h0, zero_mul] at h
  exact zero_ne_one h

theorem norm_finComp_eventually_eq_one (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ‖(x : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have hx := ((x : AdeleRing (𝓞 F) F).2).2
  have hx' := (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  filter_upwards [hx, hx'] with v hv hv'
  have h1 : ‖(x : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 := norm_le_one_of_mem_adicCompletionIntegers hv
  have h2 : ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    norm_le_one_of_mem_adicCompletionIntegers hv'
  have hprod : ‖(x : AdeleRing (𝓞 F) F).2 v‖
      * ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, finComp_mul_finComp_inv, norm_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

theorem hasFiniteMulSupport_norm_finComp (x : (AdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖(x : AdeleRing (𝓞 F) F).2 v‖).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (norm_finComp_eventually_eq_one x)

theorem placeModulus_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < placeModulus F x := by
  unfold placeModulus
  refine mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (archComp_ne_zero x w)) _) ?_
  exact finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos)
    fun v => norm_pos_iff.mpr (finComp_ne_zero x v)

theorem finHeight_upper_mul (s g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (h10 : (s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0)
    (ht : ∀ v : HeightOneSpectrum (𝓞 F),
      (s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v ≠ 0) :
    finHeight F (s * g)
      = (∏ᶠ v : HeightOneSpectrum (𝓞 F),
          ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 v‖
            / ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v‖)
        * finHeight F g := by

  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      finLocalHeight (finComponent (𝓞 F) F v (s * g))
        = ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 v‖
            / ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v‖
          * finLocalHeight (finComponent (𝓞 F) F v g) := by
    intro v
    rw [map_mul]
    exact finLocalHeight_upper_entries_mul (ht v) (finComponent_apply _ _ v s 0 0)
      (by rw [finComponent_apply, h10]; rfl) (finComponent_apply _ _ v s 1 1) _
  have hg := hasFiniteMulSupport_finLocalHeight g
  have hsg := hasFiniteMulSupport_finLocalHeight (s * g)

  have hc : (fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 v‖
        / ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v‖).HasFiniteMulSupport := by
    refine (hsg.union hg).subset fun v hv => ?_
    by_contra hv'
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hv'
    have := hloc v
    rw [hv'.1, hv'.2, mul_one] at this
    exact hv this.symm
  unfold finHeight
  rw [← finprod_mul_distrib hc hg]
  exact finprod_congr hloc

theorem archHeight_upper_mul (s g : GL (Fin 2) (InfiniteAdeleRing F))
    (h10 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0)
    (ht : ∀ w : InfinitePlace F, (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 w ≠ 0) :
    archHeight F (s * g)
      = (∏ w : InfinitePlace F,
          (‖(s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0 w‖
            / ‖(s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 w‖) ^ w.mult)
        * archHeight F g := by
  unfold archHeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_mul, localHeight_upper_entries_mul (ht w) (archComponent_apply F w s 0 0)
    (by rw [archComponent_apply, h10]; rfl) (archComponent_apply F w s 1 1) _, mul_pow]

theorem adelicHeight_borel_mul (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (b * g)
      = placeModulus F (borelDiagFst ⟨b, hb⟩) / placeModulus F (borelDiagSnd ⟨b, hb⟩)
        * adelicHeight F g := by
  have h10 : ((b : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0
      = 0 := hb

  set x : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst ⟨b, hb⟩ with hx
  set y : (AdeleRing (𝓞 F) F)ˣ := borelDiagSnd ⟨b, hb⟩ with hy
  have hx0 : (x : AdeleRing (𝓞 F) F)
      = ((b : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 := rfl
  have hy0 : (y : AdeleRing (𝓞 F) F)
      = ((b : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 := rfl

  have hfin := finHeight_upper_mul (glFin (𝓞 F) F b) (glFin (𝓞 F) F g)
    (by rw [glFin_apply, h10]; rfl) (fun v => by rw [glFin_apply, ← hy0]; exact finComp_ne_zero y v)

  have harch := archHeight_upper_mul (glArch (𝓞 F) F b) (glArch (𝓞 F) F g)
    (by rw [glArch_apply, h10]; rfl) (fun w => by rw [glArch_apply, ← hy0]; exact archComp_ne_zero y w)
  unfold adelicHeight
  rw [map_mul, map_mul, hfin, harch]
  simp only [glFin_apply, glArch_apply, ← hx0, ← hy0]
  have hy1 : ∀ w : InfinitePlace F, ‖(y : AdeleRing (𝓞 F) F).1 w‖ ≠ 0 :=
    fun w => norm_ne_zero_iff.mpr (archComp_ne_zero y w)
  have hy2 : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : AdeleRing (𝓞 F) F).2 v‖) ≠ 0 :=
    (finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos)
      fun v => norm_pos_iff.mpr (finComp_ne_zero y v)).ne'
  unfold placeModulus
  rw [finprod_div_distrib (hasFiniteMulSupport_norm_finComp x) (hasFiniteMulSupport_norm_finComp y),
    ]
  simp only [div_pow]
  rw [Finset.prod_div_distrib]
  have hA : (∏ w : InfinitePlace F, ‖(y : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (hy1 w)
  field_simp

theorem finHeight_mul_integral (g k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) :
    finHeight F (g * k) = finHeight F g := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_integral _ _ (hk v) fun i j => ?_
  rw [← map_inv]
  exact hk' v i j

theorem adelicHeight_mul_of_integral_of_rowIsometry (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v (glFin (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖
        ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v (glFin (𝓞 F) F k)⁻¹ :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hka : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    adelicHeight F (g * k) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_mul_rowIsometry F _ hka, finHeight_mul_integral _ _ hk hk']

end P6B.JE2aFlat

end

end RINHFold_JE2aFlatAdelic

section RINHFold_JE2aFlatFamily

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

namespace P6B
namespace JE2aFlat

section HeightOne

variable {K : Type*} [NormedField K]

theorem finLocalHeight_one : finLocalHeight (1 : GL (Fin 2) K) = 1 := by
  unfold finLocalHeight rowMaxNorm
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, Matrix.det_one,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq, norm_one, norm_zero,
    max_eq_right zero_le_one]
  norm_num

end HeightOne

variable (F : Type) [Field F] [NumberField F]

theorem finHeight_one : finHeight F 1 = 1 := by
  unfold finHeight
  simp only [map_one, finLocalHeight_one, finprod_one]

theorem adelicHeight_one : adelicHeight F 1 = 1 := by
  unfold adelicHeight
  rw [map_one, map_one, archHeight_one, finHeight_one, mul_one]

def flatOne (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)

theorem flatOne_apply_one (s : ℂ) : flatOne F s 1 = 1 := by
  unfold flatOne
  rw [adelicHeight_one, Complex.ofReal_one, Complex.one_cpow]

variable {F}

theorem flatOne_ne_zero (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : flatOne F s g ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (adelicHeight_pos g).ne'))

theorem flatOne_eq_exp (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    flatOne F s g = Complex.exp ((Real.log (adelicHeight F g) : ℂ) * (s + 1 / 2)) := by
  unfold flatOne
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (adelicHeight_pos g).ne'),
    Complex.ofReal_log (adelicHeight_pos g).le]

theorem differentiable_flatOne (g : AdelicGL2 (𝓞 F) F) : Differentiable ℂ fun s => flatOne F s g := by
  have h : (fun s => flatOne F s g)
      = fun s => Complex.exp ((Real.log (adelicHeight F g) : ℂ) * (s + 1 / 2)) :=
    funext fun s => flatOne_eq_exp s g
  rw [h]
  fun_prop

theorem continuous_flatOne_uncurry (hH : Continuous (adelicHeight F)) :
    Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => flatOne F p.1 p.2 := by
  have h : (fun p : ℂ × AdelicGL2 (𝓞 F) F => flatOne F p.1 p.2)
      = fun p => Complex.exp ((Real.log (adelicHeight F p.2) : ℂ) * (p.1 + 1 / 2)) :=
    funext fun p => flatOne_eq_exp p.1 p.2
  rw [h]
  have hlog : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => Real.log (adelicHeight F p.2) :=
    (hH.comp continuous_snd).log fun p => (adelicHeight_pos p.2).ne'
  fun_prop

theorem continuous_flatOne (hH : Continuous (adelicHeight F)) (s : ℂ) : Continuous (flatOne F s) := by
  have h : flatOne F s = fun g => Complex.exp ((Real.log (adelicHeight F g) : ℂ) * (s + 1 / 2)) :=
    funext fun g => flatOne_eq_exp s g
  rw [h]
  have hlog : Continuous fun g : AdelicGL2 (𝓞 F) F => Real.log (adelicHeight F g) :=
    hH.log fun g => (adelicHeight_pos g).ne'
  fun_prop

theorem adelicHeight_mul_adelicArchGLInclAt (w : InfinitePlace F)
    (k : rowIsometrySubgroup w.Completion) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, show adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)
      = adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion)) from rfl,
    glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, mul_one,
    archHeight_mul_rowIsometry F _ (fun v => ?_)]
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_archGLIncl_self]
    exact k.2
  · rw [archComponent_archGLIncl_of_ne F hvw]
    exact isRowIsometry_one

theorem flatOne_mul_adelicArchGLInclAt (s : ℂ) (w : InfinitePlace F)
    (k : rowIsometrySubgroup w.Completion) (g : AdelicGL2 (𝓞 F) F) :
    flatOne F s (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) = flatOne F s g := by
  unfold flatOne
  rw [adelicHeight_mul_adelicArchGLInclAt]

theorem hasArchType_flatOne (s : ℂ) : HasArchType F (fun _ => 1) (flatOne F s) := by
  intro w k g
  rw [flatOne_mul_adelicArchGLInclAt, MonoidHom.one_apply, Units.val_one, one_mul]

theorem isArchKFinite_flatOne (s : ℂ) : IsArchKFinite F (flatOne F s) :=
  isArchKFinite_of_hasArchType F _ _ (hasArchType_flatOne s)

theorem ofReal_div_mul_cpow {a c h : ℝ} (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) (z : ℂ) :
    (((a / c * h : ℝ)) : ℂ) ^ z = ((a : ℂ) ^ z) * ((c : ℂ) ^ (-z)) * ((h : ℂ) ^ z) := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg ha.le (inv_nonneg.mpr hc.le)) hh.le, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hc.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hc.le]
  exact Real.pi_ne_zero.symm

theorem isInducedSection_flatOne (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαmod : ∀ x, ((α x : ℝˣ) : ℝ) = placeModulus F x) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (flatOne F s) := by
  intro b hb g
  unfold flatOne
  rw [adelicHeight_borel_mul b hb g,
    ofReal_div_mul_cpow (placeModulus_pos _) (placeModulus_pos _) (adelicHeight_pos g)]
  simp only [etaFst, etaSnd, MonoidHom.mul_apply, MonoidHom.one_apply, one_mul, cpowChar_apply_val, hαmod]

end P6B.JE2aFlat

end

end RINHFold_JE2aFlatFamily

noncomputable section

namespace RS11SC

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain Matrix

open scoped NNReal Classical

variable {K : Type} [Field K] [NumberField K]

def πv (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)

theorem πv_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) : πv v x = x.2 v := rfl

theorem continuous_πv (v : HeightOneSpectrum (𝓞 K)) : Continuous (πv (K := K) v) :=
  (continuous_finAdeleEval (𝓞 K) K v).comp (continuous_adeleFin (𝓞 K) K)

def ent (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  πv v ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)

theorem ent_eq (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ent g i j v = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := rfl

theorem continuous_ent (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun g : AdelicGL2 (𝓞 K) K => ent g i j v :=
  (continuous_πv v).comp (Units.continuous_val.matrix_elem i j)

theorem ent_mul (g h : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ent (g * h) i j v = ent g i 0 v * ent h 0 j v + ent g i 1 v * ent h 1 j v := by
  simp only [ent, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]

theorem ent_one (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ent (1 : AdelicGL2 (𝓞 K) K) i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  simp only [ent, Matrix.GeneralLinearGroup.coe_one]
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

theorem ent_one_ne_zero (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ent g 1 0 v ≠ 0 ∨ ent g 1 1 v ≠ 0 := by
  by_contra h
  push Not at h
  have hdet : IsUnit ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) := g.isUnit.map Matrix.detMonoidHom
  have h2 := hdet.map (πv v)
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at h2
  change IsUnit (ent g 0 0 v * ent g 1 1 v - ent g 0 1 v * ent g 1 0 v) at h2
  rw [h.1, h.2, mul_zero, mul_zero, sub_zero] at h2
  exact not_isUnit_zero h2

def eps (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) : WithZero (Multiplicative ℤ) :=
  ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

theorem eps_ne_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) : eps n v ≠ 0 :=
  WithZero.coe_ne_zero

theorem eps_le_one (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) : eps n v ≤ 1 := by
  rw [eps, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
  omega

theorem eps_lt_one {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} (hn : 0 < n v) :
    eps n v < 1 := by
  rw [eps, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  omega

theorem exists_valued_eq_eps (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = eps n v :=
  exists_valued_eq_exp_neg (K := K) v (n v)

abbrev CondAt (n : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : Prop :=
  Valued.v (ent g 1 0 v) ≤ Valued.v (ent g 1 1 v) * eps n v

theorem condAt_borel_mul_imp {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) {g : AdelicGL2 (𝓞 K) K} (h : CondAt n v g) :
    CondAt n v (b * g) := by
  have h10 : ent b 1 0 v = 0 := by
    have : ((b : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hb
    rw [ent, this, map_zero]
  unfold CondAt at h ⊢
  rw [ent_mul, ent_mul, h10, zero_mul, zero_add, zero_mul, zero_add, map_mul, map_mul, mul_assoc]
  exact mul_le_mul_right h _

theorem condAt_borel_mul_iff {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    CondAt n v (b * g) ↔ CondAt n v g := by
  refine ⟨fun h => ?_, condAt_borel_mul_imp hb⟩
  have := condAt_borel_mul_imp (inv_mem hb) h
  rwa [inv_mul_cancel_left] at this

theorem condAt_mul_of_cong {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} (hn : 0 < n v)
    {g k : AdelicGL2 (𝓞 K) K}
    (hint : ∀ i j, Valued.v (ent k i j v) ≤ 1)
    (hcong : ∀ i j, Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ eps n v)
    (h : CondAt n v g) : CondAt n v (g * k) := by
  unfold CondAt at h ⊢
  rw [ent_mul, ent_mul]
  set c := ent g 1 0 v with hc
  set d := ent g 1 1 v with hd
  have hε1 : eps n v < 1 := eps_lt_one hn

  have hk11 : Valued.v (ent k 1 1 v) = 1 := by
    have h1 := hcong 1 1
    rw [Matrix.one_apply_eq] at h1
    have hlt1 : Valued.v (ent k 1 1 v - 1) < Valued.v (1 : v.adicCompletion K) := by
      rw [Valuation.map_one]; exact lt_of_le_of_lt h1 hε1
    rw [← (Valuation.map_one Valued.v : Valued.v (1 : v.adicCompletion K) = 1)]
    exact Valuation.map_eq_of_sub_lt _ hlt1
  have hk10 : Valued.v (ent k 1 0 v) ≤ eps n v := by
    have h1 := hcong 1 0
    rwa [Matrix.one_apply_ne (by decide), sub_zero] at h1
  have hk01 : Valued.v (ent k 0 1 v) ≤ eps n v := by
    have h1 := hcong 0 1
    rwa [Matrix.one_apply_ne (by decide), sub_zero] at h1

  by_cases hd0 : Valued.v d = 0
  · have hc0 : Valued.v c = 0 := le_antisymm (by rw [hd0, zero_mul] at h; exact h) zero_le'
    rw [(Valuation.zero_iff Valued.v).mp hc0, (Valuation.zero_iff Valued.v).mp hd0]
    simp
  · have hdnew : Valued.v (c * ent k 0 1 v + d * ent k 1 1 v) = Valued.v d := by
      have hlt : Valued.v (c * ent k 0 1 v) < Valued.v (d * ent k 1 1 v) := by
        rw [map_mul, map_mul, hk11, mul_one]
        calc Valued.v c * Valued.v (ent k 0 1 v) ≤ Valued.v d * eps n v * eps n v :=
              mul_le_mul' h hk01
          _ < Valued.v d := by
              rw [mul_assoc]
              calc Valued.v d * (eps n v * eps n v) < Valued.v d * 1 := by
                    apply mul_lt_mul_of_pos_left _ (zero_lt_iff.mpr hd0)
                    calc eps n v * eps n v ≤ eps n v * 1 := mul_le_mul_right (eps_le_one n v) _
                      _ = eps n v := mul_one _
                      _ < 1 := hε1
                _ = Valued.v d := mul_one _
      rw [Valuation.map_add_eq_of_lt_right _ hlt, map_mul, hk11, mul_one]
    rw [hdnew]
    calc Valued.v (c * ent k 0 0 v + d * ent k 1 0 v)
        ≤ max (Valued.v (c * ent k 0 0 v)) (Valued.v (d * ent k 1 0 v)) := Valuation.map_add Valued.v _ _
      _ ≤ Valued.v d * eps n v := by
          apply max_le
          · rw [map_mul]
            calc Valued.v c * Valued.v (ent k 0 0 v) ≤ Valued.v d * eps n v * 1 := mul_le_mul' h (hint 0 0)
              _ = Valued.v d * eps n v := mul_one _
          · rw [map_mul]
            exact mul_le_mul_right hk10 _

theorem cong_inv {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} {k : AdelicGL2 (𝓞 K) K}
    (hint' : ∀ i j, Valued.v (ent k⁻¹ i j v) ≤ 1)
    (hcong : ∀ i j, Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ eps n v) :
    ∀ i j, Valued.v (ent k⁻¹ i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ eps n v := by
  intro i j

  have key : ent k⁻¹ i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      -(ent k⁻¹ i 0 v * (ent k 0 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 j) +
        ent k⁻¹ i 1 v * (ent k 1 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 j)) := by
    have h1 : ent (k⁻¹ * k) i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
      rw [inv_mul_cancel, ent_one]
    rw [ent_mul] at h1
    have h2 : ent (k⁻¹ * 1) i j v = ent k⁻¹ i j v := by rw [mul_one]
    rw [ent_mul, ent_one, ent_one] at h2
    linear_combination h1 - h2
  rw [key, Valuation.map_neg]
  calc Valued.v (ent k⁻¹ i 0 v * (ent k 0 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 j) +
        ent k⁻¹ i 1 v * (ent k 1 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 j))
      ≤ max (Valued.v (ent k⁻¹ i 0 v * (ent k 0 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 j)))
          (Valued.v (ent k⁻¹ i 1 v * (ent k 1 j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 j))) :=
        Valuation.map_add Valued.v _ _
    _ ≤ eps n v := by
        apply max_le <;> rw [map_mul]
        · calc _ ≤ 1 * eps n v := mul_le_mul' (hint' i 0) (hcong 0 j)
            _ = eps n v := one_mul _
        · calc _ ≤ 1 * eps n v := mul_le_mul' (hint' i 1) (hcong 1 j)
            _ = eps n v := one_mul _

theorem condAt_mul_iff_of_cong {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} (hn : 0 < n v)
    (g : AdelicGL2 (𝓞 K) K) {k : AdelicGL2 (𝓞 K) K}
    (hint : ∀ i j, Valued.v (ent k i j v) ≤ 1) (hint' : ∀ i j, Valued.v (ent k⁻¹ i j v) ≤ 1)
    (hcong : ∀ i j, Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ eps n v) :
    CondAt n v (g * k) ↔ CondAt n v g := by
  refine ⟨fun h => ?_, condAt_mul_of_cong hn hint hcong⟩
  have := condAt_mul_of_cong (g := g * k) hn hint' (cong_inv hint' hcong) h
  rwa [mul_inv_cancel_right] at this

theorem condAt_mul_of_ent_eq_one {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (g : AdelicGL2 (𝓞 K) K) {k : AdelicGL2 (𝓞 K) K}
    (hk : ∀ i j, ent k i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) :
    CondAt n v (g * k) ↔ CondAt n v g := by
  unfold CondAt
  rw [ent_mul, ent_mul, hk, hk, hk, hk]
  simp [Matrix.one_apply]

theorem isOpen_setOf_condAt {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} (hn : 0 < n v) :
    IsOpen {g : AdelicGL2 (𝓞 K) K | CondAt n v g} := by
  obtain ⟨t, ht0, ht⟩ := exists_valued_eq_eps n v
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_valued_eq_exp_neg (K := K) v 1
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  change CondAt n v g at hg
  set c := ent g 1 0 v with hc
  set d := ent g 1 1 v with hd

  have hd0 : d ≠ 0 := by
    intro h0
    rcases ent_one_ne_zero g v with h1 | h1
    · apply h1
      unfold CondAt at hg
      rw [← hd, h0, Valuation.map_zero, zero_mul] at hg
      exact (Valuation.zero_iff Valued.v).mp (le_antisymm hg zero_le')
    · exact h1 h0
  have hvd : Valued.v d ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hd0

  refine ⟨{g' | Valued.v (ent g' 1 1 v - d) ≤ Valued.v (d * ϖ)} ∩ {g' | Valued.v (ent g' 1 0 v - c) ≤ Valued.v (d * t * ϖ)},
    ?_, ?_, ?_⟩
  · rintro g' ⟨h1, h2⟩
    change Valued.v (ent g' 1 1 v - d) ≤ Valued.v (d * ϖ) at h1
    change Valued.v (ent g' 1 0 v - c) ≤ Valued.v (d * t * ϖ) at h2
    change CondAt n v g'
    unfold CondAt at hg ⊢
    have hd' : Valued.v (ent g' 1 1 v) = Valued.v d := by
      refine Valuation.map_eq_of_sub_lt Valued.v (lt_of_le_of_lt h1 ?_)
      rw [map_mul]
      calc Valued.v d * Valued.v ϖ < Valued.v d * 1 := mul_lt_mul_of_pos_left hϖ1 (zero_lt_iff.mpr hvd)
        _ = Valued.v d := mul_one _
    rw [hd']
    have hsplit : ent g' 1 0 v = c + (ent g' 1 0 v - c) := by ring
    rw [hsplit]
    calc Valued.v (c + (ent g' 1 0 v - c)) ≤ max (Valued.v c) (Valued.v (ent g' 1 0 v - c)) := Valuation.map_add Valued.v _ _
      _ ≤ Valued.v d * eps n v := by
          apply max_le hg
          calc Valued.v (ent g' 1 0 v - c) ≤ Valued.v (d * t * ϖ) := h2
            _ = Valued.v d * eps n v * Valued.v ϖ := by rw [map_mul, map_mul, ht]
            _ ≤ Valued.v d * eps n v * 1 := mul_le_mul_right hϖ1.le _
            _ = Valued.v d * eps n v := mul_one _
  · apply IsOpen.inter
    · exact (isOpen_setOf_valued_le v (d * ϖ) (mul_ne_zero hd0 hϖ0)).preimage
        ((continuous_ent 1 1 v).sub continuous_const)
    · exact (isOpen_setOf_valued_le v (d * t * ϖ) (mul_ne_zero (mul_ne_zero hd0 ht0) hϖ0)).preimage
        ((continuous_ent 1 0 v).sub continuous_const)
  · constructor
    · show Valued.v (ent g 1 1 v - d) ≤ Valued.v (d * ϖ)
      rw [← hd, sub_self, Valuation.map_zero]; exact zero_le'
    · show Valued.v (ent g 1 0 v - c) ≤ Valued.v (d * t * ϖ)
      rw [← hc, sub_self, Valuation.map_zero]; exact zero_le'

theorem isOpen_setOf_not_condAt {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} (hn : 0 < n v) :
    IsOpen {g : AdelicGL2 (𝓞 K) K | ¬ CondAt n v g} := by
  obtain ⟨t, ht0, ht⟩ := exists_valued_eq_eps n v
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_valued_eq_exp_neg (K := K) v 1
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hε1 : eps n v < 1 := eps_lt_one hn
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  change ¬ CondAt n v g at hg
  set c := ent g 1 0 v with hc
  set d := ent g 1 1 v with hd
  unfold CondAt at hg
  push Not at hg

  have hc0 : c ≠ 0 := by
    intro h0; rw [← hc, h0, Valuation.map_zero] at hg; exact (not_lt.mpr zero_le') hg
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hc0
  refine ⟨{g' | Valued.v (ent g' 1 0 v - c) ≤ Valued.v (c * ϖ)} ∩ {g' | Valued.v (ent g' 1 1 v - d) ≤ Valued.v c},
    ?_, ?_, ?_⟩
  · rintro g' ⟨h1, h2⟩
    change Valued.v (ent g' 1 0 v - c) ≤ Valued.v (c * ϖ) at h1
    change Valued.v (ent g' 1 1 v - d) ≤ Valued.v c at h2
    change ¬ CondAt n v g'
    unfold CondAt
    push Not
    have hc' : Valued.v (ent g' 1 0 v) = Valued.v c := by
      refine Valuation.map_eq_of_sub_lt Valued.v (lt_of_le_of_lt h1 ?_)
      rw [map_mul]
      calc Valued.v c * Valued.v ϖ < Valued.v c * 1 := mul_lt_mul_of_pos_left hϖ1 (zero_lt_iff.mpr hvc)
        _ = Valued.v c := mul_one _
    rw [hc']
    have hsplit : ent g' 1 1 v = d + (ent g' 1 1 v - d) := by ring
    rw [hsplit]
    calc Valued.v (d + (ent g' 1 1 v - d)) * eps n v
        ≤ max (Valued.v d) (Valued.v (ent g' 1 1 v - d)) * eps n v :=
          mul_le_mul_left (Valuation.map_add Valued.v _ _) _
      _ < Valued.v c := by
          rcases le_total (Valued.v d) (Valued.v (ent g' 1 1 v - d)) with hle | hle
          · rw [max_eq_right hle]
            calc Valued.v (ent g' 1 1 v - d) * eps n v ≤ Valued.v c * eps n v := mul_le_mul_left h2 _
              _ < Valued.v c * 1 := mul_lt_mul_of_pos_left hε1 (zero_lt_iff.mpr hvc)
              _ = Valued.v c := mul_one _
          · rw [max_eq_left hle]; exact hg
  · apply IsOpen.inter
    · exact (isOpen_setOf_valued_le v (c * ϖ) (mul_ne_zero hc0 hϖ0)).preimage
        ((continuous_ent 1 0 v).sub continuous_const)
    · exact (isOpen_setOf_valued_le v c hc0).preimage ((continuous_ent 1 1 v).sub continuous_const)
  · constructor
    · show Valued.v (ent g 1 0 v - c) ≤ Valued.v (c * ϖ)
      rw [← hc, sub_self, Valuation.map_zero]; exact zero_le'
    · show Valued.v (ent g 1 1 v - d) ≤ Valued.v c
      rw [← hd, sub_self, Valuation.map_zero]; exact zero_le'

theorem isClopen_setOf_cond (S : Finset (HeightOneSpectrum (𝓞 K))) {n : HeightOneSpectrum (𝓞 K) → ℕ}
    (hn : ∀ v ∈ S, 0 < n v) : IsClopen {g : AdelicGL2 (𝓞 K) K | ∀ v ∈ S, CondAt n v g} := by
  have h : {g : AdelicGL2 (𝓞 K) K | ∀ v ∈ S, CondAt n v g} = ⋂ v ∈ S, {g | CondAt n v g} := by
    ext g; simp
  rw [h]
  refine ⟨?_, ?_⟩
  · refine isClosed_biInter fun v hv => ?_
    rw [← isOpen_compl_iff]
    exact isOpen_setOf_not_condAt (hn v hv)
  · exact S.finite_toSet.isOpen_biInter fun v hv => isOpen_setOf_condAt (hn v hv)

end RS11SC

end

noncomputable section

namespace RS11SC

open MeasureTheory NumberField NumberField.AdelicHeight NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain Matrix AdelicDock FLT.SmoothVectors

open scoped NNReal Classical

variable {K : Type} [Field K] [NumberField K]

theorem ent_eq_finComponent (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ent g i j v = (finComponent (𝓞 K) K v (glFin (𝓞 K) K g) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j :=
  rfl

theorem ent_eq_one_of_finComponent_eq_one {g : AdelicGL2 (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (h : finComponent (𝓞 K) K v (glFin (𝓞 K) K g) = 1) (i j : Fin 2) :
    ent g i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  rw [ent_eq_finComponent, h, Matrix.GeneralLinearGroup.coe_one]

theorem ent_eq_one_of_glFin_eq_one {g : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K g = 1) (v : HeightOneSpectrum (𝓞 K))
    (i j : Fin 2) : ent g i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j :=
  ent_eq_one_of_finComponent_eq_one (by rw [h, map_one]) i j

theorem placeEmbed_apply (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (v.adicCompletion K)) :
    UnramifiedWhittaker.placeEmbed K v k = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) := rfl

theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v k) = 1 := by
  rw [placeEmbed_apply, glArch_finEmbed]

theorem finComponent_placeEmbed_self (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (v.adicCompletion K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v k)) = k := by
  rw [placeEmbed_apply, glFin_finEmbed, finComponent_localEmbed_self]

theorem finComponent_placeEmbed_of_ne (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    finComponent (𝓞 K) K w (glFin (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v k)) = 1 := by
  rw [placeEmbed_apply, glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

def sel (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  if Valued.v (ent g 1 0 v) ≤ Valued.v (ent g 1 1 v) then ent g 1 1 v else ent g 1 0 v

theorem valued_sel (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (sel g v) = max (Valued.v (ent g 1 0 v)) (Valued.v (ent g 1 1 v)) := by
  unfold sel
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_lt (not_le.mp h))]

theorem sel_ne_zero (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) : sel g v ≠ 0 := by
  intro h0
  have h := valued_sel g v
  rw [h0, Valuation.map_zero] at h
  rcases ent_one_ne_zero g v with h1 | h1
  · exact h1 ((Valuation.zero_iff _).mp (le_antisymm (h ▸ le_max_left _ _) zero_le'))
  · exact h1 ((Valuation.zero_iff _).mp (le_antisymm (h ▸ le_max_right _ _) zero_le'))

theorem sel_of_condAt {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} {g : AdelicGL2 (𝓞 K) K}
    (h : CondAt n v g) : sel g v = ent g 1 1 v := by
  unfold sel
  rw [if_pos (le_trans h (mul_le_of_le_one_right' (eps_le_one n v)))]

theorem ent_borel_one_one_ne_zero {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ent b 1 1 v ≠ 0 := by
  have h10 : ent b 1 0 v = 0 := by
    have : ((b : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hb
    rw [ent, this, map_zero]
  rcases ent_one_ne_zero b v with h | h
  · exact absurd h10 h
  · exact h

theorem sel_borel_mul {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) : sel (b * g) v = ent b 1 1 v * sel g v := by
  have h10 : ent b 1 0 v = 0 := by
    have : ((b : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hb
    rw [ent, this, map_zero]
  have hb0 : Valued.v (ent b 1 1 v) ≠ 0 := (Valuation.ne_zero_iff _).mpr (ent_borel_one_one_ne_zero hb v)
  have e0 : ent (b * g) 1 0 v = ent b 1 1 v * ent g 1 0 v := by rw [ent_mul, h10, zero_mul, zero_add]
  have e1 : ent (b * g) 1 1 v = ent b 1 1 v * ent g 1 1 v := by rw [ent_mul, h10, zero_mul, zero_add]
  unfold sel
  rw [e0, e1, map_mul, map_mul]
  have key : ∀ x y : WithZero (Multiplicative ℤ),
      Valued.v (ent b 1 1 v) * x ≤ Valued.v (ent b 1 1 v) * y → x ≤ y := by
    intro x y hxy
    have := mul_le_mul_right hxy (Valued.v (ent b 1 1 v))⁻¹
    rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul, one_mul] at this
  by_cases h : Valued.v (ent g 1 0 v) ≤ Valued.v (ent g 1 1 v)
  · rw [if_pos h, if_pos (mul_le_mul_right h _)]
  · rw [if_neg h, if_neg (fun h' => h (key _ _ h'))]

theorem sel_mul_of_ent_eq_one (g : AdelicGL2 (𝓞 K) K) {k : AdelicGL2 (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hk : ∀ i j, ent k i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) :
    sel (g * k) v = sel g v := by
  have e0 : ent (g * k) 1 0 v = ent g 1 0 v := by rw [ent_mul, hk, hk]; simp [Matrix.one_apply]
  have e1 : ent (g * k) 1 1 v = ent g 1 1 v := by rw [ent_mul, hk, hk]; simp [Matrix.one_apply]
  unfold sel
  rw [e0, e1]

theorem eventually_valued_ent_le_one (h : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, Valued.v (ent h i j v) ≤ 1 := by
  have := (((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2).2
  filter_upwards [this] with v hv
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hv

theorem eventually_integral (g : AdelicGL2 (𝓞 K) K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (∀ i j, Valued.v (ent g i j v) ≤ 1) ∧ (∀ i j, Valued.v (ent g⁻¹ i j v) ≤ 1) := by
  refine ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valued_ent_le_one g i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valued_ent_le_one g⁻¹ i j)).mono ?_
  intro v hv
  exact ⟨fun i j => hv.1 i j, fun i j => hv.2 i j⟩

theorem det_ent_mul_det_ent_inv (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    (ent g 0 0 v * ent g 1 1 v - ent g 0 1 v * ent g 1 0 v) *
      (ent g⁻¹ 0 0 v * ent g⁻¹ 1 1 v - ent g⁻¹ 0 1 v * ent g⁻¹ 1 0 v) = 1 := by
  have hd : ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).det *
      (((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.det_one]
  have := congrArg (πv v) hd
  rw [map_mul, map_one, Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul] at this
  exact this

theorem valued_sel_eq_one_of_integral {g : AdelicGL2 (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hint : ∀ i j, Valued.v (ent g i j v) ≤ 1) (hint' : ∀ i j, Valued.v (ent g⁻¹ i j v) ≤ 1) :
    Valued.v (sel g v) = 1 := by
  rw [valued_sel]
  apply le_antisymm (max_le (hint 1 0) (hint 1 1))
  by_contra hlt
  rw [not_le] at hlt
  have h10 : Valued.v (ent g 1 0 v) < 1 := lt_of_le_of_lt (le_max_left _ _) hlt
  have h11 : Valued.v (ent g 1 1 v) < 1 := lt_of_le_of_lt (le_max_right _ _) hlt
  have hA : Valued.v (ent g 0 0 v * ent g 1 1 v - ent g 0 1 v * ent g 1 0 v) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      calc Valued.v (ent g 0 0 v) * Valued.v (ent g 1 1 v) ≤ 1 * Valued.v (ent g 1 1 v) := mul_le_mul' (hint 0 0) le_rfl
        _ < 1 := by rw [one_mul]; exact h11
    · rw [map_mul]
      calc Valued.v (ent g 0 1 v) * Valued.v (ent g 1 0 v) ≤ 1 * Valued.v (ent g 1 0 v) := mul_le_mul' (hint 0 1) le_rfl
        _ < 1 := by rw [one_mul]; exact h10
  have hB : Valued.v (ent g⁻¹ 0 0 v * ent g⁻¹ 1 1 v - ent g⁻¹ 0 1 v * ent g⁻¹ 1 0 v) ≤ 1 := by
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · rw [map_mul]
      calc Valued.v (ent g⁻¹ 0 0 v) * Valued.v (ent g⁻¹ 1 1 v) ≤ 1 * 1 := mul_le_mul' (hint' 0 0) (hint' 1 1)
        _ = 1 := one_mul 1
    · rw [map_mul]
      calc Valued.v (ent g⁻¹ 0 1 v) * Valued.v (ent g⁻¹ 1 0 v) ≤ 1 * 1 := mul_le_mul' (hint' 0 1) (hint' 1 0)
        _ = 1 := one_mul 1
  have hprod := congrArg Valued.v (det_ent_mul_det_ent_inv g v)
  rw [map_mul, map_one] at hprod
  have : Valued.v (ent g 0 0 v * ent g 1 1 v - ent g 0 1 v * ent g 1 0 v) *
      Valued.v (ent g⁻¹ 0 0 v * ent g⁻¹ 1 1 v - ent g⁻¹ 0 1 v * ent g⁻¹ 1 0 v) < 1 :=
    calc _ ≤ Valued.v (ent g 0 0 v * ent g 1 1 v - ent g 0 1 v * ent g 1 0 v) * 1 := mul_le_mul_right hB _
      _ < 1 := by rw [mul_one]; exact hA
  rw [hprod] at this
  exact lt_irrefl _ this

theorem eventually_valued_sel_eq_one (g : AdelicGL2 (𝓞 K) K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, Valued.v (sel g v) = 1 :=
  (eventually_integral g).mono fun _ hv => valued_sel_eq_one_of_integral hv.1 hv.2

def yFin (g : AdelicGL2 (𝓞 K) K) : (FiniteAdeleRing (𝓞 K) K)ˣ where
  val := ⟨fun v => sel g v, (eventually_valued_sel_eq_one g).mono fun v hv =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hv.le⟩
  inv := ⟨fun v => (sel g v)⁻¹, (eventually_valued_sel_eq_one g).mono fun v hv => by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_
    rw [map_inv₀, hv, inv_one]⟩
  val_inv := RestrictedProduct.ext _ _ fun v => mul_inv_cancel₀ (sel_ne_zero g v)
  inv_val := RestrictedProduct.ext _ _ fun v => inv_mul_cancel₀ (sel_ne_zero g v)

def yIdele (g : AdelicGL2 (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ := Units.map (finIncl (𝓞 K) K) (yFin g)

theorem yIdele_fst (g : AdelicGL2 (𝓞 K) K) : ((yIdele g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl
theorem yIdele_snd (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ((yIdele g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = sel g v := rfl

theorem yIdele_eq_of_glFin_eq {g g' : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') :
    yIdele g = yIdele g' := by
  have he : ∀ i j v, ent g i j v = ent g' i j v := fun i j v => by
    rw [ent_eq_finComponent, ent_eq_finComponent, h]
  refine Units.ext (Prod.ext rfl (RestrictedProduct.ext _ _ fun v => ?_))
  show sel g v = sel g' v
  unfold sel
  rw [he, he]

theorem yIdele_borel_mul {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) (hba : glArch (𝓞 K) K b = 1)
    (g : AdelicGL2 (𝓞 K) K) :
    yIdele (b * g) = borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) * yIdele g := by
  refine Units.ext (Prod.ext ?_ (RestrictedProduct.ext _ _ fun v => ?_))
  · change (1 : InfiniteAdeleRing K) = ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).1 * 1
    rw [mul_one]
    have := congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) hba
    simp only [glArch_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply_eq] at this
    exact this.symm
  · change sel (b * g) v = ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v * sel g v
    exact sel_borel_mul hb g v

open NumberField.TateGlobal NumberField.AdeleRing

def iota (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)).comp (localUnit (𝓞 K) K v)

theorem localChar_eq (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    localChar ν v t = ν (iota v t) := rfl

theorem iota_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((iota v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

theorem iota_snd_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((iota v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = t := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = t
  exact localUnit_apply_self (𝓞 K) K v t

theorem iota_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ≠ v) : ((iota v t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
  show ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1
  exact localUnit_apply_of_ne (𝓞 K) K v t hw

def archHom : (AdeleRing (𝓞 K) K)ˣ →* InfiniteAdeleRing K :=
  (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (Units.coeHom (AdeleRing (𝓞 K) K))

def finHom (w : HeightOneSpectrum (𝓞 K)) : (AdeleRing (𝓞 K) K)ˣ →* w.adicCompletion K :=
  (πv (K := K) w).toMonoidHom.comp (Units.coeHom (AdeleRing (𝓞 K) K))

theorem archHom_apply (x : (AdeleRing (𝓞 K) K)ˣ) : archHom x = (x : AdeleRing (𝓞 K) K).1 := rfl
theorem finHom_apply (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ) : finHom w x = (x : AdeleRing (𝓞 K) K).2 w := rfl

theorem finHom_inv (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ) :
    finHom w x⁻¹ = (finHom w x)⁻¹ := by
  have h : finHom w x⁻¹ * finHom w x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  exact eq_inv_of_mul_eq_one_left h

theorem valued_finHom_ne_zero (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ) : finHom w x ≠ 0 := by
  intro h0
  have h : finHom w x⁻¹ * finHom w x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [h0, mul_zero] at h
  exact zero_ne_one h

theorem continuous_units_of_continuous_val {ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) : Continuous ν := by
  refine Units.continuous_iff.mpr ⟨hνc, ?_⟩
  have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z)⁻¹ : ℂˣ).val) = (fun z => ((ν z : ℂˣ) : ℂ)) ∘ (fun z => z⁻¹) := by
    funext z; simp [map_inv]
  rw [this]
  exact hνc.comp continuous_inv

theorem apply_eq_prod_localChar (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hνout : ∀ v, v ∉ S → IsUnramifiedCharAt ν v)
    (x : (AdeleRing (𝓞 K) K)ˣ) (hx1 : (x : AdeleRing (𝓞 K) K).1 = 1)
    (hxu : ∀ v, v ∉ S → Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1) :
    ν x = ∏ v ∈ S, localChar ν v (Units.mk0 ((x : AdeleRing (𝓞 K) K).2 v) (valued_finHom_ne_zero v x)) := by
  set z : (AdeleRing (𝓞 K) K)ˣ := ∏ v ∈ S, iota v (Units.mk0 ((x : AdeleRing (𝓞 K) K).2 v) (valued_finHom_ne_zero v x)) with hz

  have hz1 : archHom z = 1 := by
    rw [hz, map_prod]
    exact Finset.prod_eq_one fun v _ => iota_fst v (Units.mk0 _ (valued_finHom_ne_zero v x))
  have hz2 : ∀ w ∈ S, finHom w z = (x : AdeleRing (𝓞 K) K).2 w := by
    intro w hw
    rw [hz, map_prod, Finset.prod_eq_single w]
    · rw [finHom_apply, iota_snd_self]; rfl
    · intro v _ hvw
      rw [finHom_apply, iota_snd_of_ne v _ (Ne.symm hvw)]
    · intro h; exact absurd hw h
  have hz3 : ∀ w, w ∉ S → finHom w z = 1 := by
    intro w hw
    rw [hz, map_prod]
    exact Finset.prod_eq_one fun v hv => by
      rw [finHom_apply, iota_snd_of_ne v _ (by rintro rfl; exact hw hv)]

  set u : (AdeleRing (𝓞 K) K)ˣ := x * z⁻¹ with hu
  have hx : x = u * z := by rw [hu, inv_mul_cancel_right]
  have hu1 : (u : AdeleRing (𝓞 K) K).1 = 1 := by
    have h := congrArg archHom hx
    rw [map_mul, hz1, mul_one, archHom_apply, archHom_apply] at h
    rw [← h]; exact hx1
  have hu2 : ∀ w ∈ S, (u : AdeleRing (𝓞 K) K).2 w = 1 := by
    intro w hw
    have h : finHom w u = 1 := by
      rw [hu, map_mul, finHom_inv, hz2 w hw, finHom_apply]
      exact mul_inv_cancel₀ (valued_finHom_ne_zero w x)
    exact h
  have hu3 : ∀ w, w ∉ S → (u : AdeleRing (𝓞 K) K).2 w = (x : AdeleRing (𝓞 K) K).2 w := by
    intro w hw
    have h : finHom w u = finHom w x := by
      rw [hu, map_mul, finHom_inv, hz3 w hw, inv_one, mul_one]
    exact h
  have huU : finitePartUnits (𝓞 K) K u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
    have hval : ∀ w, Valued.v ((u : AdeleRing (𝓞 K) K).2 w) = 1 := fun w => by
      by_cases hw : w ∈ S
      · rw [hu2 w hw, map_one]
      · rw [hu3 w hw, hxu w hw]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · rw [val_finitePartUnits]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hval w).le
    · rw [← map_inv, val_finitePartUnits]
      refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_
      have h := finHom_inv w u
      rw [finHom_apply, finHom_apply] at h
      rw [h, map_inv₀, hval w, inv_one]
  have hνu : ν u = 1 :=
    NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous K ν
      (continuous_units_of_continuous_val hνc) S hνout u hu1 hu2 huU
  have h1 : ν x = ν z := by
    conv_lhs => rw [hx]
    rw [map_mul, hνu, one_mul]
  rw [h1, hz, map_prod]
  rfl

def finP : AdelicGL2 (𝓞 K) K →* AdelicGL2 (𝓞 K) K := (AdelicDock.finEmbed (𝓞 K) K).comp (glFin (𝓞 K) K)

theorem glFin_finP (g : AdelicGL2 (𝓞 K) K) : glFin (𝓞 K) K (finP g) = glFin (𝓞 K) K g :=
  AdelicDock.glFin_finEmbed (𝓞 K) K _
theorem glArch_finP (g : AdelicGL2 (𝓞 K) K) : glArch (𝓞 K) K (finP g) = 1 := AdelicDock.glArch_finEmbed (𝓞 K) K _

theorem gl_eq_of_parts {g g' : AdelicGL2 (𝓞 K) K} (h1 : glArch (𝓞 K) K g = glArch (𝓞 K) K g')
    (h2 : glFin (𝓞 K) K g = glFin (𝓞 K) K g') : g = g' := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h1
    simpa [glArch_apply] using this
  · have := congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h2
    simpa [glFin_apply] using this

theorem finP_eq_self_of_glArch_eq_one {b : AdelicGL2 (𝓞 K) K} (hba : glArch (𝓞 K) K b = 1) : finP b = b :=
  gl_eq_of_parts (by rw [glArch_finP, hba]) (glFin_finP b)

theorem finP_eq_of_glFin_eq {g g' : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') : finP g = finP g' := by
  unfold finP; simp only [MonoidHom.comp_apply, h]

theorem ent_finP (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) : ent (finP g) i j v = ent g i j v := by
  rw [ent_eq_finComponent, ent_eq_finComponent, glFin_finP]

theorem condAt_iff_of_glFin_eq {n : HeightOneSpectrum (𝓞 K) → ℕ} {v : HeightOneSpectrum (𝓞 K)} {g g' : AdelicGL2 (𝓞 K) K}
    (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') : CondAt n v g ↔ CondAt n v g' := by
  have he : ∀ i j, ent g i j v = ent g' i j v := fun i j => by rw [ent_eq_finComponent, ent_eq_finComponent, h]
  unfold CondAt; rw [he, he]

theorem adelicHeight_finP_eq_one {k : AdelicGL2 (𝓞 K) K} (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K) :
    adelicHeight K (finP k) = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hki
  have h := P6B.JE2aFlat.adelicHeight_mul_of_integral_of_rowIsometry 1 (finP k) (fun v i j => ?_) (fun v i j => ?_)
    (fun w => by rw [glArch_finP, map_one]; exact isRowIsometry_one)
  · rwa [one_mul, P6B.JE2aFlat.adelicHeight_one] at h
  · rw [finComponent_apply, glFin_finP]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.1 i j v)
  · rw [← map_inv, ← map_inv, finComponent_apply, glFin_finP, map_inv]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.2 i j v)

theorem adelicHeight_finP_mul {g k : AdelicGL2 (𝓞 K) K} (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K) :
    adelicHeight K (finP (g * k)) = adelicHeight K (finP g) := by
  rw [mem_finiteIntegralGL2_iff] at hki
  rw [map_mul]
  refine P6B.JE2aFlat.adelicHeight_mul_of_integral_of_rowIsometry (finP g) (finP k) (fun v i j => ?_) (fun v i j => ?_)
    (fun w => by rw [glArch_finP, map_one]; exact isRowIsometry_one)
  · rw [finComponent_apply, glFin_finP]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.1 i j v)
  · rw [← map_inv, ← map_inv, finComponent_apply, glFin_finP, map_inv]
    exact norm_le_one_of_mem_adicCompletionIntegers (hki.2 i j v)

theorem max_valued_mul_of_integral (g : AdelicGL2 (𝓞 K) K) {k : AdelicGL2 (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hint : ∀ i j, Valued.v (ent k i j v) ≤ 1) (hint' : ∀ i j, Valued.v (ent k⁻¹ i j v) ≤ 1) :
    max (Valued.v (ent (g * k) 1 0 v)) (Valued.v (ent (g * k) 1 1 v)) = max (Valued.v (ent g 1 0 v)) (Valued.v (ent g 1 1 v)) := by
  have hle : ∀ (h : AdelicGL2 (𝓞 K) K) {m : AdelicGL2 (𝓞 K) K}, (∀ i j, Valued.v (ent m i j v) ≤ 1) →
      max (Valued.v (ent (h * m) 1 0 v)) (Valued.v (ent (h * m) 1 1 v)) ≤ max (Valued.v (ent h 1 0 v)) (Valued.v (ent h 1 1 v)) := by
    intro h m hm
    have hrow : ∀ j, Valued.v (ent (h * m) 1 j v) ≤ max (Valued.v (ent h 1 0 v)) (Valued.v (ent h 1 1 v)) := by
      intro j
      rw [ent_mul]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · rw [map_mul]
        calc Valued.v (ent h 1 0 v) * Valued.v (ent m 0 j v) ≤ Valued.v (ent h 1 0 v) * 1 := mul_le_mul_right (hm 0 j) _
          _ ≤ _ := by rw [mul_one]; exact le_max_left _ _
      · rw [map_mul]
        calc Valued.v (ent h 1 1 v) * Valued.v (ent m 1 j v) ≤ Valued.v (ent h 1 1 v) * 1 := mul_le_mul_right (hm 1 j) _
          _ ≤ _ := by rw [mul_one]; exact le_max_right _ _
    exact max_le (hrow 0) (hrow 1)
  apply le_antisymm (hle g hint)
  have := hle (g * k) hint'
  rwa [mul_inv_cancel_right] at this

theorem valued_sel_mul_of_integral (g : AdelicGL2 (𝓞 K) K) {k : AdelicGL2 (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)}
    (hint : ∀ i j, Valued.v (ent k i j v) ≤ 1) (hint' : ∀ i j, Valued.v (ent k⁻¹ i j v) ≤ 1) :
    Valued.v (sel (g * k) v) = Valued.v (sel g v) := by
  rw [valued_sel, valued_sel, max_valued_mul_of_integral g hint hint']

def twist (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (g : AdelicGL2 (𝓞 K) K) : ℂ := ((ν (yIdele g) : ℂˣ) : ℂ)

def psi (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) (s : ℂ)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  if ∀ v ∈ S, CondAt n v g then ((adelicHeight K (finP g) : ℝ) : ℂ) ^ (s + 1 / 2) * twist ν g else 0

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) (s : ℂ)
  (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

theorem psi_of_cond {g : AdelicGL2 (𝓞 K) K} (h : ∀ v ∈ S, CondAt n v g) :
    psi S n s ν g = ((adelicHeight K (finP g) : ℝ) : ℂ) ^ (s + 1 / 2) * twist ν g := if_pos h

theorem psi_of_not_cond {g : AdelicGL2 (𝓞 K) K} (h : ¬ ∀ v ∈ S, CondAt n v g) : psi S n s ν g = 0 := if_neg h

theorem psi_eq_of_glFin_eq {g g' : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') :
    psi S n s ν g = psi S n s ν g' := by
  have hc : (∀ v ∈ S, CondAt n v g) ↔ ∀ v ∈ S, CondAt n v g' := forall₂_congr fun v _ => condAt_iff_of_glFin_eq h
  unfold psi twist
  rw [finP_eq_of_glFin_eq h, yIdele_eq_of_glFin_eq h]
  by_cases hg : ∀ v ∈ S, CondAt n v g'
  · rw [if_pos hg, if_pos (hc.mpr hg)]
  · rw [if_neg hg, if_neg (fun h' => hg (hc.mp h'))]

theorem psi_borel_mul (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hflat : IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s)
      (fun g : AdelicGL2 (𝓞 K) K => ((adelicHeight K g : ℝ) : ℂ) ^ (s + 1 / 2)))
    {b : AdelicGL2 (𝓞 K) K} (hb : b ∈ adelicBorel (𝓞 K) K) (hba : glArch (𝓞 K) K b = 1) (g : AdelicGL2 (𝓞 K) K) :
    psi S n s ν (b * g) =
      ((etaFst 1 α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
        ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * psi S n s ν g := by
  by_cases h : ∀ v ∈ S, CondAt n v g
  · have h' : ∀ v ∈ S, CondAt n v (b * g) := fun v hv => condAt_borel_mul_imp hb (h v hv)
    rw [psi_of_cond S n s ν h', psi_of_cond S n s ν h]
    have hH : ((adelicHeight K (finP (b * g)) : ℝ) : ℂ) ^ (s + 1 / 2) =
        ((etaFst 1 α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
          ((etaSnd 1 α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
            ((adelicHeight K (finP g) : ℝ) : ℂ) ^ (s + 1 / 2) := by
      rw [map_mul, finP_eq_self_of_glArch_eq_one hba]
      exact hflat b hb (finP g)
    have hN : twist ν (b * g) = ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * twist ν g := by
      unfold twist
      rw [yIdele_borel_mul hb hba, map_mul, Units.val_mul]
    rw [hH, hN, etaSnd_apply ν, etaSnd_apply (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)]
    simp only [MonoidHom.one_apply, one_mul, Units.val_mul]
    ring
  · have h' : ¬ ∀ v ∈ S, CondAt n v (b * g) := fun h' => h fun v hv => (condAt_borel_mul_iff hb g).mp (h' v hv)
    rw [psi_of_not_cond S n s ν h', psi_of_not_cond S n s ν h, mul_zero]

theorem psi_eq_zero_of_exists {g : AdelicGL2 (𝓞 K) K} (h : ∃ v ∈ S, ¬ CondAt n v g) : psi S n s ν g = 0 := by
  obtain ⟨v, hv, hnc⟩ := h
  exact psi_of_not_cond S n s ν (fun h' => hnc (h' v hv))

theorem yIdele_mul_inv_fst (g g' : AdelicGL2 (𝓞 K) K) :
    (((yIdele g' * (yIdele g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).1 = 1 := by
  show (1 : InfiniteAdeleRing K) * 1 = 1
  rw [one_mul]

theorem yIdele_mul_inv_snd (g g' : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    (((yIdele g' * (yIdele g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v = sel g' v * (sel g v)⁻¹ := rfl

theorem twist_eq_of {g g' : AdelicGL2 (𝓞 K) K} (h : ν (yIdele g' * (yIdele g)⁻¹) = 1) : twist ν g' = twist ν g := by
  unfold twist
  have : yIdele g' = (yIdele g' * (yIdele g)⁻¹) * yIdele g := by rw [inv_mul_cancel_right]
  rw [this, map_mul, h, one_mul]

theorem localChar_mk0_eq_one_of {v : HeightOneSpectrum (𝓞 K)} {t : v.adicCompletion K} (ht : t ≠ 0)
    (hνS : ∀ u : (v.adicCompletion K)ˣ, Valued.v ((u : v.adicCompletion K) - 1) ≤ eps n v → localChar ν v u = 1)
    (h : Valued.v (t - 1) ≤ eps n v) : localChar ν v (Units.mk0 t ht) = 1 :=
  hνS _ h

theorem psi_mul_of_cong' (hn : ∀ v ∈ S, 0 < n v)
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v ((t : v.adicCompletion K) - 1) ≤ eps n v → localChar ν v t = 1)
    (hνout : ∀ v, v ∉ S → IsUnramifiedCharAt ν v)
    (g k : AdelicGL2 (𝓞 K) K) (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K)
    (hkc : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤ eps n v) :
    psi S n s ν (g * k) = psi S n s ν g := by
  have hki' := hki
  rw [mem_finiteIntegralGL2_iff] at hki
  have hint : ∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k i j v) ≤ 1 := fun v i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hki.1 i j v)
  have hint' : ∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k⁻¹ i j v) ≤ 1 := fun v i j => by
    have := hki.2 i j v
    rw [← map_inv] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp this
  have hcong : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ eps n v := by
    intro v hv i j
    have h := hkc v hv i j
    rwa [← ent_one i j v, ent, ent, ← map_sub] at ⊢
  by_cases h : ∀ v ∈ S, CondAt n v g
  · have h' : ∀ v ∈ S, CondAt n v (g * k) := fun v hv => condAt_mul_of_cong (hn v hv) (hint v) (hcong v hv) (h v hv)
    rw [psi_of_cond S n s ν h', psi_of_cond S n s ν h, adelicHeight_finP_mul hki']
    congr 1
    refine twist_eq_of ν ?_
    set r : (AdeleRing (𝓞 K) K)ˣ := yIdele (g * k) * (yIdele g)⁻¹ with hr
    have hru : ∀ v, v ∉ S → Valued.v ((r : AdeleRing (𝓞 K) K).2 v) = 1 := by
      intro v hv
      rw [hr, yIdele_mul_inv_snd, map_mul, map_inv₀, valued_sel_mul_of_integral g (hint v) (hint' v),
        mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr (sel_ne_zero g v))]
    rw [apply_eq_prod_localChar ν hνc S hνout r (yIdele_mul_inv_fst g (g * k)) hru]
    refine Finset.prod_eq_one fun v hv => hνS v hv _ ?_

    change Valued.v (((r : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v - 1) ≤ eps n v
    rw [hr, yIdele_mul_inv_snd, sel_of_condAt (h' v hv), sel_of_condAt (h v hv)]
    set c := ent g 1 0 v
    set d := ent g 1 1 v
    have hd0 : d ≠ 0 := by
      intro h0
      have hc := h v hv
      change Valued.v c ≤ Valued.v d * eps n v at hc
      rw [h0, Valuation.map_zero, zero_mul] at hc
      rcases ent_one_ne_zero g v with h1 | h1
      · exact h1 ((Valuation.zero_iff _).mp (le_antisymm hc zero_le'))
      · exact h1 h0
    have hvd : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
    have hexp : ent (g * k) 1 1 v * d⁻¹ - 1 = (c * ent k 0 1 v + d * (ent k 1 1 v - 1)) * d⁻¹ := by
      rw [ent_mul]
      field_simp
      ring
    rw [hexp, map_mul, map_inv₀]
    have hnum : Valued.v (c * ent k 0 1 v + d * (ent k 1 1 v - 1)) ≤ Valued.v d * eps n v := by
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · rw [map_mul]
        have hc := h v hv
        change Valued.v c ≤ Valued.v d * eps n v at hc
        have h01 : Valued.v (ent k 0 1 v) ≤ eps n v := by
          have := hcong v hv 0 1
          rwa [Matrix.one_apply_ne (by decide), sub_zero] at this
        calc Valued.v c * Valued.v (ent k 0 1 v) ≤ Valued.v d * eps n v * eps n v := mul_le_mul' hc h01
          _ ≤ Valued.v d * eps n v * 1 := mul_le_mul_right (eps_le_one n v) _
          _ = Valued.v d * eps n v := mul_one _
      · rw [map_mul]
        have h11 : Valued.v (ent k 1 1 v - 1) ≤ eps n v := by
          have := hcong v hv 1 1
          rwa [Matrix.one_apply_eq] at this
        exact mul_le_mul_right h11 _
    calc Valued.v (c * ent k 0 1 v + d * (ent k 1 1 v - 1)) * (Valued.v d)⁻¹
        ≤ Valued.v d * eps n v * (Valued.v d)⁻¹ := mul_le_mul_left hnum _
      _ = eps n v := by rw [mul_comm (Valued.v d), mul_assoc, mul_inv_cancel₀ hvd, mul_one]
  · have h' : ¬ ∀ v ∈ S, CondAt n v (g * k) := fun h' => h fun v hv =>
      (condAt_mul_iff_of_cong (hn v hv) g (hint v) (hint' v) (hcong v hv)).mp (h' v hv)
    rw [psi_of_not_cond S n s ν h', psi_of_not_cond S n s ν h]

theorem glFin_placeEmbed_mem {v : HeightOneSpectrum (𝓞 K)} (kv : GL (Fin 2) (v.adicCompletionIntegers K)) :
    glFin (𝓞 K) K (UnramifiedWhittaker.placeEmbed K v
      (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) ∈
      finiteIntegralGL2 (𝓞 K) K := by
  set k := UnramifiedWhittaker.placeEmbed K v
      (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) with hk
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j w => ?_, fun i j w => ?_⟩
  · change (finComponent (𝓞 K) K w (glFin (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j ∈ _
    by_cases hw : w = v
    · subst hw
      rw [hk, finComponent_placeEmbed_self]
      change (algebraMap (w.adicCompletionIntegers K) (w.adicCompletion K)) ((kv : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
      exact SetLike.coe_mem _
    · rw [hk, finComponent_placeEmbed_of_ne v _ hw, Matrix.GeneralLinearGroup.coe_one]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · change (finComponent (𝓞 K) K w (glFin (𝓞 K) K k)⁻¹ : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j ∈ _
    by_cases hw : w = v
    · subst hw
      rw [hk, ← map_inv, ← map_inv, ← map_inv, finComponent_placeEmbed_self]
      change (algebraMap (w.adicCompletionIntegers K) (w.adicCompletion K)) (((kv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j) ∈ _
      exact SetLike.coe_mem _
    · rw [hk, ← map_inv, ← map_inv, ← map_inv, finComponent_placeEmbed_of_ne v _ hw, Matrix.GeneralLinearGroup.coe_one]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne hij]; exact zero_mem _

theorem psi_mul_placeEmbed (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (hνout : ∀ v, v ∉ S → IsUnramifiedCharAt ν v)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K) :
    psi S n s ν (g * UnramifiedWhittaker.placeEmbed K v
      (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) =
      psi S n s ν g := by
  set k := UnramifiedWhittaker.placeEmbed K v
      (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) with hk
  have hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K := glFin_placeEmbed_mem kv
  have hkw : ∀ w, w ≠ v → ∀ i j, ent k i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := fun w hw i j =>
    ent_eq_one_of_finComponent_eq_one (finComponent_placeEmbed_of_ne v _ hw) i j
  have hc : (∀ w ∈ S, CondAt n w (g * k)) ↔ ∀ w ∈ S, CondAt n w g :=
    forall₂_congr fun w hw => condAt_mul_of_ent_eq_one g (hkw w (fun h => hv (h ▸ hw)))
  by_cases h : ∀ w ∈ S, CondAt n w g
  · rw [psi_of_cond S n s ν (hc.mpr h), psi_of_cond S n s ν h, adelicHeight_finP_mul hki]
    congr 1
    refine twist_eq_of ν ?_
    have hki2 := hki
    rw [mem_finiteIntegralGL2_iff] at hki2
    have hint : ∀ (w : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k i j w) ≤ 1 := fun w i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hki2.1 i j w)
    have hint' : ∀ (w : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k⁻¹ i j w) ≤ 1 := fun w i j => by
      have := hki2.2 i j w
      rw [← map_inv] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp this
    set r : (AdeleRing (𝓞 K) K)ˣ := yIdele (g * k) * (yIdele g)⁻¹ with hr
    have hr1 : ∀ w, w ≠ v → ((r : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
      intro w hw
      rw [hr, yIdele_mul_inv_snd, sel_mul_of_ent_eq_one g (hkw w hw), mul_inv_cancel₀ (sel_ne_zero g w)]
    have hru : ∀ w, w ∉ S → Valued.v ((r : AdeleRing (𝓞 K) K).2 w) = 1 := by
      intro w hwS
      by_cases hw : w = v
      · subst hw
        rw [hr, yIdele_mul_inv_snd, map_mul, map_inv₀, valued_sel_mul_of_integral g (hint w) (hint' w),
          mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr (sel_ne_zero g w))]
      · rw [hr1 w hw, map_one]
    rw [apply_eq_prod_localChar ν hνc S hνout r (yIdele_mul_inv_fst g (g * k)) hru]
    refine Finset.prod_eq_one fun w hw => ?_
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    have : Units.mk0 (((r : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) (valued_finHom_ne_zero w r) = 1 :=
      Units.ext (by rw [Units.val_mk0, hr1 w hwv, Units.val_one])
    rw [this, map_one]
  · rw [psi_of_not_cond S n s ν (fun h' => h (hc.mp h')), psi_of_not_cond S n s ν h]

theorem psi_eq_prod (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (hνout : ∀ v, v ∉ S → IsUnramifiedCharAt ν v)
    (k : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
    (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K)
    (hd : ∀ v ∈ S, ent k 1 1 v = (d v : v.adicCompletion K))
    (hsupp : ∀ v ∈ S, CondAt n v k) :
    psi S n s ν k = ∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ) := by
  rw [psi_of_cond S n s ν hsupp, adelicHeight_finP_eq_one hki, Complex.ofReal_one, Complex.one_cpow, one_mul]
  have hki2 := hki
  rw [mem_finiteIntegralGL2_iff] at hki2
  have hint : ∀ (w : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k i j w) ≤ 1 := fun w i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hki2.1 i j w)
  have hint' : ∀ (w : HeightOneSpectrum (𝓞 K)) (i j : Fin 2), Valued.v (ent k⁻¹ i j w) ≤ 1 := fun w i j => by
    have := hki2.2 i j w
    rw [← map_inv] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp this
  unfold twist
  rw [apply_eq_prod_localChar ν hνc S hνout (yIdele k) (yIdele_fst k)
    (fun w _ => by rw [yIdele_snd]; exact valued_sel_eq_one_of_integral (hint w) (hint' w))]
  push_cast
  refine Finset.prod_congr rfl fun v hv => ?_
  have : Units.mk0 (((yIdele k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) (valued_finHom_ne_zero v (yIdele k)) = d v :=
    Units.ext (by rw [Units.val_mk0, yIdele_snd, sel_of_condAt (hsupp v hv), hd v hv])
  rw [this]

theorem exists_open_invariant (hn : ∀ v ∈ S, 0 < n v)
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v ((t : v.adicCompletion K) - 1) ≤ eps n v → localChar ν v t = 1)
    (hνout : ∀ v, v ∉ S → IsUnramifiedCharAt ν v) :
    ∃ O : Set (AdelicGL2 (𝓞 K) K), IsOpen O ∧ (1 : AdelicGL2 (𝓞 K) K) ∈ O ∧
      ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ O, psi S n s ν (g * k) = psi S n s ν g := by
  choose t ht0 ht using fun v : HeightOneSpectrum (𝓞 K) => exists_valued_eq_eps n v
  set O : Set (AdelicGL2 (𝓞 K) K) :=
    {k | glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K} ∩
      ⋂ v ∈ S, ⋂ i : Fin 2, ⋂ j : Fin 2,
        {k | Valued.v (ent k i j v - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ Valued.v (t v)} with hO
  have hOopen : IsOpen O := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_finiteLevelZero (𝓞 K) K (N := ⊤) (by simp)).preimage (continuous_glFin (𝓞 K) K)
    · refine S.finite_toSet.isOpen_biInter fun v _ => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact (isOpen_setOf_valued_le v (t v) (ht0 v)).preimage ((continuous_ent i j v).sub continuous_const)
  have hO1 : (1 : AdelicGL2 (𝓞 K) K) ∈ O := by
    refine ⟨?_, ?_⟩
    · show glFin (𝓞 K) K (1 : AdelicGL2 (𝓞 K) K) ∈ finiteIntegralGL2 (𝓞 K) K
      rw [map_one]; exact one_mem _
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro v _ i j
    rw [ent_one, sub_self, Valuation.map_zero]
    exact zero_le'
  refine ⟨O, hOopen, hO1, fun g k hk => ?_⟩
  obtain ⟨hk1, hk2⟩ := hk
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hk2
  refine psi_mul_of_cong' S n s ν hn hνc hνS hνout g k hk1 fun v hv i j => ?_
  have h := hk2 v hv i j
  rw [ht v] at h
  rwa [← ent_one i j v, ent, ent, ← map_sub] at h

theorem continuous_psi (hn : ∀ v ∈ S, 0 < n v)
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v ((t : v.adicCompletion K) - 1) ≤ eps n v → localChar ν v t = 1)
    (hνout : ∀ v, v ∉ S → IsUnramifiedCharAt ν v) :
    Continuous (psi S n s ν) := by
  obtain ⟨O, hOopen, hO1, hinv⟩ := exists_open_invariant S n s ν hn hνc hνS hνout
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hmem : {x : AdelicGL2 (𝓞 K) K | g⁻¹ * x ∈ O} ∈ nhds g :=
    (hOopen.preimage (continuous_mul_left g⁻¹)).mem_nhds (by simpa using hO1)
  refine (continuousAt_const : ContinuousAt (fun _ : AdelicGL2 (𝓞 K) K => psi S n s ν g) g).congr ?_
  filter_upwards [hmem] with x hx
  have : x = g * (g⁻¹ * x) := by rw [mul_inv_cancel_left]
  rw [this, hinv g _ hx]

theorem isKfSmooth_psi (hn : ∀ v ∈ S, 0 < n v)
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v ((t : v.adicCompletion K) - 1) ≤ eps n v → localChar ν v t = 1)
    (hνout : ∀ v, v ∉ S → IsUnramifiedCharAt ν v) :
    IsKfSmooth K (psi S n s ν) := by
  obtain ⟨O, hOopen, hO1, hinv⟩ := exists_open_invariant S n s ν hn hνc hνS hνout
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer]
  set G' := finiteAdelicGL2Subgroup K
  have hsub : ((↑) : G' → AdelicGL2 (𝓞 K) K) ⁻¹' O ⊆
      (MulAction.stabilizer G' (RightTranslationFn.mk (psi S n s ν)) : Set G') := by
    intro k hk
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    refine RightTranslationFn.ext fun g => ?_
    rw [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
    exact hinv g _ hk
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ?_ hsub)
  exact (hOopen.preimage continuous_subtype_val).mem_nhds (by simpa using hO1)

end RS11SC

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm
open IsDedekindDomain
open scoped NNReal

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ)
      (_hn : ∀ v ∈ S, 0 < n v)
      (_hνS : ∀ v ∈ S, ∀ t : (v.adicCompletion K)ˣ,
        Valued.v ((t : v.adicCompletion K) - 1) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          localChar ν v t = 1)
      (_hνout : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ν v),
    ∃ Ψ : AdelicGL2 (𝓞 K) K → ℂ,
      (∀ g g' : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g' → Ψ g = Ψ g') ∧
      (∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
        glArch (𝓞 K) K b = 1 →
          Ψ (b * g) =
            ((etaFst 1 α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) *
              ((etaSnd ν α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * Ψ g) ∧
      Continuous Ψ ∧ IsKfSmooth K Ψ ∧
      (∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        Ψ (g * k) = Ψ g) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          Ψ (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Ψ g) ∧
      (∀ g : AdelicGL2 (𝓞 K) K,
        (∃ v ∈ S, ¬ Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        Ψ g = 0) ∧
      (∀ (k : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n v : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          Ψ k = ∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) := by
  intro α hα s ν hνc S n hn hνS hνout
  obtain ⟨-, -, hflat⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow K
  refine ⟨RS11SC.psi S n s ν, fun g g' h => RS11SC.psi_eq_of_glFin_eq S n s ν h,
    fun b hb g hba => RS11SC.psi_borel_mul S n s ν α hα (hflat hα s) hb hba g,
    RS11SC.continuous_psi S n s ν hn hνc hνS hνout, RS11SC.isKfSmooth_psi S n s ν hn hνc hνS hνout,
    fun g k _ hki hkc => RS11SC.psi_mul_of_cong' S n s ν hn hνc hνS hνout g k hki hkc,
    fun v hv kv g => RS11SC.psi_mul_placeEmbed S n s ν hνc hνout hv kv g,
    fun g hg => RS11SC.psi_eq_zero_of_exists S n s ν hg,
    fun k d hki hd hsupp => RS11SC.psi_eq_prod S n s ν hνc hνout k d hki hd hsupp⟩

end S_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level
end P2MW
export P2MW.S_AutomorphicForm_exists_isKfSmooth_eq_prod_localChar_of_borel_fin_of_level (solution)
