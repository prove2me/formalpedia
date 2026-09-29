-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_adelicHeight_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5bf971e7-b5c0-5f98-94c0-bf68da3cb736

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_adelicHeight_cpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option Elab.async false

section RINHFold_JE2aFlatLocal

set_option autoImplicit false

noncomputable section

open NumberField.AdelicHeight

namespace P6B
namespace JE2aFlat

section Local

variable {K : Type*} [NormedField K]

private theorem coe_mul (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

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

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    (∀ x, 0 < ((α x : ℝˣ) : ℝ)) ∧
    IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) ∧
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ),
      IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s)
        (fun g : AdelicGL2 (𝓞 F) F => ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)) :=
  ⟨fun x => by rw [MonoidHom.coe_toHomUnits]; exact MeasureTheory.distribHaarChar_pos,
    fun x => by rw [MonoidHom.one_apply, Units.val_one, norm_one],
    fun hα s => P6B.JE2aFlat.isInducedSection_flatOne _ hα
      (fun x => NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F x) s⟩

#print axioms solution

end S_AutomorphicForm_isInducedSection_adelicHeight_cpow
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_adelicHeight_cpow (solution)
