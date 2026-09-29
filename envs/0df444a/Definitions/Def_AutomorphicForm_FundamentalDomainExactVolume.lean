-- Prove2me | Definitions.Def_AutomorphicForm_FundamentalDomainExactVolume
-- name    : AutomorphicForm_FundamentalDomainExactVolume
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/24b8952e-7677-52fb-ae4e-01075d7443f8
-- title:
--   Exact hyperbolic volume π/3 of the modular fundamental domain
-- statement:
--   The module computes the hyperbolic volume of the standard fundamental domain $\mathscr{D}=\{z\in\mathfrak H: 1\le \lvert z\rvert^2,\ \lvert \operatorname{Re} z\rvert\le 1/2\}$ for the measure on the upper half-plane with density $y^{-2}$, i.e. the measure characterised by $\mathrm{vol}(S)=\int^-_{\iota(S)}(1/\lVert \operatorname{Im} z\rVert)^2$ over the image of $S$ in $\mathbb C$.
--
--   Two auxiliary objects are defined. The function `lowerArc` sends $x\mapsto\sqrt{1-x^2}$, and is shown to be strictly positive on $[-1/2,1/2]$. The set `regionD` $\subseteq\mathbb R\times\mathbb R$ consists of the pairs $(x,y)$ with $x\in[-1/2,1/2]$ and $\sqrt{1-x^{2}}\le y$; it is measurable, and `image_image_fd` identifies it with the image of $\mathscr{D}$ under the coercion $\mathfrak H\to\mathbb C$ followed by the measurable identification $\mathbb C\simeq\mathbb R\times\mathbb R$. A private density function on $\mathbb R\times\mathbb R$, $(x,y)\mapsto(1/\lVert y\rVert)^2$, carries the weight across this identification.
--
--   The computational ingredients are: $\int^-_{[c,\infty)}y^{-2}\,dy=c^{-1}$ for $c>0$; the slice formula, which evaluates the $y$-integral of the density over `regionD` at fixed $x$ as the indicator of $[-1/2,1/2]$ times $(\sqrt{1-x^2})^{-1}$; and $\int_{-1/2}^{1/2}(1-x^2)^{-1/2}\,dx=\pi/3$, obtained from $\arcsin$ together with $\arcsin(1/2)=\pi/6$.
--
--   The conclusions are $\mathrm{vol}(\mathscr{D})=\pi/3$ in $[0,\infty]$ and as a real number, the consequences that this volume is finite and non-zero, the complex identity $\mathrm{vol}(\mathscr{D})=\pi/3$ after coercion, and the normalisation $(3/\pi)\cdot\mathrm{vol}(\mathscr{D})=1$.
--
--   **Relation to Mathlib.** The domain $\mathscr{D}$ and the measure on $\mathfrak H$ with density $y^{-2}$ (used through Mathlib's expression of that volume as a lower Lebesgue integral over the image in $\mathbb C$) are Mathlib's; the exact evaluation of the volume, and the plane region and arc function used for it, are the project's own.
--
--   **Where it is used.** The constant $3/\pi$ appearing here is the residue at $s=1$ of the Eisenstein scattering quotient $\Lambda(2s-1)/\Lambda(2s)$ studied in the companion module on Eisenstein scattering, and the final identity pins the two against each other; the finiteness and non-vanishing statements sharpen the qualitative bounds obtained earlier for the volume of $\mathscr{D}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_FundamentalDomainExactVolume.lean

import Mathlib
import Definitions.Def_AutomorphicForm_EisensteinScattering
import Definitions.Def_AutomorphicForm_FundamentalDomainVolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Modular Pointwise NNReal ENNReal

noncomputable section

namespace FLT.FundamentalDomainExactVolume

private lemma density_eq_ofReal_rpow {y : ℝ} (hy : 0 < y) :
    (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.norm_eq_abs, abs_of_pos hy,
    show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy.le, Real.rpow_natCast,
    one_div, inv_pow]

theorem setLIntegral_Ici_density {c : ℝ} (hc : 0 < c) :
    ∫⁻ y in Set.Ici c, (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal c⁻¹ := by

  rw [← MeasureTheory.setLIntegral_congr
    (MeasureTheory.Ioi_ae_eq_Ici' (measure_singleton c))]

  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    (fun y (hy : y ∈ Set.Ioi c) => density_eq_ofReal_rpow (hc.trans hy))]

  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hc)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall
        (fun y hy => Real.rpow_nonneg (le_of_lt (hc.trans hy)) _)))]
  rw [integral_Ioi_rpow_of_lt (by norm_num) hc]
  norm_num [Real.rpow_neg_one]

private lemma arcsin_one_half : Real.arcsin (1 / 2) = Real.pi / 6 := by
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

private lemma continuousOn_inv_sqrt :
    ContinuousOn (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹)
      (Set.uIcc (-(1 / 2) : ℝ) (1 / 2)) := by
  apply ContinuousOn.inv₀
  · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      apply sq_le_sq'
      · linarith [hx.1]
      · linarith [hx.2]
    have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)

theorem integral_inv_sqrt_one_sub_sq :
    ∫ x in (-(1 / 2) : ℝ)..(1 / 2), (Real.sqrt (1 - x ^ 2))⁻¹ = Real.pi / 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt Real.arcsin (Real.sqrt (1 - x ^ 2))⁻¹ x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have h₁ : x ≠ -1 := by intro h; rw [h] at hx; have := hx.1; norm_num at this
    have h₂ : x ≠ 1 := by intro h; rw [h] at hx; have := hx.2; norm_num at this
    simpa [one_div] using Real.hasDerivAt_arcsin h₁ h₂
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    continuousOn_inv_sqrt.intervalIntegrable]
  rw [Real.arcsin_neg, arcsin_one_half]
  ring

def lowerArc (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

lemma lowerArc_pos {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) : 0 < lowerArc x := by
  have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    apply sq_le_sq'
    · linarith [hx.1]
    · linarith [hx.2]
  have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  exact Real.sqrt_pos.mpr hpos

def regionD : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) ∧ lowerArc p.1 ≤ p.2}

lemma measurableSet_regionD : MeasurableSet regionD := by
  apply MeasurableSet.inter
  · exact measurable_fst measurableSet_Icc
  · apply measurableSet_le _ measurable_snd
    have hcont : Continuous fun p : ℝ × ℝ => lowerArc p.1 := by
      unfold lowerArc
      fun_prop
    exact hcont.measurable

lemma image_image_fd :
    Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' 𝒟) = regionD := by
  ext p
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨hnorm, hre⟩ := hz
    have him : (0 : ℝ) < z.im := z.im_pos
    have hxIcc : z.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
      rcases abs_le.mp hre with ⟨h₁, h₂⟩
      exact ⟨by linarith, h₂⟩
    refine ⟨?_, ?_⟩
    · simpa only [Complex.measurableEquivRealProd_apply, UpperHalfPlane.coe_re] using hxIcc
    ·
      have hsq : 1 - z.re ^ 2 ≤ z.im ^ 2 := by
        rw [Complex.normSq_apply] at hnorm
        simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hnorm
        nlinarith
      simp only [Complex.measurableEquivRealProd_apply, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      calc lowerArc z.re ≤ Real.sqrt (z.im ^ 2) := Real.sqrt_le_sqrt hsq
        _ = z.im := by rw [Real.sqrt_sq him.le]
  · rintro ⟨hx, hy⟩
    have hypos : (0 : ℝ) < p.2 := lt_of_lt_of_le (lowerArc_pos hx) hy

    have h1x : (0 : ℝ) ≤ 1 - p.1 ^ 2 := by
      have hx2 : p.1 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        apply sq_le_sq'
        · linarith [hx.1]
        · linarith [hx.2]
      nlinarith

    have himC : (0 : ℝ) < (Complex.measurableEquivRealProd.symm p).im := by
      rw [Complex.measurableEquivRealProd_symm_apply]
      exact hypos
    refine ⟨Complex.measurableEquivRealProd.symm p,
      ⟨⟨Complex.measurableEquivRealProd.symm p, himC⟩, ⟨?_, ?_⟩, rfl⟩,
      Complex.measurableEquivRealProd.apply_symm_apply p⟩
    ·
      rw [Complex.normSq_apply]
      show (1 : ℝ) ≤ (Complex.measurableEquivRealProd.symm p).re *
        (Complex.measurableEquivRealProd.symm p).re +
        (Complex.measurableEquivRealProd.symm p).im *
        (Complex.measurableEquivRealProd.symm p).im
      rw [Complex.measurableEquivRealProd_symm_apply]
      have hsq : 1 - p.1 ^ 2 ≤ p.2 ^ 2 := by
        calc 1 - p.1 ^ 2 = lowerArc p.1 ^ 2 := (Real.sq_sqrt h1x).symm
          _ ≤ p.2 ^ 2 := by
              apply pow_le_pow_left₀ (Real.sqrt_nonneg _) hy
      nlinarith
    ·
      show |(⟨Complex.measurableEquivRealProd.symm p, himC⟩ : ℍ).re| ≤ (1 : ℝ) / 2
      have : (⟨Complex.measurableEquivRealProd.symm p, himC⟩ : ℍ).re = p.1 := by
        show (Complex.measurableEquivRealProd.symm p).re = p.1
        rw [Complex.measurableEquivRealProd_symm_apply]
      rw [this]
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩

private def densityP (p : ℝ × ℝ) : ℝ≥0∞ := (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)

private lemma measurable_densityP : Measurable densityP := by
  unfold densityP
  fun_prop

private lemma inner_slice (x : ℝ) :
    ∫⁻ y, regionD.indicator densityP (x, y) =
      Set.indicator (Set.Icc (-(1 / 2) : ℝ) (1 / 2))
        (fun x' => ENNReal.ofReal (lowerArc x')⁻¹) x := by
  by_cases hx : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem hx]
    have hslice : (fun y => regionD.indicator densityP (x, y)) =
        (Set.Ici (lowerArc x)).indicator
          (fun y => (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) := by
      funext y
      by_cases hy : lowerArc x ≤ y
      · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hy),
          Set.indicator_of_mem (show (x, y) ∈ regionD from ⟨hx, hy⟩)]
        rfl
      · rw [Set.indicator_of_notMem (fun h => hy (Set.mem_Ici.mp h)),
          Set.indicator_of_notMem (fun (h : (x, y) ∈ regionD) => hy h.2)]
    rw [hslice, lintegral_indicator measurableSet_Ici]
    exact setLIntegral_Ici_density (lowerArc_pos hx)
  · rw [Set.indicator_of_notMem hx]
    have hzero : (fun y => regionD.indicator densityP (x, y)) = fun _ => 0 := by
      funext y
      exact Set.indicator_of_notMem (fun (h : (x, y) ∈ regionD) => hx h.1) _
    rw [hzero, lintegral_zero]

theorem volume_fd_eq : volume 𝒟 = ENNReal.ofReal (Real.pi / 3) := by

  rw [UpperHalfPlane.volume_eq_lintegral]

  have hfactor : ∀ z : ℂ, (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) =
      densityP (Complex.measurableEquivRealProd z) := fun z => rfl
  simp only [hfactor]
  rw [Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding densityP _]

  rw [image_image_fd]

  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl]
  rw [← lintegral_indicator measurableSet_regionD]
  rw [MeasureTheory.lintegral_prod _
    ((measurable_densityP.indicator measurableSet_regionD).aemeasurable)]

  simp only [inner_slice]

  rw [lintegral_indicator measurableSet_Icc]

  have hcont : ContinuousOn (fun x : ℝ => (lowerArc x)⁻¹)
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    have := continuousOn_inv_sqrt
    rwa [Set.uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at this
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hcont.integrableOn_compact isCompact_Icc)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall
        (fun x _ => inv_nonneg.mpr (Real.sqrt_nonneg _))))]
  congr 1

  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  exact integral_inv_sqrt_one_sub_sq

theorem volume_fd_toReal : (volume 𝒟).toReal = Real.pi / 3 := by
  rw [volume_fd_eq, ENNReal.toReal_ofReal (by positivity)]

theorem gate_volume_lt_top : volume 𝒟 < ⊤ := by
  rw [volume_fd_eq]; exact ENNReal.ofReal_lt_top

theorem gate_volume_ne_zero : volume 𝒟 ≠ 0 := by
  rw [volume_fd_eq]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem residue_mul_volume_fd :
    (3 / (Real.pi : ℂ)) * ((volume 𝒟).toReal : ℂ) = 1 := by
  rw [volume_fd_toReal]
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem volume_fd_toReal_eq_pin : ((volume 𝒟).toReal : ℂ) = (Real.pi : ℂ) / 3 := by
  rw [volume_fd_toReal]; push_cast; ring

end FLT.FundamentalDomainExactVolume

end


