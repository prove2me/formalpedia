-- Prove2me | Definitions.Def_ChapterDegKatoEsa
-- name    : ChapterDegKatoEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-05T18:02:21.825479+00:00
-- url     : https://prove2.me/theorems/217ec507-8e65-47bb-b5b2-0a635e10577b
-- title:
--   ChapterDegKatoEsa
-- statement:
--   ChapterDegKatoEsa

import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterDegEnergyEstimate
import Definitions.Def_ChapterMollifierL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Theorems.Thm_BookProof_MollifierL2_tendsto_mollify_L2
import Theorems.Thm_BookProof_DegEnergy_contDiff_cx
import Theorems.Thm_BookProof_DegEnergy_energy_bound
import Theorems.Thm_BookProof_DegEnergy_hasCompactSupport_cx
import Theorems.Thm_BookProof_DegEnergy_lapCS_cx_conj
import Theorems.Thm_BookProof_DegEnergy_norm_cx
import Theorems.Thm_BookProof_ConvolutionCalc_cnv_apply
import Theorems.Thm_BookProof_ConvolutionCalc_contDiff_cnv
import Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_dcoord
import Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_finsetSum
import Theorems.Thm_BookProof_ConvolutionCalc_integrable_cnv_integrand
import Theorems.Thm_BookProof_ConvolutionCalc_lapCS_cnv
import Theorems.Thm_BookProof_ConvolutionCalc_lapCS_reflect
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe


/-!
# Kato's theorem for `−Δ_S + W`, `W ≥ 1`, on the compactly supported smooth core

This module proves the analytic input that the Faris–Lavine criterion cannot supply: a
Schrödinger operator with an arbitrary smooth potential bounded below, and with a kinetic
term that differentiates only a subset `S` of the coordinates, is **essentially
self-adjoint on the compactly supported smooth core of `L²(ℝᵈ)`**.

## The argument

Let `w ∈ L²` be a deficiency vector at a purely imaginary `z`:
`⟪(−Δ_S + W)φ, w⟫ = z ⟪φ, w⟫` for every `φ ∈ C_c^∞(ℝᵈ)`.  No elliptic regularity is used.
Instead one *mollifies*: for a smooth compactly supported mollifier `ρ_ε` the function
`w_ε = w ∗ ρ_ε` is smooth, and testing the deficiency equation against the (compactly
supported, smooth) translate `y ↦ ρ_ε(x − y)` gives the *pointwise* identity

`Δ_S w_ε = ((W − z̄) w) ∗ ρ_ε`.

Testing this identity against `χ_R² w̄_ε`, with `χ_R` a cut-off equal to `1` on the ball of
radius `R`, and integrating by parts once in each direction of `S`, gives the energy
inequality

`∫ χ_R² |∇_S w_ε|² + Re ∫ χ_R² w̄_ε ((W − z̄)w) ∗ ρ_ε = −2 Re ∫ χ_R w̄_ε ∇χ_R · ∇w_ε`,

whose right-hand side is absorbed by Young's inequality into
`½ ∫ χ_R²|∇_S w_ε|² + 2∫|∇_Sχ_R|²|w_ε|² ≤ ½ ∫ χ_R²|∇_S w_ε|² + (2C²/R²)‖w‖²`.
Letting `ε → 0` at fixed `R` (all the integrands converge in `L¹` of the compact set
`supp χ_R`) and using `Re z = 0` leaves

`∫ χ_R² W |w|² ≤ (2C²/R²) ‖w‖²`,

and `W ≥ 1` then forces `∫_{‖x‖ ≤ R} |w|² ≤ (2C²/R²)‖w‖²`.  Letting `R → ∞` gives `w = 0`.
-/

namespace BookProof.DegKatoEsa

open MeasureTheory SchwartzMap MvPolynomial Filter Topology
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc BookProof.DegEnergy BookProof.MollifierL2

noncomputable section

variable {d : ℕ}

/-! ## 1. The deficiency equation in test-function form -/

/-- A compactly supported smooth function, as an element of the compactly supported core. -/
def ccOf {φ : Vd d → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) : ccDomain (Vd d) :=
  ccEquiv (Vd d) ⟨hφc.toSchwartzMap hφ, hφc⟩

/-- The `L²` pairing against a vector with a known representative, as an integral. -/
theorem inner_ae_eq (a : L2d d) (g : Vd d → ℂ) (hg : (a : Vd d → ℂ) =ᵐ[volume] g)
    (u : L2d d) : (inner ℂ a u : ℂ) = ∫ x, (starRingEnd ℂ) (g x) * (u : Vd d → ℂ) x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg] with x hx
  rw [← hx]
  simp [RCLike.inner_apply, mul_comm]

/-- **The deficiency equation, tested against a compactly supported smooth function.** -/
theorem weak_form (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (S : Finset (Fin d)) {z : ℂ} {u : L2d d}
    (hu : ∀ v : ccDomain (Vd d), (inner ℂ (ccHamS W hWs S v) u : ℂ)
      = z * inner ℂ ((v : L2d d)) u)
    {φ : Vd d → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ y, (starRingEnd ℂ) (-lapCS S φ y + ((W y : ℝ) : ℂ) * φ y) * (u : Vd d → ℂ) y
      = z * ∫ y, (starRingEnd ℂ) (φ y) * (u : Vd d → ℂ) y := by
  have h := hu (ccOf hφ hφc)
  rw [show (ccOf hφ hφc) = ccEquiv (Vd d) ⟨hφc.toSchwartzMap hφ, hφc⟩ from rfl] at h
  rw [inner_ae_eq _ _ (ccHamS_coeFn W hWs S ⟨hφc.toSchwartzMap hφ, hφc⟩) u, ccEquiv_coe,
    inner_ae_eq _ _ ((hφc.toSchwartzMap hφ).coeFn_toLp 2 (volume : Measure (Vd d))) u] at h
  exact h

/-! ## 2. The mollified deficiency vector solves the equation pointwise -/

/-- **The mollification of a deficiency vector satisfies `Δ_S v = (W u) ∗ ρ − z v`
pointwise.**  This is the step that replaces elliptic regularity. -/
theorem mollified_identity (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (S : Finset (Fin d)) {z : ℂ} {u : L2d d}
    (hu : ∀ v : ccDomain (Vd d), (inner ℂ (ccHamS W hWs S v) u : ℂ)
      = z * inner ℂ ((v : L2d d)) u)
    {ρ : Vd d → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (x : Vd d) :
    lapCS S (cnv ((u : Vd d → ℂ)) (cx ρ)) x
      = cnv (fun y => ((W y : ℝ) : ℂ) * (u : Vd d → ℂ) y) (cx ρ) x
        - z * cnv ((u : Vd d → ℂ)) (cx ρ) x := by
  have hUloc : LocallyIntegrable ((u : Vd d → ℂ)) (volume : Measure (Vd d)) :=
    (Lp.memLp u).locallyIntegrable one_le_two
  have hWUloc : LocallyIntegrable (fun y => ((W y : ℝ) : ℂ) * (u : Vd d → ℂ) y)
      (volume : Measure (Vd d)) := by
    have h1 : LocallyIntegrable (fun y => (u : Vd d → ℂ) y * ((W y : ℝ) : ℂ))
        (volume : Measure (Vd d)) := by
      rw [← locallyIntegrableOn_univ] at hUloc ⊢
      exact hUloc.mul_continuousOn
        (Complex.continuous_ofReal.comp hWs.continuous).continuousOn
        (IsClosed.isLocallyClosed isClosed_univ)
    have heq : (fun y => ((W y : ℝ) : ℂ) * (u : Vd d → ℂ) y)
        = fun y => (u : Vd d → ℂ) y * ((W y : ℝ) : ℂ) := by
      funext y
      ring
    rw [heq]
    exact h1
  have hρC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx ρ) := contDiff_cx hρ
  have hρCc : HasCompactSupport (cx ρ) := hasCompactSupport_cx hρc
  have hLρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lapCS S (cx ρ)) :=
    ContDiff.sum fun j _ => contDiff_dcoord (contDiff_dcoord hρC j) j
  have hLρc : HasCompactSupport (lapCS S (cx ρ)) :=
    hasCompactSupport_finsetSum S fun j _ =>
      hasCompactSupport_dcoord (hasCompactSupport_dcoord hρCc j) j
  -- the test function
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => cx ρ (x - y)) :=
    hρC.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun y => cx ρ (x - y)) :=
    hρCc.comp_homeomorph (Homeomorph.subLeft x)
  have hw := weak_form W hWs S hu hφ hφc
  have hI1 : Integrable (fun y => (u : Vd d → ℂ) y * lapCS S (cx ρ) (x - y))
      (volume : Measure (Vd d)) := integrable_cnv_integrand hUloc hLρ.continuous hLρc x
  have hI2 : Integrable (fun y => (((W y : ℝ) : ℂ) * (u : Vd d → ℂ) y) * cx ρ (x - y))
      (volume : Measure (Vd d)) := integrable_cnv_integrand hWUloc hρC.continuous hρCc x
  -- rewrite the two integrands
  have hpt : ∀ y : Vd d, (starRingEnd ℂ) (-lapCS S (fun y => cx ρ (x - y)) y
        + ((W y : ℝ) : ℂ) * cx ρ (x - y)) * (u : Vd d → ℂ) y
      = (((W y : ℝ) : ℂ) * (u : Vd d → ℂ) y) * cx ρ (x - y)
        - (u : Vd d → ℂ) y * lapCS S (cx ρ) (x - y) := by
    intro y
    rw [lapCS_reflect hρC x S y]
    simp only [map_add, map_neg, map_mul, Complex.conj_ofReal, lapCS_cx_conj hρ S (x - y)]
    have hcxr : (starRingEnd ℂ) (cx ρ (x - y)) = cx ρ (x - y) := by simp [cx]
    rw [hcxr]
    ring
  have hpt2 : ∀ y : Vd d, (starRingEnd ℂ) (cx ρ (x - y)) * (u : Vd d → ℂ) y
      = (u : Vd d → ℂ) y * cx ρ (x - y) := by
    intro y
    have hcxr : (starRingEnd ℂ) (cx ρ (x - y)) = cx ρ (x - y) := by simp [cx]
    rw [hcxr]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_congr_ae (Filter.Eventually.of_forall hpt2), integral_sub hI2 hI1] at hw
  have hcnv : cnv ((u : Vd d → ℂ)) (lapCS S (cx ρ)) x = lapCS S (cnv ((u : Vd d → ℂ)) (cx ρ)) x :=
    (lapCS_cnv hUloc hρC hρCc S x).symm
  have hw' : cnv (fun y => ((W y : ℝ) : ℂ) * (u : Vd d → ℂ) y) (cx ρ) x
      - cnv ((u : Vd d → ℂ)) (lapCS S (cx ρ)) x
      = z * cnv ((u : Vd d → ℂ)) (cx ρ) x := hw
  rw [hcnv] at hw'
  linear_combination -hw'

/-! ## 3. A mollifier sequence -/

/-- The bump of radius `1/(n+1)` underlying the `n`-th mollifier. -/
def molBump (d : ℕ) (n : ℕ) : ContDiffBump (0 : Vd d) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    nlinarith

/-- The `n`-th mollifier: a smooth probability density supported in the ball of radius
`1/(n+1)`. -/
def mol (d : ℕ) (n : ℕ) : Vd d → ℝ := (molBump d n).normed volume

theorem contDiff_mol (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mol d n) :=
  (molBump d n).contDiff_normed

theorem hasCompactSupport_mol (n : ℕ) : HasCompactSupport (mol d n) :=
  (molBump d n).hasCompactSupport_normed

theorem mol_nonneg (n : ℕ) (y : Vd d) : 0 ≤ mol d n y := (molBump d n).nonneg_normed y

theorem integral_mol (n : ℕ) : ∫ y, mol d n y = 1 := (molBump d n).integral_normed

theorem norm_lt_of_mol_ne_zero {n : ℕ} {y : Vd d} (hy : mol d n y ≠ 0) :
    ‖y‖ < 1 / ((n : ℝ) + 1) := by
  have h : y ∈ Function.support (mol d n) := hy
  rw [mol, (molBump d n).support_normed_eq] at h
  simp only [Metric.mem_ball, dist_zero_right] at h
  exact h

theorem lintegral_mol (n : ℕ) : ∫⁻ y, ENNReal.ofReal (mol d n y) = 1 := by
  have hint : Integrable (mol d n) (volume : Measure (Vd d)) :=
    (contDiff_mol n).continuous.integrable_of_hasCompactSupport (hasCompactSupport_mol n)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => mol_nonneg n y), integral_mol]
  simp

/-- The mollification, minus the function, as an average of translates. -/
theorem integral_mol_smul_sub {f : Vd d → ℂ} (hf : LocallyIntegrable f (volume : Measure (Vd d)))
    (n : ℕ) (x : Vd d) :
    ∫ y, mol d n y • (f (x - y) - f x) = cnv f (cx (mol d n)) x - f x := by
  have hρC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx (mol d n)) := contDiff_cx (contDiff_mol n)
  have hρc : HasCompactSupport (cx (mol d n)) := hasCompactSupport_cx (hasCompactSupport_mol n)
  have hex : ConvolutionExistsAt f (cx (mol d n)) x (ContinuousLinearMap.mul ℝ ℂ) volume :=
    hρc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ) hf hρC.continuous x
  have hsw : Integrable (fun t => f (x - t) * cx (mol d n) t) (volume : Measure (Vd d)) :=
    hex.integrable_swap
  have hcnv : cnv f (cx (mol d n)) x = ∫ t, f (x - t) * cx (mol d n) t := by
    rw [cnv, convolution_eq_swap]
    rfl
  have hint2 : Integrable (fun t => cx (mol d n) t * f x) (volume : Measure (Vd d)) :=
    (hρC.continuous.integrable_of_hasCompactSupport hρc).mul_const _
  have hpt : ∀ y, mol d n y • (f (x - y) - f x)
      = f (x - y) * cx (mol d n) y - cx (mol d n) y * f x := by
    intro y
    simp only [cx, Complex.real_smul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hsw hint2,
    integral_mul_const, hcnv]
  have h1 : ∫ t, cx (mol d n) t = 1 := by
    simp only [cx]
    rw [integral_complex_ofReal, integral_mol]
    simp
  rw [h1, one_mul]

/-- **Mollification converges in `L²`** along the mollifier sequence. -/
theorem tendsto_cnv_mol {f : Vd d → ℂ} (hf : StronglyMeasurable f)
    (hf2 : MemLp f 2 (volume : Measure (Vd d))) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => cnv f (cx (mol d n)) x - f x) 2 volume) atTop
      (𝓝 0) := by
  have hloc : LocallyIntegrable f (volume : Measure (Vd d)) := hf2.locallyIntegrable one_le_two
  have h := tendsto_mollify_L2 (μ := (volume : Measure (Vd d))) (l := atTop) f hf hf2
    (fun n => mol d n) (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n y => mol_nonneg n y)
    (fun n => (contDiff_mol n).continuous.measurable) (fun n => lintegral_mol n)
    (fun n y hy => norm_lt_of_mol_ne_zero hy) tendsto_one_div_add_atTop_nhds_zero_nat
  refine h.congr fun n => ?_
  congr 1
  funext x
  exact integral_mol_smul_sub hloc n x

/-! ## 4. `L²` bookkeeping -/

/-- A bounded continuous multiple of a square-integrable function is square-integrable. -/
theorem memLp_bdd_mul {b f : Vd d → ℂ} (hb : Continuous b) {B : ℝ} (hbB : ∀ x, ‖b x‖ ≤ B)
    (hf : MemLp f 2 (volume : Measure (Vd d))) :
    MemLp (fun x => b x * f x) 2 (volume : Measure (Vd d)) := by
  refine MemLp.of_le (hf.const_mul (B : ℂ)) (hb.aestronglyMeasurable.mul hf.1) ?_
  filter_upwards with x
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbB x)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hB]
  exact mul_le_mul_of_nonneg_right (hbB x) (norm_nonneg _)

/-- The `L²` inner product of two `toLp`'s, as an integral. -/
theorem inner_toLp {f g : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d)))
    (hg : MemLp g 2 (volume : Measure (Vd d))) :
    (inner ℂ (hf.toLp f) (hg.toLp g) : ℂ) = ∫ x, (starRingEnd ℂ) (f x) * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

/-- The squared `L²` norm of a `toLp`, as an integral. -/
theorem norm_toLp_sq {f : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d))) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := inner_toLp hf hf
  have hpt : ∀ x, (starRingEnd ℂ) (f x) * f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.conj_mul']
    norm_cast
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal] at h
  have h2 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h2
  rw [← h2, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/-- Convergence in `L²` from an `eLpNorm` majorant that tends to zero. -/
theorem tendsto_toLp_of_le {f : ℕ → Vd d → ℂ} {g : Vd d → ℂ}
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure (Vd d))) (hg : MemLp g 2 (volume : Measure (Vd d)))
    {e : ℕ → ENNReal} (he : Tendsto e atTop (𝓝 0)) (B : ℝ)
    (hle : ∀ n, eLpNorm (f n - g) 2 (volume : Measure (Vd d)) ≤ ENNReal.ofReal B * e n) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  have h2 : Tendsto (fun n => ENNReal.ofReal B * e n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul he (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le) hle

/-! ## 5. The cut-off estimate for a deficiency vector -/

set_option maxHeartbeats 1000000 in
-- the limit argument assembles many integrability and convergence side conditions
/-- **The cut-off estimate.**  If `u` is a deficiency vector of `−Δ_S + W` (`W ≥ 1`) at a
purely imaginary `z`, and `χ` is a real smooth cut-off with `|χ| ≤ 1` and `|∂ⱼχ| ≤ B`, then
`‖χu‖² ≤ 2 |S| B² ‖u‖²`. -/
theorem kato_cutoff_bound (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hW1 : ∀ x, 1 ≤ W x) (S : Finset (Fin d)) {z : ℂ} (hz : z.re = 0) {u : L2d d}
    (hu : ∀ v : ccDomain (Vd d), (inner ℂ (ccHamS W hWs S v) u : ℂ)
      = z * inner ℂ ((v : L2d d)) u)
    {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ1 : ∀ x, |χ x| ≤ 1) {B : ℝ} (hdχ : ∀ j x, ‖dcoord j (cx χ) x‖ ≤ B)
    (hA : MemLp (fun x => cx χ x * (u : Vd d → ℂ) x) 2 (volume : Measure (Vd d))) :
    ‖hA.toLp _‖ ^ 2 ≤ 2 * S.card * B ^ 2 * ‖u‖ ^ 2 := by
  classical
  set uf : Vd d → ℂ := (u : Vd d → ℂ) with huf
  have hu2 : MemLp uf 2 (volume : Measure (Vd d)) := Lp.memLp u
  have hum : StronglyMeasurable uf := Lp.stronglyMeasurable u
  have hUloc : LocallyIntegrable uf (volume : Measure (Vd d)) := hu2.locallyIntegrable one_le_two
  have hWc : Continuous W := hWs.continuous
  have hWcC : Continuous (fun y => ((W y : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hWc
  have hWUloc : LocallyIntegrable (fun y => ((W y : ℝ) : ℂ) * uf y)
      (volume : Measure (Vd d)) := by
    have h1 : LocallyIntegrable (fun y => uf y * ((W y : ℝ) : ℂ)) (volume : Measure (Vd d)) := by
      rw [← locallyIntegrableOn_univ] at hUloc ⊢
      exact hUloc.mul_continuousOn hWcC.continuousOn (IsClosed.isLocallyClosed isClosed_univ)
    have heq : (fun y => ((W y : ℝ) : ℂ) * uf y) = fun y => uf y * ((W y : ℝ) : ℂ) := by
      funext y
      ring
    rw [heq]
    exact h1
  -- the compact sets and the localised potential term
  set K : Set (Vd d) := tsupport χ with hKdef
  have hK : IsCompact K := hχc
  set K₁ : Set (Vd d) := Metric.cthickening 1 K with hK₁def
  have hK₁ : IsCompact K₁ := hK.cthickening
  obtain ⟨M, hM⟩ := hK₁.exists_bound_of_continuousOn hWc.continuousOn
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set fK : Vd d → ℂ := K₁.indicator (fun y => ((W y : ℝ) : ℂ) * uf y) with hfKdef
  have hfKm : StronglyMeasurable fK :=
    (hWcC.stronglyMeasurable.mul hum).indicator hK₁.isClosed.measurableSet
  have hfK2 : MemLp fK 2 (volume : Measure (Vd d)) := by
    refine MemLp.of_le (hu2.const_mul (M' : ℂ)) hfKm.aestronglyMeasurable ?_
    filter_upwards with y
    by_cases hy : y ∈ K₁
    · rw [hfKdef, Set.indicator_of_mem hy, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg hM'0]
      exact mul_le_mul_of_nonneg_right ((hM y hy).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hfKdef, Set.indicator_of_notMem hy, norm_zero]
      exact norm_nonneg _
  have hχ0 : ∀ x, x ∉ K → χ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hWloc : ∀ x, x ∈ K → fK x = ((W x : ℝ) : ℂ) * uf x := fun x hx => by
    rw [hfKdef, Set.indicator_of_mem (Metric.self_subset_cthickening K hx)]
  -- the mollified sequences
  set v : ℕ → Vd d → ℂ := fun n => cnv uf (cx (mol d n)) with hvdef
  set G : ℕ → Vd d → ℂ := fun n => cnv (fun y => ((W y : ℝ) : ℂ) * uf y) (cx (mol d n))
    with hGdef
  have hvs : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v n) := fun n =>
    contDiff_cnv hUloc (contDiff_cx (contDiff_mol n))
      (hasCompactSupport_cx (hasCompactSupport_mol n))
  have hGc : ∀ n, Continuous (G n) := fun n =>
    (contDiff_cnv hWUloc (contDiff_cx (contDiff_mol n))
      (hasCompactSupport_cx (hasCompactSupport_mol n))).continuous
  have hGloc : ∀ n x, x ∈ K → G n x = cnv fK (cx (mol d n)) x := by
    intro n x hx
    simp only [hGdef, cnv_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : mol d n (x - y) = 0
    · simp [cx, hy]
    · have hlt := norm_lt_of_mol_ne_zero hy
      have hle1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hy1 : y ∈ K₁ := Metric.mem_cthickening_of_dist_le y x 1 K hx (by
        rw [dist_comm, dist_eq_norm]
        exact hlt.le.trans hle1)
      simp only [hfKdef, Set.indicator_of_mem hy1]
  -- the energy inequality for each mollification
  have henergy : ∀ n, (∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v n x) * G n x).re
      ≤ 2 * ∑ j ∈ S, ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v n x‖ ^ 2 := fun n =>
    energy_bound S hz (hvs n) (hGc n)
      (fun x => mollified_identity W hWs S hu (contDiff_mol n) (hasCompactSupport_mol n) x)
      hχ hχc
  -- the `L²` vectors
  have hcxs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cx χ) := contDiff_cx hχ
  have hcxc : Continuous (cx χ) := hcxs.continuous
  have hcxcs : HasCompactSupport (cx χ) := hasCompactSupport_cx hχc
  have hcxb : ∀ x, ‖cx χ x‖ ≤ 1 := fun x => by rw [norm_cx]; exact hχ1 x
  have hdc : ∀ j, Continuous (dcoord j (cx χ)) := fun j => (contDiff_dcoord hcxs j).continuous
  have hA2 : ∀ n, MemLp (fun x => cx χ x * v n x) 2 (volume : Measure (Vd d)) := fun n =>
    (hcxc.mul (hvs n).continuous).memLp_of_hasCompactSupport (hcxcs.mul_right)
  have hB2 : ∀ n, MemLp (fun x => cx χ x * G n x) 2 (volume : Measure (Vd d)) := fun n =>
    (hcxc.mul (hGc n)).memLp_of_hasCompactSupport (hcxcs.mul_right)
  have hE2 : ∀ j n, MemLp (fun x => dcoord j (cx χ) x * v n x) 2 (volume : Measure (Vd d)) :=
    fun j n => ((hdc j).mul (hvs n).continuous).memLp_of_hasCompactSupport
      ((hasCompactSupport_dcoord hcxcs j).mul_right)
  have hBl : MemLp (fun x => cx χ x * fK x) 2 (volume : Measure (Vd d)) :=
    memLp_bdd_mul hcxc hcxb hfK2
  have hEl : ∀ j, MemLp (fun x => dcoord j (cx χ) x * uf x) 2 (volume : Measure (Vd d)) :=
    fun j => memLp_bdd_mul (hdc j) (hdχ j) hu2
  -- convergence of the mollifications
  have hconvU := tendsto_cnv_mol (d := d) hum hu2
  have hconvF := tendsto_cnv_mol (d := d) hfKm hfK2
  have tA : Tendsto (fun n => (hA2 n).toLp _) atTop (𝓝 (hA.toLp _)) := by
    refine tendsto_toLp_of_le hA2 hA hconvU 1 fun n => ?_
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall fun x => ?_) 2
    simp only [Pi.sub_apply]
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hcxb x) (norm_nonneg _)
  have tB : Tendsto (fun n => (hB2 n).toLp _) atTop (𝓝 (hBl.toLp _)) := by
    refine tendsto_toLp_of_le hB2 hBl hconvF 1 fun n => ?_
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall fun x => ?_) 2
    simp only [Pi.sub_apply]
    rw [← mul_sub, norm_mul]
    by_cases hx : x ∈ K
    · rw [hGloc n x hx]
      exact mul_le_mul_of_nonneg_right (hcxb x) (norm_nonneg _)
    · have h0 : cx χ x = 0 := by simp [cx, hχ0 x hx]
      rw [h0, norm_zero, zero_mul]
      positivity
  have tE : ∀ j, Tendsto (fun n => (hE2 j n).toLp _) atTop (𝓝 ((hEl j).toLp _)) := by
    intro j
    refine tendsto_toLp_of_le (hE2 j) (hEl j) hconvU B fun n => ?_
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall fun x => ?_) 2
    simp only [Pi.sub_apply]
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hdχ j x) (norm_nonneg _)
  -- the energy inequality in `L²` form
  have hcxconj : ∀ x, (starRingEnd ℂ) (cx χ x) = cx χ x := fun x => by simp [cx]
  have hinnerN : ∀ n, (inner ℂ ((hA2 n).toLp _) ((hB2 n).toLp _) : ℂ)
      = ∫ x, cx χ x ^ 2 * (starRingEnd ℂ) (v n x) * G n x := by
    intro n
    rw [inner_toLp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, hcxconj]
    ring
  have hnormE : ∀ j n, ‖(hE2 j n).toLp _‖ ^ 2
      = ∫ x, ‖dcoord j (cx χ) x‖ ^ 2 * ‖v n x‖ ^ 2 := by
    intro j n
    rw [norm_toLp_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, mul_pow]
  have hineqN : ∀ n, (inner ℂ ((hA2 n).toLp _) ((hB2 n).toLp _) : ℂ).re
      ≤ 2 * ∑ j ∈ S, ‖(hE2 j n).toLp _‖ ^ 2 := by
    intro n
    rw [hinnerN n]
    simp only [hnormE]
    exact henergy n
  -- pass to the limit
  have hlimL : Tendsto (fun n => (inner ℂ ((hA2 n).toLp _) ((hB2 n).toLp _) : ℂ).re) atTop
      (𝓝 (inner ℂ (hA.toLp _) (hBl.toLp _) : ℂ).re) :=
    (Complex.continuous_re.tendsto _).comp (tA.inner tB)
  have hlimR : Tendsto (fun n => 2 * ∑ j ∈ S, ‖(hE2 j n).toLp _‖ ^ 2) atTop
      (𝓝 (2 * ∑ j ∈ S, ‖(hEl j).toLp _‖ ^ 2)) :=
    (tendsto_finset_sum S fun j _ => ((tE j).norm).pow 2).const_mul 2
  have hlim : (inner ℂ (hA.toLp _) (hBl.toLp _) : ℂ).re ≤ 2 * ∑ j ∈ S, ‖(hEl j).toLp _‖ ^ 2 :=
    le_of_tendsto_of_tendsto' hlimL hlimR hineqN
  -- the gradient terms are bounded by `B ‖u‖`
  have hEbound : ∀ j, ‖(hEl j).toLp _‖ ≤ B * ‖u‖ := by
    intro j
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(hEl j).coeFn_toLp] with x hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hdχ j x) (norm_nonneg _)
  -- the potential term dominates the mass
  have hmass : ‖hA.toLp _‖ ^ 2 ≤ (inner ℂ (hA.toLp _) (hBl.toLp _) : ℂ).re := by
    have hdiff : (inner ℂ (hA.toLp _) (hBl.toLp _) : ℂ) - inner ℂ (hA.toLp _) (hA.toLp _)
        = ((∫ x, (χ x) ^ 2 * (W x - 1) * ‖uf x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_sub_right, ← MemLp.toLp_sub, inner_toLp, ← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      by_cases hx : x ∈ K
      · rw [hWloc x hx]
        have hn : (starRingEnd ℂ) (uf x) * uf x = ((‖uf x‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.conj_mul']
          norm_cast
        simp only [map_mul, cx, Complex.conj_ofReal]
        push_cast at hn ⊢
        linear_combination ((χ x : ℂ) ^ 2 * ((W x : ℂ) - 1)) * hn
      · simp [cx, hχ0 x hx]
    have hnn : 0 ≤ ∫ x, (χ x) ^ 2 * (W x - 1) * ‖uf x‖ ^ 2 :=
      integral_nonneg fun x => by
        have := hW1 x
        have h1 : 0 ≤ W x - 1 := by linarith
        positivity
    have h2 := congrArg Complex.re hdiff
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    have h3 : (inner ℂ (hA.toLp _) (hA.toLp _) : ℂ).re = ‖hA.toLp _‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      rfl
    linarith
  -- conclusion
  have hsum : 2 * ∑ j ∈ S, ‖(hEl j).toLp _‖ ^ 2 ≤ 2 * S.card * B ^ 2 * ‖u‖ ^ 2 := by
    have h1 : ∑ j ∈ S, ‖(hEl j).toLp _‖ ^ 2 ≤ ∑ j ∈ S, (B * ‖u‖) ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hEbound j) 2
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    nlinarith
  linarith

/-! ## 6. The deficiency spaces are trivial -/

/-- The cut-off estimate for the scaled cut-off `χ_N`, combined with the `L²` tail. -/
theorem norm_le_cut_tail (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hW1 : ∀ x, 1 ≤ W x) (S : Finset (Fin d)) {z : ℂ} (hz : z.re = 0) {u : L2d d}
    (hu : ∀ v : ccDomain (Vd d), (inner ℂ (ccHamS W hWs S v) u : ℂ)
      = z * inner ℂ ((v : L2d d)) u)
    {C : ℝ} (hC0 : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N)
    (hdχ : ∀ j x, ‖dcoord j (cx (cut d (N : ℝ))) x‖ ≤ C / N) :
    ‖u‖ ≤ Real.sqrt (2 * S.card) * (C / N) * ‖u‖
      + (eLpNorm (({z : Vd d | ‖z‖ ≤ (N : ℝ)}ᶜ).indicator (fun x => ‖(u : Vd d → ℂ) x‖)) 2
          (volume : Measure (Vd d))).toReal := by
  have hR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hR0 : (0 : ℝ) < N := by linarith
  have hu2 : MemLp (u : Vd d → ℂ) 2 (volume : Measure (Vd d)) := Lp.memLp u
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut d (N : ℝ)) := contDiff_cut (N : ℝ)
  have hχc : HasCompactSupport (cut d (N : ℝ)) := hasCompactSupport_cut hR0
  have hχI : ∀ x, cut d (N : ℝ) x ∈ Set.Icc (0 : ℝ) 1 := fun x => cut_mem_Icc x
  have hχ1 : ∀ x, |cut d (N : ℝ) x| ≤ 1 := fun x => by
    rw [abs_le]
    constructor <;> linarith [(hχI x).1, (hχI x).2]
  have hA : MemLp (fun x => cx (cut d (N : ℝ)) x * (u : Vd d → ℂ) x) 2
      (volume : Measure (Vd d)) :=
    memLp_bdd_mul (contDiff_cx hχ).continuous (fun x => by rw [norm_cx]; exact hχ1 x) hu2
  have hbd := kato_cutoff_bound W hWs hW1 S hz hu hχ hχc hχ1 hdχ hA
  have hAn : ‖hA.toLp _‖ ≤ Real.sqrt (2 * S.card) * (C / N) * ‖u‖ := by
    have hsq : 2 * (S.card : ℝ) * (C / N) ^ 2 * ‖u‖ ^ 2
        = (Real.sqrt (2 * S.card) * (C / N) * ‖u‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsq] at hbd
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hbd
  have htail : ‖u - hA.toLp _‖ ≤ (eLpNorm (({z : Vd d | ‖z‖ ≤ (N : ℝ)}ᶜ).indicator
      (fun x => ‖(u : Vd d → ℂ) x‖)) 2 (volume : Measure (Vd d))).toReal := by
    refine norm_le_tailNorm hu2.norm ?_
    filter_upwards [Lp.coeFn_sub u (hA.toLp _), hA.coeFn_toLp] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
    by_cases hx : ‖x‖ ≤ (N : ℝ)
    · have h1' : cx (cut d (N : ℝ)) x = 1 := by simp [cx, cut_eq_one hR0 hx]
      rw [h1', one_mul, sub_self, norm_zero]
      exact norm_nonneg _
    · have hmem : x ∈ ({z : Vd d | ‖z‖ ≤ (N : ℝ)}ᶜ) := hx
      rw [Set.indicator_of_mem hmem, norm_norm]
      have hfac : (u : Vd d → ℂ) x - cx (cut d (N : ℝ)) x * (u : Vd d → ℂ) x
          = ((1 - cut d (N : ℝ) x : ℝ) : ℂ) * (u : Vd d → ℂ) x := by
        simp only [cx]
        push_cast
        ring
      rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [(hχI x).2])]
      have : 1 - cut d (N : ℝ) x ≤ 1 := by linarith [(hχI x).1]
      nlinarith [norm_nonneg ((u : Vd d → ℂ) x)]
  calc ‖u‖ = ‖hA.toLp _ + (u - hA.toLp _)‖ := by rw [add_sub_cancel]
    _ ≤ ‖hA.toLp _‖ + ‖u - hA.toLp _‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hAn htail

/-- **The deficiency spaces of `−Δ_S + W` on the compactly supported smooth core are
trivial**, for every smooth potential `W ≥ 1` and every purely imaginary `z`. -/
theorem deficiencyTrivialAt_ccHamS (W : Vd d → ℝ)
    (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hW1 : ∀ x, 1 ≤ W x) (S : Finset (Fin d))
    {z : ℂ} (hz : z.re = 0) :
    DeficiencyTrivialAt (ccDomain (Vd d)) (ccHamS W hWs S) z := by
  intro u hu
  obtain ⟨C, hC0, hCb⟩ := exists_cut_derivative_bounds d
  have hlim : Tendsto (fun N : ℕ => Real.sqrt (2 * S.card) * (C / N) * ‖u‖
      + (eLpNorm (({z : Vd d | ‖z‖ ≤ (N : ℝ)}ᶜ).indicator (fun x => ‖(u : Vd d → ℂ) x‖)) 2
          (volume : Measure (Vd d))).toReal) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.sqrt (2 * S.card) * (C / N) * ‖u‖) atTop (𝓝 0) := by
      have := ((tendsto_const_div_atTop_nhds_zero_nat C).const_mul
        (Real.sqrt (2 * S.card))).mul_const ‖u‖
      simpa using this
    simpa using h1.add (tendsto_tailNorm (Lp.memLp u).norm)
  have hle : ‖u‖ ≤ 0 := ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN =>
    norm_le_cut_tail W hWs hW1 S hz hu hC0 hN fun j x => (hCb N (by exact_mod_cast hN) x).1 j⟩)
  exact norm_le_zero_iff.1 hle

/-- **`−Δ_S + W` is essentially self-adjoint on the compactly supported smooth core of
`L²(ℝᵈ)`** for every smooth potential `W ≥ 1`, with no growth restriction from above and no
ellipticity in the directions outside `S`. -/
theorem ccHamS_esa (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hW1 : ∀ x, 1 ≤ W x) (S : Finset (Fin d)) :
    EssentiallySelfAdjointOn (ccDomain (Vd d)) (ccHamS W hWs S) :=
  ⟨deficiencyTrivialAt_ccHamS W hWs hW1 S (by simp),
   deficiencyTrivialAt_ccHamS W hWs hW1 S (by simp)⟩

end

end BookProof.DegKatoEsa


