-- Prove2me | solution 1 for ArtinPrimitiveRoots.finsum_cexp_trace_sq_div_eq_sqrt_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:14:55.882224+00:00
-- url     : https://prove2.me/submissions/a5e39522-69d2-40be-980f-aed7002280da

import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Mathlib

section
section
/-!
# L3P_Dil: positive dilations of the mixed space

For `x : realSpace K`, `dilV x = mixedSpaceOfRealSpace (expMap x)` has coordinates
`exp(x_w / mult w) > 0`. Multiplication by it is a linear automorphism of determinant
`exp (∑ w, x w)` (for `K` totally complex), and it rescales the Fourier transform.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-- The positive point `(exp(x_w / mult w))_w` of the mixed space. -/
noncomputable def dilV (x : realSpace K) : mixedSpace K := mixedSpaceOfRealSpace (expMap x)

theorem dilV_fst (x : realSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (dilV x).1 w = Real.exp ((w.1.mult : ℝ)⁻¹ * x w) := by
  simp [dilV, mixedSpaceOfRealSpace_apply, expMap_apply]

theorem dilV_snd (x : realSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (dilV x).2 w = (Real.exp ((w.1.mult : ℝ)⁻¹ * x w) : ℂ) := by
  simp [dilV, mixedSpaceOfRealSpace_apply, expMap_apply]

theorem dilV_add (x x' : realSpace K) : dilV (x + x') = dilV x * dilV x' := by
  ext w
  · simp only [dilV_fst, Prod.fst_mul, Pi.mul_apply, Pi.add_apply, mul_add, Real.exp_add]
  · simp only [dilV_snd, Prod.snd_mul, Pi.mul_apply, Pi.add_apply, mul_add, Real.exp_add,
      Complex.ofReal_mul]

theorem dilV_zero : dilV (0 : realSpace K) = 1 := by
  ext w
  · simp [dilV_fst]
  · simp [dilV_snd]

theorem dilV_mul_neg (x : realSpace K) : dilV x * dilV (-x) = 1 := by
  rw [← dilV_add, add_neg_cancel, dilV_zero]

theorem dilV_neg_mul (x : realSpace K) : dilV (-x) * dilV x = 1 := by
  rw [mul_comm, dilV_mul_neg]

/-- Multiplication by `a`, as a linear map. -/
noncomputable def mulL (a : mixedSpace K) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  LinearMap.mulLeft ℝ a

@[simp] theorem mulL_apply (a z : mixedSpace K) : mulL a z = a * z := rfl

theorem mulL_eq_prodMap (a : mixedSpace K) :
    mulL a = LinearMap.prodMap (LinearMap.mulLeft ℝ a.1)
      (LinearMap.pi fun w : {w : InfinitePlace K // IsComplex w} =>
        (LinearMap.mulLeft ℝ (a.2 w)) ∘ₗ LinearMap.proj w) := by
  ext z w <;> simp

theorem isEmpty_isReal [IsTotallyComplex K] : IsEmpty {w : InfinitePlace K // IsReal w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩

theorem det_mulL [IsTotallyComplex K] (a : mixedSpace K) :
    LinearMap.det (mulL a) = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖a.2 w‖ ^ 2 := by
  have : IsEmpty {w : InfinitePlace K // IsReal w} := isEmpty_isReal
  rw [mulL_eq_prodMap, LinearMap.det_prodMap, LinearMap.det_eq_one_of_subsingleton, one_mul,
    LinearMap.det_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [show LinearMap.mulLeft ℝ (a.2 w) = Algebra.lmul ℝ ℂ (a.2 w) from rfl,
    ← Algebra.norm_apply ℝ (a.2 w), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem det_mulL_dilV [IsTotallyComplex K] (x : realSpace K) :
    LinearMap.det (mulL (dilV x)) = Real.exp (∑ w, x w) := by
  rw [det_mulL]
  simp only [dilV_snd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mult_isComplex, Nat.cast_ofNat]
  simp_rw [← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) _ _
    fun w => ?_
  simp only [Equiv.subtypeUnivEquiv_apply]
  push_cast
  ring

/-- The change of variables for multiplication by an invertible `a`. -/
theorem integral_comp_mul [IsTotallyComplex K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : mixedSpace K → E) (a b : mixedSpace K) (hab : a * b = 1) :
    ∫ v, g (a * v) = (LinearMap.det (mulL a))⁻¹ • ∫ v, g v := by
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have hdet : LinearMap.det (mulL a) ≠ 0 := by
    intro h
    have : LinearMap.det (mulL a) * LinearMap.det (mulL b) = 1 := by
      rw [← LinearMap.det_comp]
      have : mulL a ∘ₗ mulL b = LinearMap.id := by ext z <;> simp [← mul_assoc, hab]
      rw [this, LinearMap.det_id]
    rw [h, zero_mul] at this; exact zero_ne_one this
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (mixedSpace K)) hdet
  let eL : mixedSpace K ≃ₗ[ℝ] mixedSpace K :=
    { mulL a with
      invFun := fun z => b * z
      left_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc, hba,
          one_mul]
      right_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc, hab,
          one_mul] }
  let e : mixedSpace K ≃ᵐ mixedSpace K :=
    (LinearEquiv.toContinuousLinearEquiv eL).toHomeomorph.toMeasurableEquiv
  have he : (e : mixedSpace K → mixedSpace K) = mulL a := rfl
  have h1 := integral_map_equiv (μ := (volume : Measure (mixedSpace K))) e g
  rw [he, hmap, integral_smul_measure] at h1
  rw [← he] at h1
  change ∫ v, g (e v) = _
  rw [← h1, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hpos : 0 < LinearMap.det (mulL a) := by
    refine lt_of_le_of_ne ?_ (Ne.symm hdet)
    rw [det_mulL]; positivity
  rw [abs_of_pos (inv_pos.2 hpos)]

/-- Multiplication by an invertible `a`, as a continuous linear equivalence. -/
noncomputable def mulE (a b : mixedSpace K) (hab : a * b = 1) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  LinearEquiv.toContinuousLinearEquiv
    { mulL a with
      invFun := fun z => b * z
      left_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc,
          mul_comm b a, hab, one_mul]
      right_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulL_apply, ← mul_assoc, hab,
          one_mul] }

@[simp] theorem mulE_apply (a b : mixedSpace K) (hab : a * b = 1) (z : mixedSpace K) :
    mulE a b hab z = a * z := rfl

/-- Multiplication by `dilV x`, as a continuous linear equivalence. -/
noncomputable def dilE (x : realSpace K) : mixedSpace K ≃L[ℝ] mixedSpace K :=
  mulE (dilV x) (dilV (-x)) (dilV_mul_neg x)

@[simp] theorem dilE_apply (x : realSpace K) (z : mixedSpace K) : dilE x z = dilV x * z := rfl

/-- The change of variables for a positive dilation. -/
theorem integral_comp_dilV [IsTotallyComplex K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : mixedSpace K → E) (x : realSpace K) :
    ∫ v, g (dilV x * v) = Real.exp (-(∑ w, x w)) • ∫ v, g v := by
  rw [integral_comp_mul g _ _ (dilV_mul_neg x), det_mulL_dilV, Real.exp_neg]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Pois: Poisson summation over a fractional ideal, dilated and translated

From the library's lattice Poisson formula (4bf11d4c) and the trace dual of an ideal lattice
(9fd5cbc5): for a fractional ideal `I`, a Schwartz function `φ` on the mixed space, a positive
dilation `x` and a translation `t ∈ K`,
`∑_{a ∈ I} φ(y_x (t + a)) = (covol I · e^{Σx})⁻¹ ∑_{η ∈ I^∨} φ̂(y_x⁻¹ η) e(Tr(t η))`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The Fourier transform on the mixed space for the trace pairing. -/
noncomputable def fourierM (φ : mixedSpace K → ℂ) (η : mixedSpace K) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume (Algebra.traceForm ℝ (mixedSpace K)) φ η

theorem fourierM_dil [IsTotallyComplex K] (φ : mixedSpace K → ℂ) (x : realSpace K)
    (η : mixedSpace K) :
    fourierM (fun v => φ (dilV x * v)) η =
      Real.exp (-(∑ w, x w)) • fourierM φ (dilV (-x) * η) := by
  simp only [fourierM, VectorFourier.fourierIntegral]
  have key : ∀ v : mixedSpace K, Algebra.traceForm ℝ (mixedSpace K) v η =
      Algebra.traceForm ℝ (mixedSpace K) (dilV x * v) (dilV (-x) * η) := by
    intro v
    simp only [Algebra.traceForm_apply]
    congr 1
    calc v * η = (dilV (-x) * dilV x) * (v * η) := by rw [dilV_neg_mul, one_mul]
      _ = dilV x * v * (dilV (-x) * η) := by ring
  simp_rw [key]
  exact integral_comp_dilV (fun u => Real.fourierChar (-(Algebra.traceForm ℝ (mixedSpace K) u
    (dilV (-x) * η))) • φ u) x

/-- The elements of a fractional ideal, embedded, are the ideal lattice. -/
noncomputable def latEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) ≃ idealLattice K I :=
  Equiv.ofBijective (fun a => ⟨mixedEmbedding K a, (mem_idealLattice K I).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (mixedEmbedding_injective K (congrArg Subtype.val h)), fun z => by
      obtain ⟨a, ha, h⟩ := (mem_idealLattice K I).1 z.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩

/-- The trace dual, embedded, is the dual lattice. -/
noncomputable def dualEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K) :
      Set K) ≃
    LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
      (idealLattice K I) :=
  Equiv.ofBijective (fun a => ⟨mixedEmbedding K a, by
      have h := coe_dualSubmodule_flip_traceForm_idealLattice K I
      have : mixedEmbedding K a ∈ (LinearMap.BilinForm.dualSubmodule
          (Algebra.traceForm ℝ (mixedSpace K)).flip (idealLattice K I) : Set (mixedSpace K)) := by
        rw [h]; exact ⟨a, a.2, rfl⟩
      exact this⟩)
    ⟨fun a b h => Subtype.ext (mixedEmbedding_injective K (congrArg Subtype.val h)), fun z => by
      have h := coe_dualSubmodule_flip_traceForm_idealLattice K I
      have hz : (z : mixedSpace K) ∈ (LinearMap.BilinForm.dualSubmodule
          (Algebra.traceForm ℝ (mixedSpace K)).flip (idealLattice K I) : Set (mixedSpace K)) := z.2
      rw [h] at hz
      obtain ⟨a, ha, h⟩ := hz
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩

theorem traceForm_mixedEmbedding (t η : K) :
    Algebra.traceForm ℝ (mixedSpace K) (mixedEmbedding K t) (mixedEmbedding K η) =
      (Algebra.trace ℚ K (t * η) : ℝ) := by
  rw [Algebra.traceForm_apply, ← map_mul, NumberField.mixedEmbedding.trace_mixedEmbedding]

/-- **Poisson summation over a fractional ideal**, dilated by `dilV x` and translated by `t`. -/
theorem tsum_dil_eq [IsTotallyComplex K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (φ : 𝓢(mixedSpace K, ℂ)) (x : realSpace K) (t : K) :
    ∑' a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K),
        φ (dilV x * mixedEmbedding K (t + a)) =
      ((ZLattice.covolume (idealLattice K I) * Real.exp (∑ w, x w) : ℝ) : ℂ)⁻¹ *
        ∑' η : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
            FractionalIdeal (𝓞 K)⁰ K) : Set K),
          fourierM φ (dilV (-x) * mixedEmbedding K η) *
            (Real.fourierChar (Algebra.trace ℚ K (t * η) : ℝ) : ℂ) := by
  set φx : 𝓢(mixedSpace K, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilE x) φ
  have hφx : ∀ v, φx v = φ (dilV x * v) := fun v => rfl
  have h := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral volume
    (Algebra.traceForm ℝ (mixedSpace K)) (traceForm_mixedSpace_nondegenerate K) (idealLattice K I)
    φx (mixedEmbedding K t)
  rw [← (latEquiv I).tsum_eq, ← (dualEquiv I).tsum_eq] at h
  simp only [hφx] at h
  have hL : ∀ a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K),
      φ (dilV x * mixedEmbedding K (t + a)) =
        φ (dilV x * (mixedEmbedding K t + ((latEquiv I a : idealLattice K I) : mixedSpace K))) := by
    intro a; rw [map_add]; rfl
  simp_rw [hL, h]
  rw [Complex.ofReal_mul, mul_inv, mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun η => ?_
  change VectorFourier.fourierIntegral Real.fourierChar volume (Algebra.traceForm ℝ (mixedSpace K))
      (fun v => φ (dilV x * v)) (mixedEmbedding K η) *
      (Real.fourierChar (Algebra.traceForm ℝ (mixedSpace K) (mixedEmbedding K t)
        (mixedEmbedding K η)) : ℂ) = _
  have := fourierM_dil (φ := fun v => φ v) x (mixedEmbedding K η)
  simp only [fourierM] at this
  rw [this, traceForm_mixedEmbedding, Real.exp_neg, Complex.real_smul]
  push_cast
  simp only [fourierM]
  ring

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Test: radial test functions on the mixed space

A smooth compactly supported `Φ` on `realSpace K` (log coordinates `mult w · log ‖z_w‖`) gives the
radial test function `phiF Φ` on the mixed space: smooth, compactly supported, vanishing near the
coordinate hyperplanes. Its Fourier transform is radial as well, `fourierM (phiF Φ) z = PhiHat Φ
(logM z)`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-- Log coordinates of a point of the mixed space. -/
noncomputable def logM (z : mixedSpace K) : realSpace K :=
  fun w => (w.mult : ℝ) * Real.log (normAtPlace w z)

/-- The radial test function attached to `Φ`. -/
noncomputable def phiF (Φ : realSpace K → ℝ) (z : mixedSpace K) : ℂ :=
  if ∀ w, normAtPlace w z ≠ 0 then (Φ (logM z) : ℂ) else 0

theorem phiF_of_ne {Φ : realSpace K → ℝ} {z : mixedSpace K} (hz : ∀ w, normAtPlace w z ≠ 0) :
    phiF Φ z = Φ (logM z) := if_pos hz

section smooth

variable [IsTotallyComplex K]

theorem normAtPlace_eq_norm_snd (w : InfinitePlace K) (z : mixedSpace K) :
    normAtPlace w z = ‖z.2 ⟨w, IsTotallyComplex.isComplex w⟩‖ :=
  normAtPlace_apply_of_isComplex (IsTotallyComplex.isComplex w) z

theorem contDiffAt_logM {z : mixedSpace K} (hz : ∀ w, normAtPlace w z ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (logM (K := K)) z := by
  refine contDiffAt_pi.2 fun w => ?_
  have hw := hz w
  rw [normAtPlace_eq_norm_snd] at hw
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : mixedSpace K => ‖z.2 ⟨w, IsTotallyComplex.isComplex w⟩‖)
      z := by
    have hn := contDiffAt_norm ℝ (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (norm_ne_zero_iff.1 hw)
    have hp : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : mixedSpace K => z.2 ⟨w, IsTotallyComplex.isComplex w⟩) :=
      (contDiff_apply ℝ ℂ _).comp contDiff_snd
    exact hn.comp z hp.contDiffAt
  have h2 := (Real.contDiffAt_log.2 hw).comp z h1
  have h3 := contDiffAt_const (c := (w.mult : ℝ)).mul h2
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
  simp only [logM, normAtPlace_eq_norm_snd, Function.comp_apply]

variable {Φ : realSpace K → ℝ}

theorem exists_bound_of_hasCompactSupport (hΦ : HasCompactSupport Φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ b, R < ‖b‖ → Φ b = 0 := by
  obtain ⟨R, hR⟩ := hΦ.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun b hb => ?_⟩
  by_contra h
  have := hR (subset_tsupport _ h)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 1]

theorem phiF_eventually_zero (hΦ : HasCompactSupport Φ) {z : mixedSpace K}
    (hz : ¬ ∀ w, normAtPlace w z ≠ 0) : phiF Φ =ᶠ[nhds z] 0 := by
  push Not at hz
  obtain ⟨w, hw⟩ := hz
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hΦ
  have hm : (1 : ℝ) ≤ w.mult := by exact_mod_cast w.mult_pos
  set ε := Real.exp (-(R + 1))
  have hε : 0 < ε := Real.exp_pos _
  have hcont : Continuous (normAtPlace w : mixedSpace K → ℝ) := continuous_normAtPlace w
  have hU : ∀ᶠ z' in nhds z, normAtPlace w z' < ε :=
    hcont.continuousAt.eventually (gt_mem_nhds (by rw [hw]; exact hε))
  filter_upwards [hU] with z' hz'
  simp only [Pi.zero_apply, phiF]
  split_ifs with h
  · have hpos : 0 < normAtPlace w z' := lt_of_le_of_ne (normAtPlace_nonneg w z') (Ne.symm (h w))
    have hlog : Real.log (normAtPlace w z') < -(R + 1) := by
      rw [Real.log_lt_iff_lt_exp hpos]; exact hz'
    have hb : R < ‖logM z'‖ := by
      have h1 : |logM z' w| ≤ ‖logM z'‖ := by
        have := norm_le_pi_norm (logM z') w
        rwa [Real.norm_eq_abs] at this
      have h2 : R < |logM z' w| := by
        rw [abs_of_neg]
        · simp only [logM]; nlinarith
        · simp only [logM]; nlinarith
      linarith
    rw [hR _ hb]; simp
  · rfl

theorem contDiff_phiF (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (phiF (K := K) Φ) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : ∀ w, normAtPlace w z ≠ 0
  · have hU : ∀ᶠ z' in nhds z, ∀ w, normAtPlace w z' ≠ 0 := by
      refine Filter.eventually_all.2 fun w => ?_
      exact (continuous_normAtPlace w).continuousAt.eventually_ne (hz w)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' => ((Φ (logM z') : ℝ) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z (hΦs.contDiffAt.comp z (contDiffAt_logM hz))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with z' hz'
    exact phiF_of_ne hz'
  · exact contDiffAt_const.congr_of_eventuallyEq (phiF_eventually_zero hΦ hz)

theorem hasCompactSupport_phiF (hΦ : HasCompactSupport Φ) :
    HasCompactSupport (phiF (K := K) Φ) := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_of_hasCompactSupport hΦ
  have hm : ∀ w : InfinitePlace K, (1 : ℝ) ≤ w.mult := fun w => by exact_mod_cast w.mult_pos
  refine HasCompactSupport.intro (isCompact_closedBall (0 : mixedSpace K) (Real.exp R))
    fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  simp only [phiF]
  split_ifs with h
  · rw [norm_eq_sup'_normAtPlace] at hz
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun w => normAtPlace w z)
    rw [hw] at hz
    have hpos : 0 < normAtPlace w z := lt_of_le_of_ne (normAtPlace_nonneg w z) (Ne.symm (h w))
    have hlog : R < Real.log (normAtPlace w z) := by
      rw [Real.lt_log_iff_exp_lt hpos]; exact hz
    have hb : R < ‖logM z‖ := by
      have h1 : |logM z w| ≤ ‖logM z‖ := by
        have := norm_le_pi_norm (logM z) w
        rwa [Real.norm_eq_abs] at this
      have h2 : R < |logM z w| := by
        rw [abs_of_pos]
        · simp only [logM]; nlinarith [hm w]
        · simp only [logM]; nlinarith [hm w]
      linarith
    rw [hR _ hb]; simp
  · rfl

/-- The radial test function as a Schwartz function. -/
noncomputable def phiS (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ) :
    𝓢(mixedSpace K, ℂ) :=
  (hasCompactSupport_phiF hΦ).toSchwartzMap (contDiff_phiF hΦs hΦ)

@[simp] theorem phiS_apply (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ)
    (z : mixedSpace K) : phiS hΦs hΦ z = phiF Φ z := rfl

end smooth

/-! ### The Fourier transform is radial -/

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Radial: integrals of radial functions in log coordinates

For `K` totally complex and `f z = F (logM z)` off the coordinate hyperplanes,
`∫ f = π^{r₂} ∫ e^{Σ b} F(b) db` (polar coordinates, then `r_w = exp (b_w / 2)`).
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

theorem prod_complex_eq {M : Type*} [CommMonoid M] (g : InfinitePlace K → M) :
    ∏ w : {w : InfinitePlace K // IsComplex w}, g w.1 = ∏ w, g w :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) _ _
    fun _ => rfl

theorem mult_eq_two (w : InfinitePlace K) : w.mult = 2 :=
  mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Zeta: log-profiles of Schwartz functions and their zeta integrals

For `h` Schwartz on the mixed space, `prof h b = h (dilV b)` decays like `∏_w (1 + e^{b_w/2})^{-N}`
for every `N`, so `Zm h s = ∫ prof h b · e^{s Σ b} db` converges and is holomorphic on `Re s > 0`,
bounded on vertical strips.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

variable [IsTotallyComplex K]

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Exch: the exchange identity and `Z(φ̂, 1/6) ≠ 0`

For the radial test function `φ = phiF Φ`, Fubini and Fourier inversion (a79f4737) give
`∫ φ̂(y_b v) φ̂(v) dv = c ∫ φ(u) φ(y_b u) du` with `c > 0`; integrating against `e^{s Σ b}` in log
coordinates gives `Z(φ̂, s) Z(φ̂, 1 − s) = c Z(φ, s) Z(φ, 1 − s)` for `0 < s < 1`.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding.fundamentalCone
open scoped Real Classical SchwartzMap

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

section exchange

variable {Φ : realSpace K → ℝ} (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : HasCompactSupport Φ)

end exchange

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-! # L3M_Tr: the trace form of the mixed space in coordinates (`K` totally complex)

* `trace_pi_apply`: the trace of a finite product of algebras is the sum of the traces.
* `traceForm_eq`: `Tr(v η) = Σ_w 2 Re(v_w η_w)` on the mixed space of a totally complex field.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.L3M

/-- The trace of a finite product of algebras. -/
lemma trace_pi_apply {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [Algebra ℝ A]
    [Module.Free ℝ A] [Module.Finite ℝ A] (f : ι → A) :
    Algebra.trace ℝ (ι → A) f = ∑ i, Algebra.trace ℝ A (f i) := by
  conv_lhs => rw [← Finset.univ_sum_single f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_apply, Algebra.trace_apply]
  have key : Algebra.lmul ℝ (ι → A) (Pi.single i (f i)) =
      (LinearMap.single ℝ (fun _ => A) i) ∘ₗ (Algebra.lmul ℝ A (f i) ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun g => funext fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [key, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have hps : (LinearMap.proj i : (ι → A) →ₗ[ℝ] A) ∘ₗ LinearMap.single ℝ (fun _ => A) i =
      LinearMap.id := by
    refine LinearMap.ext fun a => ?_
    simp
  rw [hps, LinearMap.comp_id]

variable {K : Type*} [Field K] [NumberField K]

/-- The complex places. -/
abbrev CP (K : Type*) [Field K] [NumberField K] := {w : InfinitePlace K // IsComplex w}

/-- `Tr(v η) = Σ_w 2 Re(v_w η_w)` for `K` totally complex. -/
lemma traceForm_eq [IsTotallyComplex K] (v η : mixedSpace K) :
    Algebra.traceForm ℝ (mixedSpace K) v η = ∑ w : CP K, 2 * (v.2 w * η.2 w).re := by
  classical
  have : IsEmpty {w : InfinitePlace K // IsReal w} := L3P.isEmpty_isReal
  rw [Algebra.traceForm_apply, Algebra.trace_prod_apply, trace_pi_apply, trace_pi_apply]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Prod.snd_mul, Pi.mul_apply,
    Algebra.trace_complex_apply]

lemma traceForm_eq_trace [IsTotallyComplex K] (x : K) :
    ∑ w : CP K, 2 * (w.1.embedding x).re = (Algebra.trace ℚ K x : ℝ) := by
  have h := L3P.traceForm_mixedEmbedding (K := K) x 1
  rw [mul_one, traceForm_eq] at h
  simpa [mixedEmbedding_apply_isComplex] using h

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Phi: the Gaussian test functions with a quadratic phase

For weights `T : CP K → ℝ` (positive) and coefficients `b : CP K → ℂ`, the Schwartz function
`phiS T b v = exp(−π Σ_w T_w |v_w|²) · exp(2πi Σ_w 2 Re(b_w v_w²))` on the mixed space of a totally
complex field. Built from the library Gaussian on `EuclideanSpace` (f3ab09be), a dilation, and a
phase of temperate growth.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical SchwartzMap

noncomputable section

namespace ArtinPrimitiveRoots.L3M

/-- `x ↦ exp(a i x)` has temperate growth. -/
lemma hasTemperateGrowth_cexp_mul_I (a : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ => Complex.exp ((a : ℂ) * Complex.I * x)) := by
  set c : ℂ := (a : ℂ) * Complex.I with hc
  have hd : ∀ (k : ℂ) (x : ℝ), HasDerivAt (fun y : ℝ => k * Complex.exp (c * y))
      (k * (c * Complex.exp (c * x))) x := by
    intro k x
    have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) (c * 1) x :=
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    exact ((h1.cexp).const_mul k).congr_deriv (by ring)
  have hit : ∀ n : ℕ, iteratedDeriv n (fun y : ℝ => Complex.exp (c * y)) =
      fun y : ℝ => c ^ n * Complex.exp (c * y) := by
    intro n
    induction n with
    | zero => funext y; simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      rw [(hd _ y).deriv]
      ring
  refine ⟨?_, fun n => ⟨0, |a| ^ n, fun x => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit, norm_mul, norm_pow]
    have h1 : ‖Complex.exp (c * x)‖ = 1 := by
      rw [Complex.norm_exp]; simp [c]
    rw [h1, hc, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    simp

variable {K : Type*} [Field K] [NumberField K]

/-- The number of real coordinates. -/
abbrev mcount (K : Type*) [Field K] [NumberField K] : ℕ := Fintype.card (CP K × Fin 2)

/-- An enumeration of the real coordinates. -/
def eqv (K : Type*) [Field K] [NumberField K] : CP K × Fin 2 ≃ Fin (mcount K) :=
  Fintype.equivFin _

/-- A real coordinate of a point of the mixed space. -/
def coordF (p : CP K × Fin 2) (v : mixedSpace K) : ℝ :=
  if p.2 = 0 then (v.2 p.1).re else (v.2 p.1).im

/-- The real coordinates, as a linear map. -/
def coordL (K : Type*) [Field K] [NumberField K] : mixedSpace K →ₗ[ℝ] (Fin (mcount K) → ℝ) where
  toFun v i := coordF ((eqv K).symm i) v
  map_add' v v' := by
    funext i; simp only [coordF, Prod.snd_add, Pi.add_apply, Complex.add_re, Complex.add_im]
    split_ifs <;> rfl
  map_smul' r v := by
    funext i; simp only [coordF, Prod.smul_snd, Pi.smul_apply, Complex.real_smul,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> rfl

/-- The real coordinates in Euclidean space. -/
def eucL (K : Type*) [Field K] [NumberField K] : mixedSpace K →L[ℝ] EuclideanSpace ℝ (Fin (mcount K)) :=
  (EuclideanSpace.equiv (Fin (mcount K)) ℝ).symm.toContinuousLinearMap.comp
    (LinearMap.toContinuousLinearMap (coordL K))

lemma norm_eucL_sq (v : mixedSpace K) : ‖eucL K v‖ ^ 2 = ∑ w : CP K, ‖v.2 w‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have h1 : ∀ i, ‖(eucL K v) i‖ ^ 2 = coordF ((eqv K).symm i) v ^ 2 := by
    intro i
    simp [eucL, coordL, Real.norm_eq_abs, sq_abs]
  simp_rw [h1]
  rw [Equiv.sum_comp (eqv K).symm (fun p => coordF p v ^ 2), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.sum_univ_two]
  simp only [coordF, show (1 : Fin 2) ≠ 0 from by decide, if_false, if_true]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

lemma norm_le_eucL [IsTotallyComplex K] (v : mixedSpace K) : ‖v‖ ≤ ‖eucL K v‖ := by
  have : IsEmpty {w : InfinitePlace K // IsReal w} := L3P.isEmpty_isReal
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [show v.1 = 0 from Subsingleton.elim _ _, norm_zero]; exact norm_nonneg _
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
    have h1 : ‖v.2 w‖ ^ 2 ≤ ‖eucL K v‖ ^ 2 := by
      rw [norm_eucL_sq]
      exact Finset.single_le_sum (f := fun w => ‖v.2 w‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ w)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h1

/-- The standard Gaussian `exp(−π Σ_w |v_w|²)` on the mixed space. -/
def gauss1 (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLM ℂ (eucL K).hasTemperateGrowth
    ⟨1, 1, fun v => by
      have := norm_le_eucL v
      have h0 := norm_nonneg (eucL K v)
      nlinarith⟩
    (SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin (mcount K))).choose

lemma gauss1_apply [IsTotallyComplex K] (v : mixedSpace K) :
    gauss1 K v = ((Real.exp (-(Real.pi * ∑ w : CP K, ‖v.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  simp only [gauss1, SchwartzMap.compCLM_apply, Function.comp_apply]
  rw [(SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin (mcount K))).choose_spec,
    norm_eucL_sq]

/-- The dilation parameter for weights `T`. -/
def xT (T : CP K → ℝ) : realSpace K := fun w => if h : IsComplex w then Real.log (T ⟨w, h⟩) else 0

lemma dilV_xT_snd (T : CP K → ℝ) (hT : ∀ w, 0 < T w) (w : CP K) :
    ((L3P.dilV (xT T)).2 w : ℂ) = ((Real.sqrt (T w) : ℝ) : ℂ) := by
  rw [L3P.dilV_snd]
  congr 1
  rw [mult_isComplex, xT, dif_pos w.2, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (hT w)]
  congr 1; push_cast; ring

/-- The weighted Gaussian `exp(−π Σ_w T_w |v_w|²)`. -/
def gaussT [IsTotallyComplex K] (T : CP K → ℝ) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (L3P.dilE (xT T)) (gauss1 K)

lemma gaussT_apply [IsTotallyComplex K] (T : CP K → ℝ) (hT : ∀ w, 0 < T w) (v : mixedSpace K) :
    gaussT T v = ((Real.exp (-(Real.pi * ∑ w : CP K, T w * ‖v.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  simp only [gaussT, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    L3P.dilE_apply, gauss1_apply]
  congr 4
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Prod.snd_mul, Pi.mul_apply, norm_mul, dilV_xT_snd T hT, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hT w).le]

/-- The quadratic phase `Σ_w 2 Re(b_w v_w²)`. -/
def qq (b : CP K → ℂ) (v : mixedSpace K) : ℝ := ∑ w : CP K, 2 * (b w * v.2 w ^ 2).re

lemma hasTemperateGrowth_qq (b : CP K → ℂ) : Function.HasTemperateGrowth (qq b) := by
  unfold qq
  refine Function.HasTemperateGrowth.sum (s := Finset.univ)
    (f := fun (w : CP K) (v : mixedSpace K) => (2 * (b w * v.2 w ^ 2).re : ℝ)) fun w _ => ?_
  have hp : Function.HasTemperateGrowth (fun v : mixedSpace K => v.2 w) := by
    have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : CP K => ℂ) w).comp
      (ContinuousLinearMap.snd ℝ ({w : InfinitePlace K // IsReal w} → ℝ) (CP K → ℂ))).hasTemperateGrowth
    exact this
  have h2 : Function.HasTemperateGrowth (fun v : mixedSpace K => b w * v.2 w ^ 2) :=
    (Function.HasTemperateGrowth.const (b w)).mul (hp.pow 2)
  have h3 : Function.HasTemperateGrowth (fun v : mixedSpace K => (b w * v.2 w ^ 2).re) :=
    Complex.reCLM.hasTemperateGrowth.comp h2
  exact (Function.HasTemperateGrowth.const (2 : ℝ)).mul h3

/-- The phase factor. -/
def phase (b : CP K → ℂ) (v : mixedSpace K) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (qq b v : ℂ))

lemma hasTemperateGrowth_phase (b : CP K → ℂ) : Function.HasTemperateGrowth (phase b) :=
  (hasTemperateGrowth_cexp_mul_I (2 * Real.pi)).comp (hasTemperateGrowth_qq b)

/-- The test function `exp(−π Σ T_w |v_w|²) · exp(2πi Σ 2 Re(b_w v_w²))`. -/
def phiS [IsTotallyComplex K] (T : CP K → ℝ) (b : CP K → ℂ) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (phase b) (gaussT T)

lemma phiS_apply [IsTotallyComplex K] (T : CP K → ℝ) (hT : ∀ w, 0 < T w) (b : CP K → ℂ)
    (v : mixedSpace K) :
    phiS T b v = ((Real.exp (-(Real.pi * ∑ w : CP K, T w * ‖v.2 w‖ ^ 2)) : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (qq b v : ℂ)) := by
  rw [phiS, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase b), smul_eq_mul,
    gaussT_apply T hT, mul_comm]
  rfl

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_FT1: the Fourier transform of a Gaussian with a quadratic phase on `ℂ`

`∫_ℂ exp(−π t |z|²) exp(2πi·2 Re(β z²)) exp(−2πi·2 Re(z η)) dz = F1 t β η` with
`F1 t β η = (t² + 16|β|²)^{-1/2} exp(−4π (t |η|² + 4 i Re(β̄ η²)) / (t² + 16|β|²))`.

Proof: rotate `z ↦ u z` with `u² β = |β|`, split `ℂ = ℝ × ℝ`, and use the one-dimensional complex
Gaussian integral `integral_cexp_quadratic`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open MeasureTheory Complex
open scoped Real ComplexConjugate

noncomputable section

namespace ArtinPrimitiveRoots.L3M

/-- The transform. -/
def F1 (t : ℝ) (β η : ℂ) : ℂ :=
  ((Real.sqrt (t ^ 2 + 16 * ‖β‖ ^ 2))⁻¹ : ℝ) *
    cexp (-(4 * π * ((t : ℂ) * (‖η‖ ^ 2 : ℝ) + 4 * I * ((conj β * η ^ 2).re : ℂ)) /
      ((t ^ 2 + 16 * ‖β‖ ^ 2 : ℝ) : ℂ)))

/-- The integrand. -/
def g1 (t : ℝ) (β η : ℂ) (z : ℂ) : ℂ :=
  cexp (-(π * t * ‖z‖ ^ 2 : ℝ)) * cexp (2 * π * I * ((2 * (β * z ^ 2).re : ℝ) : ℂ)) *
    cexp (2 * π * I * ((-(2 * (z * η).re) : ℝ) : ℂ))

lemma sqrt_prod_conj {w : ℂ} (hw : 0 < w.re) :
    w ^ (1 / 2 : ℂ) * (conj w) ^ (1 / 2 : ℂ) = (‖w‖ : ℂ) := by
  have harg : w.arg ≠ π := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have h1 : (conj w) ^ (1 / 2 : ℂ) = conj (w ^ (1 / 2 : ℂ)) := by
    have := Complex.cpow_conj w (1 / 2 : ℂ) harg
    have hc : conj (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    rw [hc] at this
    rw [this, Complex.conj_conj]
  rw [h1, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : ‖w ^ (1 / 2 : ℂ)‖ = ‖w‖ ^ (1 / 2 : ℝ) := by
    have := Complex.norm_cpow_real w (1 / 2 : ℝ)
    simpa using this
  rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- The real-coefficient case. -/
lemma integral_g1_real (t : ℝ) (ht : 0 < t) (c : ℝ) (ξ : ℂ) :
    ∫ z : ℂ, g1 t c ξ z =
      ((Real.sqrt (t ^ 2 + 16 * c ^ 2))⁻¹ : ℝ) *
        cexp (-(4 * π * ((t : ℂ) * (‖ξ‖ ^ 2 : ℝ) + 4 * I * c * ((ξ ^ 2).re : ℂ)) /
          ((t ^ 2 + 16 * c ^ 2 : ℝ) : ℂ))) := by
  set p := ξ.re
  set q := ξ.im
  set b₁ : ℂ := -(π : ℂ) * (t - 4 * I * c)
  set b₂ : ℂ := -(π : ℂ) * (t + 4 * I * c)
  have hb₁ : b₁.re < 0 := by
    simp only [b₁, neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, sub_re, mul_im, I_re, I_im]
    norm_num; positivity
  have hb₂ : b₂.re < 0 := by
    simp only [b₂, neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, add_re, mul_im, I_re, I_im]
    norm_num; positivity
  -- split `ℂ = ℝ × ℝ`
  have hsplit : ∀ a b : ℝ, g1 t c ξ (equivRealProd.symm (a, b)) =
      cexp (b₁ * (a : ℂ) ^ 2 + (-4 * π * I * p) * a + 0) *
        cexp (b₂ * (b : ℂ) ^ 2 + (4 * π * I * q) * b + 0) := by
    intro a b
    simp only [g1, equivRealProd_symm_apply]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hn : ‖(a : ℂ) + b * I‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    rw [hn]
    simp only [b₁, b₂, p, q]
    push_cast
    simp only [sq, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
    ring_nf
    (try push_cast)
    (try ring_nf)
    (try simp only [Complex.I_sq])
    (try ring)
  have hpres := (Complex.volume_preserving_equiv_real_prod.symm)
  rw [← hpres.integral_comp' (g := g1 t c ξ)]
  change ∫ x : ℝ × ℝ, g1 t c ξ (Complex.measurableEquivRealProd.symm x) = _
  have hsplit' : ∀ x : ℝ × ℝ, g1 t c ξ (Complex.measurableEquivRealProd.symm x) =
      cexp (b₁ * (x.1 : ℂ) ^ 2 + (-4 * π * I * p) * x.1 + 0) *
        cexp (b₂ * (x.2 : ℂ) ^ 2 + (4 * π * I * q) * x.2 + 0) := fun x => hsplit x.1 x.2
  simp_rw [hsplit']
  rw [Measure.volume_eq_prod, MeasureTheory.integral_prod_mul (fun a : ℝ => cexp (b₁ * (a : ℂ) ^ 2 + (-4 * π * I * p) * a + 0))
    (fun b : ℝ => cexp (b₂ * (b : ℂ) ^ 2 + (4 * π * I * q) * b + 0)),
    integral_cexp_quadratic hb₁, integral_cexp_quadratic hb₂]
  -- the square roots
  have hw : (π / -b₁) = 1 / ((t : ℂ) - 4 * I * c) := by
    simp only [b₁]; field_simp
  have hw2 : (π / -b₂) = conj (1 / ((t : ℂ) - 4 * I * c)) := by
    simp only [b₂, map_div₀, map_one, map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I,
      map_ofNat]
    field_simp
    ring
  have hre : 0 < (1 / ((t : ℂ) - 4 * I * c)).re := by
    rw [one_div, Complex.inv_re]
    apply div_pos
    · simp; exact ht
    · rw [Complex.normSq_pos]
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
  have hnorm : ‖1 / ((t : ℂ) - 4 * I * c)‖ = (Real.sqrt (t ^ 2 + 16 * c ^ 2))⁻¹ := by
    rw [norm_div, norm_one, one_div]
    congr 1
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp; ring
  have hroot := sqrt_prod_conj hre
  rw [hnorm] at hroot
  have hden : (t : ℂ) - 4 * I * c ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hden2 : (t : ℂ) + 4 * I * c ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hden3 : ((t ^ 2 + 16 * c ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (t ^ 2 + 16 * c ^ 2 : ℝ) ≠ 0)
  calc (π / -b₁) ^ (1 / 2 : ℂ) * cexp (0 - (-4 * π * I * p) ^ 2 / (4 * b₁)) *
        ((π / -b₂) ^ (1 / 2 : ℂ) * cexp (0 - (4 * π * I * q) ^ 2 / (4 * b₂))) =
      ((π / -b₁) ^ (1 / 2 : ℂ) * (π / -b₂) ^ (1 / 2 : ℂ)) *
        cexp ((0 - (-4 * π * I * p) ^ 2 / (4 * b₁)) + (0 - (4 * π * I * q) ^ 2 / (4 * b₂))) := by
        rw [Complex.exp_add]; ring
    _ = _ := by
        rw [hw, hw2, hroot]
        congr 1
        congr 1
        have hξ : ‖ξ‖ ^ 2 = p ^ 2 + q ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        have hξ2 : (ξ ^ 2).re = p ^ 2 - q ^ 2 := by
          simp only [sq, mul_re, p, q]
        rw [hξ, hξ2]
        have hD : ((t : ℂ) ^ 2 + 16 * (c : ℂ) ^ 2) ≠ 0 := by
          exact_mod_cast (by positivity : (t ^ 2 + 16 * c ^ 2 : ℝ) ≠ 0)
        have hprod : ((t : ℂ) - 4 * I * c) * ((t : ℂ) + 4 * I * c) = (t : ℂ) ^ 2 + 16 * (c : ℂ) ^ 2 := by
          ring_nf; rw [Complex.I_sq]; ring
        have hs1 : (-4 * (π : ℂ) * I * p) ^ 2 = -16 * (π : ℂ) ^ 2 * (p : ℂ) ^ 2 := by
          ring_nf; rw [Complex.I_sq]; ring
        have hs2 : (4 * (π : ℂ) * I * q) ^ 2 = -16 * (π : ℂ) ^ 2 * (q : ℂ) ^ 2 := by
          ring_nf; rw [Complex.I_sq]; ring
        have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        have e1 : 0 - (-4 * (π : ℂ) * I * p) ^ 2 / (4 * b₁) =
            -4 * π * p ^ 2 * ((t : ℂ) + 4 * I * c) / ((t : ℂ) ^ 2 + 16 * (c : ℂ) ^ 2) := by
          rw [hs1, ← hprod]
          simp only [b₁]
          field_simp
          ring
        have e2 : 0 - (4 * (π : ℂ) * I * q) ^ 2 / (4 * b₂) =
            -4 * π * q ^ 2 * ((t : ℂ) - 4 * I * c) / ((t : ℂ) ^ 2 + 16 * (c : ℂ) ^ 2) := by
          rw [hs2, ← hprod]
          simp only [b₂]
          field_simp
          ring
        rw [e1, e2]
        push_cast
        field_simp
        ring

/-- Rotation invariance of the integral on `ℂ`. -/
lemma integral_comp_mul_unit {u : ℂ} (hu : ‖u‖ = 1) (g : ℂ → ℂ) :
    ∫ z, g (u * z) = ∫ z, g z := by
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  let L : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ u
  have hdet : LinearMap.det L = 1 := by
    rw [show L = Algebra.lmul ℝ ℂ u from rfl, ← Algebra.norm_apply ℝ u, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, hu, one_pow]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := L) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hmap
  let eL : ℂ ≃ₗ[ℝ] ℂ :=
    { L with
      invFun := fun z => u⁻¹ * z
      left_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, L, LinearMap.mulLeft_apply]
        field_simp
      right_inv := fun z => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, L, LinearMap.mulLeft_apply]
        field_simp }
  let e : ℂ ≃ᵐ ℂ := (LinearEquiv.toContinuousLinearEquiv eL).toHomeomorph.toMeasurableEquiv
  have he : (e : ℂ → ℂ) = L := rfl
  have h1 := integral_map_equiv (μ := (volume : Measure ℂ)) e g
  rw [he, hmap] at h1
  rw [h1]
  rfl

/-- **The per-place Fourier transform.** -/
lemma integral_g1 (t : ℝ) (ht : 0 < t) (β η : ℂ) : ∫ z : ℂ, g1 t β η z = F1 t β η := by
  set u : ℂ := cexp (-((β.arg / 2 : ℝ) : ℂ) * I) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, show -((β.arg / 2 : ℝ) : ℂ) * I = ((-(β.arg / 2) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hu2 : u ^ 2 * β = (‖β‖ : ℂ) := by
    have hβ := Complex.norm_mul_exp_arg_mul_I β
    have hsq : u ^ 2 = cexp (-(β.arg : ℂ) * I) := by
      rw [hu_def, ← Complex.exp_nat_mul]; push_cast; ring_nf
    calc u ^ 2 * β = cexp (-(β.arg : ℂ) * I) * (‖β‖ * cexp (β.arg * I)) := by rw [hsq, hβ]
      _ = ‖β‖ * cexp (-(β.arg : ℂ) * I + β.arg * I) := by rw [Complex.exp_add]; ring
      _ = ‖β‖ := by rw [show -(β.arg : ℂ) * I + β.arg * I = 0 by ring, Complex.exp_zero, mul_one]
  have hconj : (‖β‖ : ℂ) * u ^ 2 = conj β := by
    by_cases hβ0 : β = 0
    · simp [hβ0]
    have hn : (‖β‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hβ0
    have hβ0' : β ≠ 0 := hβ0
    have hu2' : u ^ 2 = (‖β‖ : ℂ) / β := by
      rw [eq_div_iff hβ0']; exact hu2
    have h1 : (‖β‖ : ℂ) * ‖β‖ = β * conj β := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [hu2', ← mul_div_assoc, h1]
    field_simp
  rw [← integral_comp_mul_unit hu]
  have hpt : ∀ z, g1 t β η (u * z) = g1 t (‖β‖ : ℂ) (u * η) z := by
    intro z
    simp only [g1]
    rw [norm_mul, hu, one_mul]
    congr 3
    · congr 2
      rw [show β * (u * z) ^ 2 = (u ^ 2 * β) * z ^ 2 by ring, hu2]
    · congr 3
      rw [show u * z * η = z * (u * η) by ring]
  simp_rw [hpt]
  rw [integral_g1_real t ht ‖β‖ (u * η)]
  simp only [F1]
  rw [norm_mul, hu, one_mul]
  congr 4
  have : (‖β‖ : ℂ) * ((u * η) ^ 2) = conj β * η ^ 2 := by
    rw [mul_pow, ← mul_assoc, hconj]
  have hre : ((‖β‖ : ℝ) : ℂ) * (((u * η) ^ 2).re : ℂ) = ((conj β * η ^ 2).re : ℂ) := by
    rw [← this]
    simp
  rw [mul_assoc (4 * I), hre]

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_FT: the Fourier transform of `phiS T b` on the mixed space

`fourierM (phiS T b) ξ = ∏_w F1 (T w) (b w) (ξ_w)` for `K` totally complex (Fubini over the places and
`integral_g1`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped Classical SchwartzMap Real

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

lemma integrand_eq (T : CP K → ℝ) (hT : ∀ w, 0 < T w) (b : CP K → ℂ) (ξ v : mixedSpace K) :
    Real.fourierChar (-(Algebra.traceForm ℝ (mixedSpace K) v ξ)) • phiS T b v =
      ∏ w : CP K, g1 (T w) (b w) (ξ.2 w) (v.2 w) := by
  rw [Circle.smul_def, phiS_apply T hT b v, traceForm_eq, Real.fourierChar_apply, smul_eq_mul]
  simp only [g1, ← Complex.exp_sum, Complex.ofReal_exp, ← Complex.exp_add, qq]
  congr 1
  push_cast
  simp only [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

lemma integral_snd_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (CP K → ℂ) → E) : ∫ v : mixedSpace K, f v.2 = ∫ z, f z := by
  have : IsEmpty {w : InfinitePlace K // IsReal w} := L3P.isEmpty_isReal
  rw [Measure.volume_eq_prod, integral_fun_snd]
  have h1 : (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ)).real Set.univ = 1 := by
    rw [measureReal_def, volume_pi, Measure.pi_univ, Finset.univ_eq_empty, Finset.prod_empty,
      ENNReal.toReal_one]
  rw [h1, one_smul]

/-- **The Fourier transform of `phiS`.** -/
theorem fourierM_phiS (T : CP K → ℝ) (hT : ∀ w, 0 < T w) (b : CP K → ℂ) (ξ : mixedSpace K) :
    L3P.fourierM (phiS T b) ξ = ∏ w : CP K, F1 (T w) (b w) (ξ.2 w) := by
  simp only [L3P.fourierM, VectorFourier.fourierIntegral]
  simp_rw [integrand_eq T hT b ξ]
  rw [integral_snd_eq (fun z : CP K → ℂ => ∏ w : CP K, g1 (T w) (b w) (ξ.2 w) (z w)),
    integral_fintype_prod_volume_eq_prod (fun w : CP K => g1 (T w) (b w) (ξ.2 w))]
  exact Finset.prod_congr rfl fun w _ => integral_g1 (T w) (hT w) (b w) (ξ.2 w)

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Asym: Gaussian lattice sums

For a fractional ideal `I`, weights `T_w > 0` and `y ∈ K`:
* `gauss_poisson`: `(∏ T_w) covol(I) Σ_{a∈I} e^{−π Σ T_w |y+a|_w²} = Σ_{η∈I^∨} e^{−4π Σ |η_w|²/T_w} e(Tr(yη))`;
* `gauss_err`: if all `T_w ≤ τ`, the left side is within `errE I τ` of `1`;
* `errE_tendsto`: `errE I τ → 0` as `τ → 0⁺`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical SchwartzMap Real nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {K : Type*} [Field K] [NumberField K]

theorem summable_schwartz_idealLattice' (f : 𝓢(mixedSpace K, ℂ)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : mixedSpace K) : Summable fun z : idealLattice K I => ‖f (t + z)‖ := by
  set N : ℕ := Module.finrank ℤ (idealLattice K I) + 1
  set C := 2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hb : ∀ x : mixedSpace K, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖ ^ (-(N : ℝ)) := by
    intro x hx
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at h1
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h2 : ‖x‖ ^ N * ‖f x‖ ≤ C := by
      refine le_trans ?_ h1
      gcongr
      linarith
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
      mul_comm]
    exact h2
  refine Summable.of_norm_bounded_eventually
    ((ZLattice.summable_norm_sub_rpow (L := idealLattice K I) (-(N : ℝ))
      (by simp [N]) (-t)).mul_left C) ?_
  have hfin : {z : idealLattice K I | t + (z : mixedSpace K) = 0}.Subsingleton := by
    intro a ha b hb
    exact Subtype.ext (by have := ha.trans hb.symm; simpa using this)
  refine (hfin.finite.subset fun z hz => ?_)
  by_contra h
  apply hz
  simp only [Set.mem_ofPred_eq, norm_norm]
  rw [sub_neg_eq_add, add_comm]
  exact hb _ fun h0 => h (by simpa [add_comm] using h0)

theorem summable_schwartz_fi (f : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : mixedSpace K) :
    Summable fun a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) => ‖f (t + mixedEmbedding K a)‖ := by
  have := summable_schwartz_idealLattice' f I t
  rw [← (L3P.latEquiv I).summable_iff] at this
  exact this

variable [IsTotallyComplex K]

/-- `Σ_w |v_w|²`. -/
def nsq (v : mixedSpace K) : ℝ := ∑ w : CP K, ‖v.2 w‖ ^ 2

lemma nsq_nonneg (v : mixedSpace K) : 0 ≤ nsq v := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nsq_pos {x : K} (hx : x ≠ 0) : 0 < nsq (mixedEmbedding K x) := by
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hw : IsComplex w₀ := IsTotallyComplex.isComplex w₀
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun w : CP K => ‖(mixedEmbedding K x).2 w‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ ⟨w₀, hw⟩))
  simp only [mixedEmbedding_apply_isComplex]
  have : w₀.embedding x ≠ 0 := (map_ne_zero _).2 hx
  positivity

lemma F1_zero (t : ℝ) (ht : 0 < t) (η : ℂ) :
    F1 t 0 η = ((t⁻¹ * Real.exp (-(4 * π * ‖η‖ ^ 2 / t)) : ℝ) : ℂ) := by
  simp only [F1, norm_zero, map_zero, zero_mul, Complex.zero_re, Complex.ofReal_zero, mul_zero,
    add_zero]
  rw [show t ^ 2 + 16 * (0 : ℝ) ^ 2 = t ^ 2 by ring, Real.sqrt_sq ht.le]
  push_cast
  congr 2
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp

lemma phiS_zero_apply (T : CP K → ℝ) (hT : ∀ w, 0 < T w) (v : mixedSpace K) :
    phiS T 0 v = ((Real.exp (-(Real.pi * ∑ w : CP K, T w * ‖v.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [phiS_apply T hT 0 v]
  simp [qq]

/-- The unit fractional ideal `I^∨`. -/
def dualU (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

lemma covol_pos (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : 0 < ZLattice.covolume (idealLattice K I) :=
  ZLattice.covolume_pos _ _

/-- The Gaussian weight on the dual side. -/
def dualW (T : CP K → ℝ) (η : K) : ℝ :=
  Real.exp (-(4 * π * ∑ w : CP K, ‖(mixedEmbedding K η).2 w‖ ^ 2 / T w))

/-- **Poisson for the Gaussian.** -/
theorem gauss_poisson (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (T : CP K → ℝ) (hT : ∀ w, 0 < T w)
    (y : K) :
    ((∏ w : CP K, T w : ℝ) : ℂ) * (ZLattice.covolume (idealLattice K I) : ℂ) *
        ∑' a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K), phiS T 0 (mixedEmbedding K (y + a)) =
      ∑' η : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
          FractionalIdeal (𝓞 K)⁰ K) : Set K),
        (dualW T η : ℂ) * (Real.fourierChar (Algebra.trace ℚ K (y * η) : ℝ) : ℂ) := by
  have h := L3P.tsum_dil_eq I (phiS T 0) 0 y
  simp only [L3P.dilV_zero, one_mul, neg_zero, Pi.zero_apply, Finset.sum_const_zero, Real.exp_zero,
    mul_one] at h
  rw [h]
  have hc : (ZLattice.covolume (idealLattice K I) : ℂ) ≠ 0 := by
    exact_mod_cast (covol_pos I).ne'
  have hT0 : ((∏ w : CP K, T w : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos fun w _ => hT w).ne'
  have e : ∀ S : ℂ, ((∏ w : CP K, T w : ℝ) : ℂ) * (ZLattice.covolume (idealLattice K I) : ℂ) *
      ((ZLattice.covolume (idealLattice K I) : ℂ)⁻¹ * S) = ((∏ w : CP K, T w : ℝ) : ℂ) * S := by
    intro S; field_simp
  rw [e, ← tsum_mul_left]
  refine tsum_congr fun η => ?_
  rw [fourierM_phiS T hT 0 (mixedEmbedding K η)]
  simp only [Pi.zero_apply]
  rw [Finset.prod_congr rfl fun w _ => F1_zero (T w) (hT w) _, ← Complex.ofReal_prod,
    Finset.prod_mul_distrib, ← Real.exp_sum, ← mul_assoc, ← Complex.ofReal_mul, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  simp only [fun w => mul_inv_cancel₀ (hT w).ne', Finset.prod_const_one, one_mul, dualW]
  congr 3
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- The error term. -/
def errE (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℝ) : ℝ :=
  ∑' η : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K),
    if (η : K) = 0 then 0 else Real.exp (-(4 * π * nsq (mixedEmbedding K η) / τ))

lemma summable_dual_gauss (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {τ : ℝ} (hτ : 0 < τ) :
    Summable fun η : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) : Set K) =>
      Real.exp (-(4 * π * nsq (mixedEmbedding K η) / τ)) := by
  have h := summable_schwartz_fi (phiS (fun _ => 4 / τ) 0) (dualU I) 0
  have hT : ∀ w : CP K, 0 < (fun _ => 4 / τ) w := fun _ => by positivity
  refine h.congr fun η => ?_
  rw [zero_add, phiS_zero_apply _ hT, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  congr 1
  simp only [nsq, ← Finset.mul_sum]
  ring

/-- **The error bound.** -/
theorem gauss_err (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (T : CP K → ℝ) (hT : ∀ w, 0 < T w)
    {τ : ℝ} (hτ : 0 < τ) (hTτ : ∀ w, T w ≤ τ) (y : K) :
    ‖((∏ w : CP K, T w : ℝ) : ℂ) * (ZLattice.covolume (idealLattice K I) : ℂ) *
        ∑' a : ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K), phiS T 0 (mixedEmbedding K (y + a)) - 1‖
      ≤ errE I τ := by
  rw [gauss_poisson I T hT y]
  set D := ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K)
  set f : D → ℂ := fun η => (dualW T η : ℂ) * (Real.fourierChar (Algebra.trace ℚ K (y * η) : ℝ) : ℂ)
  have hle : ∀ η : D, dualW T η ≤ Real.exp (-(4 * π * nsq (mixedEmbedding K η) / τ)) := by
    intro η
    unfold dualW
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff, nsq, mul_div_assoc, Finset.sum_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun w _ => ?_
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hT w) (hTτ w)
  have hnf : ∀ η : D, ‖f η‖ = dualW T η := by
    intro η
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, mul_one]
    exact abs_of_pos (Real.exp_pos _)
  have hsum : Summable fun η : D => ‖f η‖ :=
    (summable_dual_gauss I hτ).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun η => (hnf η).le.trans (hle η)
  have h0mem : (0 : K) ∈ D :=
    show (0 : K) ∈ ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K)) : Submodule (𝓞 K) K)
      from Submodule.zero_mem _
  set z : D := ⟨0, h0mem⟩
  have hf0 : f z = 1 := by
    simp only [f, z, dualW, map_zero, mixedEmbedding_apply_isComplex, norm_zero, zero_pow two_ne_zero,
      zero_div, Finset.sum_const_zero, mul_zero, neg_zero, Real.exp_zero, mul_zero, Complex.ofReal_one,
      one_mul, AddChar.map_zero_eq_one, Circle.coe_one]
    simp
  rw [(hsum.of_norm).tsum_eq_add_tsum_ite z, hf0, add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun η => ?_
    split_ifs <;> simp
  · refine Summable.tsum_le_tsum (fun η => ?_) ?_ ?_
    · by_cases h : η = z
      · rw [if_pos h, norm_zero]
        rw [if_pos (by rw [h])]
      · rw [if_neg h]
        have hη : (η : K) ≠ 0 := fun h' => h (Subtype.ext h')
        rw [if_neg hη, hnf]
        exact hle η
    · refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun η => ?_
      split_ifs <;> simp
    · refine (summable_dual_gauss I hτ).of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
        fun η => ?_
      split_ifs <;> simp [(Real.exp_pos _).le]

/-- **`errE I τ → 0` as `τ → 0⁺`.** -/
theorem errE_tendsto (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (errE I) (𝓝[>] 0) (𝓝 0) := by
  set D := ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K)
  have hlim : ∀ η : D, Tendsto (fun τ : ℝ =>
      if (η : K) = 0 then (0 : ℝ) else Real.exp (-(4 * π * nsq (mixedEmbedding K η) / τ)))
      (𝓝[>] 0) (𝓝 0) := by
    intro η
    by_cases hη : (η : K) = 0
    · simp only [hη, if_true]; exact tendsto_const_nhds
    · simp only [hη, if_false]
      have hp : 0 < 4 * π * nsq (mixedEmbedding K η) := by
        have := nsq_pos hη; positivity
      have h1 : Tendsto (fun τ : ℝ => 4 * π * nsq (mixedEmbedding K η) / τ) (𝓝[>] 0) atTop := by
        simp_rw [div_eq_mul_inv]
        exact tendsto_inv_nhdsGT_zero.const_mul_atTop hp
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun τ (η : D) => if (η : K) = 0 then (0 : ℝ) else
      Real.exp (-(4 * π * nsq (mixedEmbedding K η) / τ)))
    (g := fun _ => 0) (bound := fun η : D => Real.exp (-(4 * π * nsq (mixedEmbedding K η) / 1)))
    (summable_dual_gauss I one_pos) hlim ?_
  · simp only [tsum_zero] at h
    exact h
  · have : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT one_pos
    filter_upwards [this] with τ hτ
    intro η
    split_ifs with hη
    · simp only [norm_zero]; positivity
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, div_one]
      have hn := nsq_nonneg (mixedEmbedding K (η : K))
      rw [le_div_iff₀ hτ.1]
      have : 0 ≤ 4 * π * nsq (mixedEmbedding K η) := by positivity
      nlinarith [hτ.2]

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Hk1: the primal side of Hecke's theta identity

For `α ∈ 𝓞 ∖ 0`, `b = (α⁻¹)_w` and weights `T`, the theta sum `S(T) = Σ_{x ∈ 𝓞} phiS T b (x)` splits
over `𝓞/(α)`: the phase `e(Tr(x²/α))` depends only on `x mod α`, and the remaining Gaussian sums over
the cosets are controlled by `gauss_err`. Hence `(∏ T_w) covol((α)) S(T) → g(α)` as `T → 0`
(`primal_limit`), with `g(α) = Σ_{x mod α} e(Tr(x²/α))`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical SchwartzMap Real nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

/-- The quadratic coefficient `α⁻¹` at the complex places. -/
def bα (α : 𝓞 K) : CP K → ℂ := fun w => w.1.embedding ((α : K)⁻¹)

/-- The Gauss sum of the cut. -/
def gsum (α : 𝓞 K) : ℂ :=
  ∑ᶠ x : 𝓞 K ⧸ Ideal.span {α},
    Complex.exp (2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ K (((Quotient.out x : 𝓞 K) : K) ^ 2 / (α : K)) : ℚ) : ℂ))

lemma qq_emb (α : 𝓞 K) (x : K) :
    qq (bα α) (mixedEmbedding K x) = (Algebra.trace ℚ K (x ^ 2 / (α : K)) : ℝ) := by
  rw [← traceForm_eq_trace]
  unfold qq bα
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mixedEmbedding_apply_isComplex, div_eq_mul_inv, mul_comm (x ^ 2), map_mul, map_pow]

lemma phase_emb (α : 𝓞 K) (x : K) :
    phase (bα α) (mixedEmbedding K x) = Complex.exp (2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ K (x ^ 2 / (α : K)) : ℚ) : ℂ)) := by
  unfold phase
  rw [qq_emb]
  congr 2
  push_cast
  ring

lemma trace_int (z : 𝓞 K) : ∃ n : ℤ, Algebra.trace ℚ K (z : K) = n :=
  ⟨Algebra.trace ℤ (𝓞 K) z, by rw [Algebra.coe_trace_int]⟩

lemma phase_shift (α : 𝓞 K) (hα : α ≠ 0) (y z : 𝓞 K) :
    phase (bα α) (mixedEmbedding K ((y : K) + (α : K) * z)) =
      phase (bα α) (mixedEmbedding K (y : K)) := by
  rw [phase_emb, phase_emb]
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  obtain ⟨n, hn⟩ := trace_int (y * z + y * z + α * z ^ 2)
  have : ((y : K) + α * z) ^ 2 / α = (y : K) ^ 2 / α + ((y * z + y * z + α * z ^ 2 : 𝓞 K) : K) := by
    push_cast; field_simp; ring
  rw [this, map_add, hn]
  push_cast
  rw [mul_add, Complex.exp_add]
  have : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * n = n * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [this, mul_one]

lemma phiS_eq_mul (T : CP K → ℝ) (hT : ∀ w, 0 < T w) (b : CP K → ℂ) (v : mixedSpace K) :
    phiS T b v = phiS T 0 v * phase b v := by
  rw [phiS_apply T hT b v, phiS_zero_apply T hT v]
  rfl

/-- The fibration `𝓞/(α) × 𝓞 ≃ 𝓞`, `(y, z) ↦ ỹ + α z`. -/
def decEquiv (α : 𝓞 K) (hα : α ≠ 0) : (𝓞 K ⧸ Ideal.span {α}) × 𝓞 K ≃ 𝓞 K :=
  Equiv.ofBijective (fun p => Quotient.out p.1 + α * p.2) (by
    constructor
    · rintro ⟨y, z⟩ ⟨y', z'⟩ h
      simp only at h
      have hy : y = y' := by
        have := congrArg (Ideal.Quotient.mk (Ideal.span {α})) h
        rw [map_add, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _
          (Ideal.mem_span_singleton_self α)), Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self α)), add_zero, add_zero] at this
        have h1 : Ideal.Quotient.mk (Ideal.span {α}) (Quotient.out y) = y := Quotient.out_eq y
        have h2 : Ideal.Quotient.mk (Ideal.span {α}) (Quotient.out y') = y' := Quotient.out_eq y'
        rw [h1, h2] at this; exact this
      subst hy
      have : α * z = α * z' := add_left_cancel h
      rw [mul_left_cancel₀ hα this]
    · intro a
      have h1 : Ideal.Quotient.mk (Ideal.span {α}) (Quotient.out (Ideal.Quotient.mk (Ideal.span {α}) a)) =
          Ideal.Quotient.mk (Ideal.span {α}) a := Quotient.out_eq _
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h1.symm)
      refine ⟨(Ideal.Quotient.mk _ a, z), ?_⟩
      simp only
      linear_combination hz)

lemma tsum_decomp (α : 𝓞 K) (hα : α ≠ 0) (F : 𝓞 K → ℂ) (hF : Summable F) :
    ∑' x, F x = ∑ᶠ y : 𝓞 K ⧸ Ideal.span {α}, ∑' z : 𝓞 K, F (Quotient.out y + α * z) := by
  haveI : Finite (𝓞 K ⧸ Ideal.span {α}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  haveI : Fintype (𝓞 K ⧸ Ideal.span {α}) := Fintype.ofFinite _
  rw [← (decEquiv α hα).tsum_eq, finsum_eq_sum_of_fintype]
  have hs : Summable (F ∘ decEquiv α hα) := (decEquiv α hα).summable_iff.mpr hF
  rw [show (∑' c, F (decEquiv α hα c)) = ∑' c, (F ∘ decEquiv α hα) c from rfl, hs.tsum_prod,
    tsum_fintype]
  rfl

/-- `z ↦ α z`, as an equivalence onto `(α)`. -/
def spanEquiv (α : 𝓞 K) (hα : α ≠ 0) :
    𝓞 K ≃ ((FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) : FractionalIdeal (𝓞 K)⁰ K) : Set K) :=
  Equiv.ofBijective (fun z => ⟨(α : K) * z, (FractionalIdeal.mem_spanSingleton _).2
      ⟨z, by rw [Algebra.smul_def, mul_comm]⟩⟩) (by
    constructor
    · intro z z' h
      have := congrArg Subtype.val h
      simp only at this
      have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
      exact RingOfIntegers.coe_injective (mul_left_cancel₀ hαK this)
    · rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hx
      refine ⟨z, Subtype.ext ?_⟩
      simp only
      rw [Algebra.smul_def, mul_comm])

/-- `𝓞`, as an equivalence onto `1`. -/
def oneEquiv : 𝓞 K ≃ (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K) :=
  Equiv.ofBijective (fun z => ⟨(z : K), by
      rw [Units.val_one]; exact (FractionalIdeal.mem_one_iff _).2 ⟨z, rfl⟩⟩) (by
    constructor
    · intro z z' h
      have := congrArg Subtype.val h
      simp only at this
      exact RingOfIntegers.coe_injective this
    · rintro ⟨x, hx⟩
      rw [Units.val_one] at hx
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨z, rfl⟩)

/-- The fractional ideal `(α)` as a unit. -/
def Iα (α : 𝓞 K) (hα : α ≠ 0) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K))
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact_mod_cast hα)

lemma summable_phiS_O (T : CP K → ℝ) (b : CP K → ℂ) (y : K) :
    Summable fun x : 𝓞 K => phiS T b (mixedEmbedding K (y + x)) := by
  have h := summable_schwartz_fi (phiS T b) 1 (mixedEmbedding K y)
  rw [← oneEquiv.summable_iff] at h
  refine Summable.of_norm ?_
  refine h.congr fun x => ?_
  simp [oneEquiv, map_add]

/-- **The primal theta sum, split over `𝓞/(α)`.** -/
lemma primal_split (α : 𝓞 K) (hα : α ≠ 0) (T : CP K → ℝ) (hT : ∀ w, 0 < T w) :
    ∑' x : 𝓞 K, phiS T (bα α) (mixedEmbedding K x) =
      ∑ᶠ y : 𝓞 K ⧸ Ideal.span {α}, phase (bα α) (mixedEmbedding K ((Quotient.out y : 𝓞 K) : K)) *
        ∑' a : (((Iα α hα : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K),
          phiS T 0 (mixedEmbedding K ((Quotient.out y : 𝓞 K) + a)) := by
  have hs := summable_phiS_O T (bα α) 0
  simp only [zero_add] at hs
  rw [tsum_decomp α hα (fun x : 𝓞 K => phiS T (bα α) (mixedEmbedding K x)) hs]
  refine finsum_congr fun y => ?_
  rw [← tsum_mul_left]
  have he := (spanEquiv α hα).tsum_eq (fun a => phase (bα α) (mixedEmbedding K
    ((Quotient.out y : 𝓞 K) : K)) * phiS T 0 (mixedEmbedding K ((Quotient.out y : 𝓞 K) + (a : K))))
  rw [show ((Iα α hα : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) from rfl, ← he]
  refine tsum_congr fun z => ?_
  simp only [spanEquiv, Equiv.ofBijective_apply]
  rw [phiS_eq_mul T hT, map_add, map_mul]
  push_cast
  rw [phase_shift α hα, mul_comm]
  simp only [map_add, map_mul]

lemma norm_phase (b : CP K → ℂ) (v : mixedSpace K) : ‖phase b v‖ = 1 := by
  unfold phase
  rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (qq b v : ℂ) = ((2 * Real.pi * qq b v : ℝ) : ℂ) *
    Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The primal limit.** -/
theorem primal_limit (α : 𝓞 K) (hα : α ≠ 0) (T : ℝ → CP K → ℝ)
    (hT : ∀ s, 0 < s → ∀ w, 0 < T s w) (τ : ℝ → ℝ) (hτ : Tendsto τ (𝓝[>] 0) (𝓝[>] 0))
    (hTτ : ∀ s, 0 < s → ∀ w, T s w ≤ τ s) (hτpos : ∀ s, 0 < s → 0 < τ s) :
    Tendsto (fun s => ((∏ w : CP K, T s w : ℝ) : ℂ) *
        (ZLattice.covolume (idealLattice K (Iα α hα)) : ℂ) *
        ∑' x : 𝓞 K, phiS (T s) (bα α) (mixedEmbedding K x)) (𝓝[>] 0) (𝓝 (gsum α)) := by
  haveI : Finite (𝓞 K ⧸ Ideal.span {α}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  haveI : Fintype (𝓞 K ⧸ Ideal.span {α}) := Fintype.ofFinite _
  set Q := 𝓞 K ⧸ Ideal.span {α}
  have herr : Tendsto (fun s => (Fintype.card Q : ℝ) * errE (Iα α hα) (τ s)) (𝓝[>] 0) (𝓝 0) := by
    have := (errE_tendsto (Iα α hα)).comp hτ
    simpa using this.const_mul (Fintype.card Q : ℝ)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ herr
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [primal_split α hα (T s) (hT s hs), gsum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => errE (Iα α hα) (τ s)) fun y _ => ?_)
    (le_of_eq (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))
  have hg := gauss_err (Iα α hα) (T s) (hT s hs) (hτpos s hs) (hTτ s hs) ((Quotient.out y : 𝓞 K) : K)
  rw [← phase_emb]
  set P := ((∏ w : CP K, T s w : ℝ) : ℂ) * (ZLattice.covolume (idealLattice K (Iα α hα)) : ℂ)
  set ph := phase (bα α) (mixedEmbedding K ((Quotient.out y : 𝓞 K) : K))
  set S := ∑' a : (((Iα α hα : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K),
    phiS (T s) 0 (mixedEmbedding K ((Quotient.out y : 𝓞 K) + a))
  rw [show P * (ph * S) - ph = ph * (P * S - 1) by ring, norm_mul, norm_phase, one_mul]
  exact hg

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Hk2: the weights `T_w(s)` and the dual side of the theta identity

`Tw a s = 16 s a² / (2 + √(4 − 16 s² a²))` solves `T² + 16 a² = 4T/s` (for `s a ≤ 1/2`), so that the dual
Gaussian weight of `phiS (Tα α s) (bα α)` is the isotropic `s` for every `α` (`dual_eq`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical SchwartzMap Real nonZeroDivisors ComplexConjugate

noncomputable section

namespace ArtinPrimitiveRoots.L3M

/-- The weight. -/
def Tw (a s : ℝ) : ℝ := 16 * s * a ^ 2 / (2 + Real.sqrt (4 - 16 * s ^ 2 * a ^ 2))

lemma Tw_pos {a s : ℝ} (ha : 0 < a) (hs : 0 < s) : 0 < Tw a s := by
  unfold Tw; positivity

lemma Tw_le {a s : ℝ} (hs : 0 < s) : Tw a s ≤ 8 * s * a ^ 2 := by
  unfold Tw
  rw [div_le_iff₀ (by positivity)]
  have := Real.sqrt_nonneg (4 - 16 * s ^ 2 * a ^ 2)
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * s) (sq_nonneg a)) this]

lemma Tw_eq {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (hsa : s * a ≤ 1 / 2) :
    Tw a s ^ 2 + 16 * a ^ 2 = 4 * Tw a s / s := by
  set r := Real.sqrt (4 - 16 * s ^ 2 * a ^ 2)
  have hsa0 : 0 ≤ s * a := by positivity
  have hr0 : 0 ≤ 4 - 16 * s ^ 2 * a ^ 2 := by
    nlinarith [mul_le_mul hsa hsa hsa0 (by norm_num : (0:ℝ) ≤ 1 / 2)]
  have hr2 : r ^ 2 = 4 - 16 * s ^ 2 * a ^ 2 := Real.sq_sqrt hr0
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hT : Tw a s = (2 - r) / s := by
    unfold Tw
    rw [div_eq_div_iff (by positivity) hs.ne']
    nlinarith
  rw [hT]
  field_simp
  nlinarith

lemma Tw_div_tendsto {a : ℝ} :
    Tendsto (fun s => Tw a s / s) (𝓝[>] 0) (𝓝 (4 * a ^ 2)) := by
  have hc : ContinuousAt (fun s : ℝ => 16 * a ^ 2 / (2 + Real.sqrt (4 - 16 * s ^ 2 * a ^ 2))) 0 := by
    apply ContinuousAt.div continuousAt_const
    · exact continuousAt_const.add (Real.continuous_sqrt.continuousAt.comp (by fun_prop))
    · positivity
  have h0 : (16 * a ^ 2 / (2 + Real.sqrt (4 - 16 * (0 : ℝ) ^ 2 * a ^ 2))) = 4 * a ^ 2 := by
    rw [show (4 : ℝ) - 16 * 0 ^ 2 * a ^ 2 = 2 ^ 2 by ring, Real.sqrt_sq (by norm_num)]; ring
  rw [← h0]
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  unfold Tw
  field_simp

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

/-- The weights for `α`. -/
def Tα (α : 𝓞 K) (s : ℝ) : CP K → ℝ := fun w => Tw ‖bα α w‖ s

lemma norm_bα_pos (α : 𝓞 K) (hα : α ≠ 0) (w : CP K) : 0 < ‖bα α w‖ := by
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  unfold bα
  rw [norm_pos_iff, map_ne_zero]
  exact inv_ne_zero hαK

lemma norm_bα (α : 𝓞 K) (w : CP K) : ‖bα α w‖ = (w.1 (α : K))⁻¹ := by
  unfold bα
  rw [InfinitePlace.norm_embedding_eq, map_inv₀]

lemma conj_bα (α : 𝓞 K) (w : CP K) :
    conj (bα α w) = ((‖bα α w‖ ^ 2 : ℝ) : ℂ) * w.1.embedding (α : K) := by
  unfold bα
  rw [map_inv₀]
  set z := w.1.embedding (α : K)
  rw [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  conv_lhs => rw [Complex.inv_def]
  rw [map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

/-- The dual phase. -/
def Eα (α : 𝓞 K) (s : ℝ) (η : K) : ℂ :=
  Complex.exp (-(4 * π * Complex.I * ((s * ∑ w : CP K,
    (conj (bα α w) * (w.1.embedding η) ^ 2).re / Tα α s w : ℝ) : ℂ)))

/-- The dual-side ideal `1^∨`. -/
abbrev D1 (K : Type*) [Field K] [NumberField K] : Set K :=
  ((FractionalIdeal.dual ℤ ℚ (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    FractionalIdeal (𝓞 K)⁰ K) : Set K)

/-- The dual sum. -/
def Sig (α : 𝓞 K) (s : ℝ) : ℂ :=
  ∑' η : D1 K, ((Real.exp (-(π * s * nsq (mixedEmbedding K (η : K))))) : ℂ) * Eα α s η

/-- The dual prefactor. -/
def Pα (α : 𝓞 K) (s : ℝ) : ℝ := ∏ w : CP K, (Real.sqrt (4 * Tα α s w / s))⁻¹

lemma F1_eq {T a s : ℝ} (hTpos : 0 < T) (hs : 0 < s) (hT : T ^ 2 + 16 * a ^ 2 = 4 * T / s)
    (b η : ℂ) (hb : ‖b‖ = a) :
    F1 T b η = (((Real.sqrt (4 * T / s))⁻¹ * Real.exp (-(π * s * ‖η‖ ^ 2)) : ℝ) : ℂ) *
      Complex.exp (-(4 * π * Complex.I * ((s * (conj b * η ^ 2).re / T : ℝ) : ℂ))) := by
  unfold F1
  rw [hb, hT]
  push_cast
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 2
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hTpos.ne'
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp
  ring

/-- **The dual side.** -/
theorem dual_eq (α : 𝓞 K) (hα : α ≠ 0) {s : ℝ} (hs : 0 < s)
    (hsmall : ∀ w, s * ‖bα α w‖ ≤ 1 / 2) :
    ∑' x : 𝓞 K, phiS (Tα α s) (bα α) (mixedEmbedding K x) =
      ((ZLattice.covolume (idealLattice K 1) : ℝ) : ℂ)⁻¹ * (Pα α s : ℂ) * Sig α s := by
  have hT : ∀ w, 0 < Tα α s w := fun w => Tw_pos (norm_bα_pos α hα w) hs
  have h := L3P.tsum_dil_eq 1 (phiS (Tα α s) (bα α)) 0 0
  simp only [L3P.dilV_zero, one_mul, neg_zero, Pi.zero_apply, Finset.sum_const_zero,
    Real.exp_zero, mul_one, zero_add, zero_mul, map_zero, AddChar.map_zero_eq_one, OneMemClass.coe_one] at h
  rw [← (oneEquiv (K := K)).tsum_eq
    (fun a => phiS (Tα α s) (bα α) (mixedEmbedding K (a : K)))] at h
  simp only [oneEquiv, Equiv.ofBijective_apply] at h
  rw [h, mul_assoc]
  congr 1
  rw [Sig, ← tsum_mul_left]
  refine tsum_congr fun η => ?_
  rw [show (Real.fourierChar ((0 : ℚ) : ℝ) : ℂ) = 1 by simp, mul_one]
  rw [fourierM_phiS (Tα α s) hT (bα α)]
  rw [Finset.prod_congr rfl fun w _ => F1_eq (hT w) hs
    (Tw_eq (norm_bα_pos α hα w) hs (hsmall w)) (bα α w) _ rfl]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, Finset.prod_mul_distrib, ← Real.exp_sum,
    ← Complex.exp_sum, Pα, Eα, nsq]
  push_cast
  simp only [mixedEmbedding_apply_isComplex]
  rw [mul_assoc]
  congr 2
  · congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  · congr 1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast
    ring

/-- The small dual phase. -/
def eps (α : 𝓞 K) (s : ℝ) (η : K) : ℝ :=
  ∑ w : CP K, (w.1.embedding ((α : K) * η ^ 2)).re * s * Tα α s w / 4

/-- **The dual phase splits off `e(−Tr(α η²)/4)`.** -/
theorem Eα_eq (α : 𝓞 K) (hα : α ≠ 0) {s : ℝ} (hs : 0 < s)
    (hsmall : ∀ w, s * ‖bα α w‖ ≤ 1 / 2) (η : K) :
    Eα α s η = Complex.exp (-(π * Complex.I * ((Algebra.trace ℚ K ((α : K) * η ^ 2) : ℝ) : ℂ) / 2)) *
      Complex.exp (π * Complex.I * ((eps α s η : ℝ) : ℂ)) := by
  have hT : ∀ w, 0 < Tα α s w := fun w => Tw_pos (norm_bα_pos α hα w) hs
  have key : ∀ w : CP K, s * (conj (bα α w) * (w.1.embedding η) ^ 2).re / Tα α s w =
      (w.1.embedding ((α : K) * η ^ 2)).re / 4 -
        (w.1.embedding ((α : K) * η ^ 2)).re * s * Tα α s w / 16 := by
    intro w
    rw [show Tα α s w = Tw ‖bα α w‖ s from rfl]
    have he := Tw_eq (norm_bα_pos α hα w) hs (hsmall w)
    have hTw : 0 < Tw ‖bα α w‖ s := hT w
    rw [conj_bα, map_mul, map_pow, mul_assoc, Complex.re_ofReal_mul]
    change s * (‖bα α w‖ ^ 2 * _) / Tw ‖bα α w‖ s = _
    change Tw ‖bα α w‖ s ^ 2 + 16 * ‖bα α w‖ ^ 2 = 4 * Tw ‖bα α w‖ s / s at he
    set T := Tw ‖bα α w‖ s
    set a := ‖bα α w‖
    have ha2 : a ^ 2 = (4 * T / s - T ^ 2) / 16 := by linarith
    have hT0 : T ≠ 0 := hTw.ne'
    rw [ha2]
    field_simp
    ring
  unfold Eα eps
  rw [← Complex.exp_add]
  congr 1
  set A : ℂ := ∑ w : CP K, (((w.1.embedding ((α : K) * η ^ 2)).re : ℝ) : ℂ)
  set B : ℂ := ∑ w : CP K, (((w.1.embedding ((α : K) * η ^ 2)).re * s * Tα α s w : ℝ) : ℂ)
  have h1 : ((s * ∑ w : CP K, (conj (bα α w) * (w.1.embedding η) ^ 2).re / Tα α s w : ℝ) : ℂ) =
      A / 4 - B / 16 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun w _ => by rw [mul_div_assoc', key w]]
    simp only [A, B]
    push_cast
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  have h2 : ((Algebra.trace ℚ K ((α : K) * η ^ 2) : ℝ) : ℂ) = 2 * A := by
    rw [← traceForm_eq_trace]
    simp only [A]
    push_cast
    rw [Finset.mul_sum]
  have h3 : ((∑ w : CP K, (w.1.embedding ((α : K) * η ^ 2)).re * s * Tα α s w / 4 : ℝ) : ℂ) =
      B / 4 := by
    simp only [B]
    push_cast
    rw [Finset.sum_div]
  rw [h1, h2, h3]
  ring

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Hk3: arithmetic facts for Hecke's Gauss sum

* `dual_phase_agree`: for `α ≡ 1 (mod 4𝔇)` and `η ∈ 𝔇⁻¹`, `e(−Tr(α η²)/4) = e(−Tr(η²)/4)`;
* `gsum_one`: `g(1) = 1`; `ne_zero_of_hecke`: such `α` is nonzero;
* `covol_Iα`: `covol((α)) = N(α) covol(𝓞)`; `prod_place_eq`: `∏_w w(α) = √N(α)`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical SchwartzMap Real nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {K : Type*} [Field K] [NumberField K]

lemma not_isUnit_four : ¬ IsUnit (4 : 𝓞 K) := by
  rintro ⟨u, hu⟩
  have h1 : IsIntegral ℤ ((1 / 4 : ℚ) : K) := by
    have : ((1 / 4 : ℚ) : K) = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := by
      have h2 : ((u : 𝓞 K) : K) = 4 := by rw [hu]; rfl
      have h3 : ((u : 𝓞 K) : K) * (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
        rw [← map_mul (algebraMap (𝓞 K) K), Units.mul_inv, map_one]
      rw [h2] at h3
      push_cast
      linear_combination -h3 / 4
    rw [this]
    exact RingOfIntegers.isIntegral_coe _
  rw [show ((1 / 4 : ℚ) : K) = algebraMap ℚ K (1/4) by simp, isIntegral_algebraMap_iff
    (algebraMap ℚ K).injective] at h1
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have : (m : ℚ) = 1 / 4 := hm
  have h4 : (m : ℚ) * 4 = 1 := by rw [this]; norm_num
  have h5 : m * 4 = 1 := by exact_mod_cast h4
  omega

lemma ne_zero_of_hecke {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 K)} * differentIdeal ℤ (𝓞 K)) : α ≠ 0 := by
  intro h0
  rw [h0, zero_sub] at hα
  have hle : Ideal.span {(4 : 𝓞 K)} * differentIdeal ℤ (𝓞 K) ≤ Ideal.span {(4 : 𝓞 K)} :=
    Ideal.mul_le_left
  have h1 : (-1 : 𝓞 K) ∈ Ideal.span {(4 : 𝓞 K)} := hle hα
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h1
  exact not_isUnit_four (isUnit_iff_exists_inv.mpr ⟨-r, by linear_combination -hr⟩)

lemma trace_mem_int_of_dual {η : K}
    (hη : η ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) {d : 𝓞 K}
    (hd : d ∈ differentIdeal ℤ (𝓞 K)) :
    ∃ n : ℤ, Algebra.trace ℚ K ((d : K) * η ^ 2) = n := by
  have h1 : ((d : K)) ∈ ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)] at h1
  have h10 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  have h2 : (d : K) * η ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have := FractionalIdeal.mul_mem_mul h1 hη
    rwa [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)] at this
  obtain ⟨e, he⟩ := (FractionalIdeal.mem_one_iff _).1 h2
  have h3 := (FractionalIdeal.mem_dual h10).1 hη (algebraMap (𝓞 K) K e)
    ((FractionalIdeal.mem_one_iff _).2 ⟨e, rfl⟩)
  obtain ⟨n, hn⟩ := h3
  refine ⟨n, ?_⟩
  rw [Algebra.traceForm_apply, he] at hn
  rw [show (d : K) * η ^ 2 = η * ((d : K) * η) by ring, ← hn]
  simp

/-- **The dual main phases agree.** -/
lemma dual_phase_agree {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 K)} * differentIdeal ℤ (𝓞 K)) {η : K}
    (hη : η ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    Complex.exp (-(π * Complex.I * ((Algebra.trace ℚ K ((α : K) * η ^ 2) : ℝ) : ℂ) / 2)) =
      Complex.exp (-(π * Complex.I * ((Algebra.trace ℚ K ((1 : 𝓞 K) * η ^ 2 : K) : ℝ) : ℂ) / 2)) := by
  obtain ⟨d, hd, hd4⟩ := Ideal.mem_span_singleton_mul.mp hα
  obtain ⟨n, hn⟩ := trace_mem_int_of_dual hη hd
  have hαd : (α : K) = 1 + 4 * d := by
    have := congrArg (algebraMap (𝓞 K) K) hd4
    rw [map_mul, map_ofNat, map_sub, map_one] at this
    change 4 * (d : K) = (α : K) - 1 at this
    linear_combination -this
  have htr : Algebra.trace ℚ K ((α : K) * η ^ 2) = Algebra.trace ℚ K (η ^ 2) + 4 * n := by
    rw [hαd, show (1 + 4 * (d : K)) * η ^ 2 = η ^ 2 + (4 : ℚ) • ((d : K) * η ^ 2) by
      rw [Algebra.smul_def]; simp; ring, map_add, LinearMap.map_smul, hn, smul_eq_mul]
  rw [htr]
  push_cast
  rw [show -(↑π * Complex.I * ((((Algebra.trace ℚ K) (η ^ 2) : ℚ) : ℂ) + 4 * (n : ℂ)) / 2) =
      -(↑π * Complex.I * (((Algebra.trace ℚ K) (η ^ 2) : ℚ) : ℂ) / 2) + (-n : ℤ) * (2 * π * Complex.I)
    by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Hk4: the limit of `s^{r₂} Σ_γ(s)`

`sig_limit`: `s^{r₂} Σ_γ(s) → covol(𝓞) (∏_w w(γ)) g(γ) / covol((γ))` as `s → 0⁺`, from the dual identity
`dual_eq`, the primal limit `primal_limit` and `T_w(s)/s → 4|γ_w|^{-2}`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical SchwartzMap Real nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {K : Type*} [Field K] [NumberField K]

lemma absNorm_eq_abs_norm (α : 𝓞 K) :
    ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) = |((Algebra.norm ℚ (α : K) : ℚ) : ℝ)| := by
  rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
  push_cast
  rfl

variable [IsTotallyComplex K]

lemma gsum_one : gsum (1 : 𝓞 K) = 1 := by
  unfold gsum
  rw [Ideal.span_singleton_one]
  haveI : Subsingleton (𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [finsum_eq_single _ (0 : 𝓞 K ⧸ (⊤ : Ideal (𝓞 K)))
    (fun x hx => absurd (Subsingleton.elim x 0) hx)]
  obtain ⟨n, hn⟩ := trace_int ((Quotient.out (0 : 𝓞 K ⧸ (⊤ : Ideal (𝓞 K)))) ^ 2)
  push_cast at hn
  rw [show ((1 : 𝓞 K) : K) = 1 from rfl, div_one, hn]
  push_cast
  rw [show 2 * (π : ℂ) * Complex.I * n = n * (2 * π * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n


lemma covol_Iα (α : 𝓞 K) (hα : α ≠ 0) :
    ZLattice.covolume (idealLattice K (Iα α hα)) =
      ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) * ZLattice.covolume (idealLattice K 1) := by
  rw [covolume_idealLattice, covolume_idealLattice, Units.val_one, FractionalIdeal.absNorm_one]
  simp only [Iα, Units.val_mk0, FractionalIdeal.absNorm_span_singleton]
  rw [absNorm_eq_abs_norm]
  push_cast
  ring

lemma prod_place_eq (α : 𝓞 K) :
    ∏ w : CP K, w.1 (α : K) = Real.sqrt ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  have h := prod_eq_abs_norm (α : K)
  rw [absNorm_eq_abs_norm, ← Rat.cast_abs, ← h, ← L3P.prod_complex_eq (K := K)]
  simp only [L3P.mult_eq_two]
  rw [Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun w _ => apply_nonneg _ _)]

lemma Tα_le (α : 𝓞 K) {s : ℝ} (hs : 0 < s) (w : CP K) :
    Tα α s w ≤ 8 * s * (1 + ∑ w' : CP K, ‖bα α w'‖ ^ 2) := by
  refine (Tw_le hs).trans ?_
  have : ‖bα α w‖ ^ 2 ≤ 1 + ∑ w' : CP K, ‖bα α w'‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun w' : CP K => ‖bα α w'‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ w)
    linarith
  have hs8 : 0 ≤ 8 * s := by positivity
  exact mul_le_mul_of_nonneg_left this hs8

lemma eventually_small (α : 𝓞 K) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ w, s * ‖bα α w‖ ≤ 1 / 2 := by
  set M := 1 + ∑ w : CP K, ‖bα α w‖
  have hM : 0 < M := by positivity
  have : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 / (2 * M) := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [this, self_mem_nhdsWithin] with s hs (hs0 : 0 < s) w
  have hb : ‖bα α w‖ ≤ M := by
    have := Finset.single_le_sum (f := fun w' : CP K => ‖bα α w'‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ w)
    simp only [M]; linarith
  calc s * ‖bα α w‖ ≤ s * M := mul_le_mul_of_nonneg_left hb hs0.le
    _ ≤ 1 / (2 * M) * M := mul_le_mul_of_nonneg_right hs.le hM.le
    _ = 1 / 2 := by field_simp

/-- **The limit of the normalized dual sum.** -/
theorem sig_limit (γ : 𝓞 K) (hγ : γ ≠ 0) :
    Tendsto (fun s : ℝ => ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * Sig γ s) (𝓝[>] 0)
      (𝓝 ((ZLattice.covolume (idealLattice K 1) : ℂ) * ((∏ w : CP K, w.1 (γ : K) : ℝ) : ℂ) *
        gsum γ / (ZLattice.covolume (idealLattice K (Iα γ hγ)) : ℂ))) := by
  set c₁ := ZLattice.covolume (idealLattice K 1)
  set cγ := ZLattice.covolume (idealLattice K (Iα γ hγ))
  have hc₁ : 0 < c₁ := covol_pos 1
  have hcγ : 0 < cγ := covol_pos _
  set M := 1 + ∑ w' : CP K, ‖bα γ w'‖ ^ 2
  have hM : 0 < M := by positivity
  have hT : ∀ s, 0 < s → ∀ w, 0 < Tα γ s w := fun s hs w => Tw_pos (norm_bα_pos γ hγ w) hs
  -- the primal limit
  have hprim := primal_limit γ hγ (Tα γ) hT (fun s => 8 * s * M)
    (by
      have h1 : Tendsto (fun s : ℝ => 8 * s * M) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun s : ℝ => 8 * s * M) (𝓝 0) (𝓝 (8 * 0 * M)) := by
          exact ((tendsto_const_nhds.mul tendsto_id).mul tendsto_const_nhds)
        simpa using this.mono_left nhdsWithin_le_nhds
      refine tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      show 0 < 8 * s * M
      positivity)
    (fun s hs w => Tα_le γ hs w) (fun s hs => by positivity)
  -- the factor `∏ 2√(s/T_w) → ∏ w(γ)`
  have hQ : Tendsto (fun s : ℝ => ∏ w : CP K, 2 * Real.sqrt (s / Tα γ s w)) (𝓝[>] 0)
      (𝓝 (∏ w : CP K, w.1 (γ : K))) := by
    refine tendsto_finsetProd _ fun w _ => ?_
    have ha := norm_bα_pos γ hγ w
    have h1 := (Tw_div_tendsto (a := ‖bα γ w‖)).inv₀ (by positivity)
    have h2 : Tendsto (fun s => s / Tα γ s w) (𝓝[>] 0) (𝓝 (4 * ‖bα γ w‖ ^ 2)⁻¹) := by
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      simp only [Tα]; rw [inv_div]
    have h3 := (Real.continuous_sqrt.tendsto _).comp h2
    have h4 := h3.const_mul 2
    have hval : 2 * Real.sqrt (4 * ‖bα γ w‖ ^ 2)⁻¹ = w.1 (γ : K) := by
      rw [norm_bα, Real.sqrt_inv, show 4 * (w.1 (γ : K))⁻¹ ^ 2 = (2 * (w.1 (γ : K))⁻¹) ^ 2 by ring,
        Real.sqrt_sq (by have := ha; rw [norm_bα] at this; positivity)]
      have : w.1 (γ : K) ≠ 0 := by
        have := ha; rw [norm_bα] at this; exact (inv_pos.mp this).ne'
      field_simp
    rw [← hval]
    exact h4
  -- assemble
  have hlim := ((tendsto_const_nhds (x := (c₁ : ℂ))).mul ((Complex.continuous_ofReal.tendsto _).comp hQ)).mul
    (hprim.div_const (cγ : ℂ))
  rw [show (c₁ : ℂ) * ((∏ w : CP K, w.1 (γ : K) : ℝ) : ℂ) * gsum γ / (cγ : ℂ) =
    (c₁ : ℂ) * ((∏ w : CP K, w.1 (γ : K) : ℝ) : ℂ) * (gsum γ / (cγ : ℂ)) by ring]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_small γ] with s (hs : 0 < s) hsmall
  have hd := dual_eq γ hγ hs hsmall
  change _ = ((c₁ : ℝ) : ℂ)⁻¹ * _ * _ at hd
  have hP : 0 < Pα γ s := Finset.prod_pos fun w _ =>
    inv_pos.mpr (Real.sqrt_pos.mpr (by have := hT s hs w; positivity))
  have hPC : (Pα γ s : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hc₁C : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁.ne'
  have hcγC : (cγ : ℂ) ≠ 0 := by exact_mod_cast hcγ.ne'
  have hsig : Sig γ s = (c₁ : ℂ) * (Pα γ s : ℂ)⁻¹ *
      ∑' x : 𝓞 K, phiS (Tα γ s) (bα γ) (mixedEmbedding K x) := by
    rw [hd]; field_simp
  rw [hsig]
  simp only [Function.comp]
  have hprodQ : ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * (Pα γ s : ℂ)⁻¹ =
      ((∏ w : CP K, 2 * Real.sqrt (s / Tα γ s w) : ℝ) : ℂ) * ((∏ w : CP K, Tα γ s w : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Pα, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    have hTw := hT s hs w
    rw [inv_inv, show 4 * Tα γ s w / s = (2 * Real.sqrt (Tα γ s w / s)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring, Real.sqrt_sq (by positivity),
      Real.sqrt_div' _ hTw.le, Real.sqrt_div' _ hs.le]
    have h1 := Real.sqrt_pos.mpr hTw
    have h2 := Real.sqrt_pos.mpr hs
    have h3 : Real.sqrt (Tα γ s w) ^ 2 = Tα γ s w := Real.sq_sqrt hTw.le
    have h4 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
    field_simp
    nlinarith [h3, h4]
  have key : ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * ((c₁ : ℂ) * (Pα γ s : ℂ)⁻¹ *
        ∑' x : 𝓞 K, phiS (Tα γ s) (bα γ) (mixedEmbedding K x)) =
      (c₁ : ℂ) * ((∏ w : CP K, 2 * Real.sqrt (s / Tα γ s w) : ℝ) : ℂ) *
        (((∏ w : CP K, Tα γ s w : ℝ) : ℂ) * (cγ : ℂ) *
          (∑' x : 𝓞 K, phiS (Tα γ s) (bα γ) (mixedEmbedding K x)) / (cγ : ℂ)) := by
    rw [show ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * ((c₁ : ℂ) * (Pα γ s : ℂ)⁻¹ *
        ∑' x : 𝓞 K, phiS (Tα γ s) (bα γ) (mixedEmbedding K x)) = (c₁ : ℂ) *
        (((s ^ Fintype.card (CP K) : ℝ) : ℂ) * (Pα γ s : ℂ)⁻¹) *
        ∑' x : 𝓞 K, phiS (Tα γ s) (bα γ) (mixedEmbedding K x) by ring, hprodQ]
    field_simp
  exact key.symm

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Hk5: Hecke's quadratic Gauss sum for a totally complex field

`sig_diff`: for `α ≡ 1 (mod 4𝔇)`, `s^{r₂} (Σ_α(s) − Σ_1(s)) → 0`: the dual main phases agree on `𝔇⁻¹`
(`dual_phase_agree`), the remaining phases differ by `O(s² |η|²)`, and the Gaussian sums are
`O(s^{-r₂})` (`gauss_err`).

`hecke_gauss`: `Σ_{x ∈ 𝓞/(α)} e(Tr(x²/α)) = √N(α)` for `α ≡ 1 (mod 4𝔇)`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical SchwartzMap Real nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

lemma mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) : u * Real.exp (-u) ≤ Real.exp (-(u / 2)) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ u / 2)
  have h2 : u ≤ Real.exp (u / 2) := by nlinarith
  calc u * Real.exp (-u) ≤ Real.exp (u / 2) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-(u / 2)) := by rw [← Real.exp_add]; ring_nf

lemma norm_exp_sub_le (x y : ℝ) :
    ‖Complex.exp (π * Complex.I * (x : ℂ)) - Complex.exp (π * Complex.I * (y : ℂ))‖ ≤
      π * (|x| + |y|) := by
  have hx : ‖Complex.exp (Complex.I * ((π * x : ℝ) : ℂ)) - 1‖ ≤ ‖π * x‖ :=
    Real.norm_exp_I_mul_ofReal_sub_one_le
  have hy : ‖Complex.exp (Complex.I * ((π * y : ℝ) : ℂ)) - 1‖ ≤ ‖π * y‖ :=
    Real.norm_exp_I_mul_ofReal_sub_one_le
  have ex : Complex.exp (π * Complex.I * (x : ℂ)) = Complex.exp (Complex.I * ((π * x : ℝ) : ℂ)) := by
    push_cast; ring_nf
  have ey : Complex.exp (π * Complex.I * (y : ℂ)) = Complex.exp (Complex.I * ((π * y : ℝ) : ℂ)) := by
    push_cast; ring_nf
  rw [ex, ey, show Complex.exp (Complex.I * ((π * x : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((π * y : ℝ) : ℂ)) =
      (Complex.exp (Complex.I * ((π * x : ℝ) : ℂ)) - 1) -
        (Complex.exp (Complex.I * ((π * y : ℝ) : ℂ)) - 1) by ring]
  refine (norm_sub_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] at hx hy
  nlinarith

/-- The bound on the small phase. -/
lemma abs_eps_le (γ : 𝓞 K) (hγ : γ ≠ 0) {s : ℝ} (hs : 0 < s) (η : K) :
    |eps γ s η| ≤ 2 * s ^ 2 * (∑ w : CP K, ‖bα γ w‖) * nsq (mixedEmbedding K η) := by
  unfold eps nsq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have hb := norm_bα_pos γ hγ w
  have hT := Tw_le (a := ‖bα γ w‖) hs
  have hTpos := Tw_pos hb hs
  have hgb : ‖w.1.embedding (γ : K)‖ * ‖bα γ w‖ = 1 := by
    rw [norm_bα, InfinitePlace.norm_embedding_eq]
    have : w.1 (γ : K) ≠ 0 := by
      have := hb; rw [norm_bα] at this; exact (inv_pos.mp this).ne'
    field_simp
  have hre : |(w.1.embedding ((γ : K) * η ^ 2)).re| ≤
      ‖w.1.embedding (γ : K)‖ * ‖(mixedEmbedding K η).2 w‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [map_mul, map_pow, norm_mul, norm_pow, mixedEmbedding_apply_isComplex]
  have hbsum : ‖bα γ w‖ ≤ ∑ w' : CP K, ‖bα γ w'‖ :=
    Finset.single_le_sum (f := fun w' : CP K => ‖bα γ w'‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ w)
  change |(w.1.embedding ((γ : K) * η ^ 2)).re * s * Tw ‖bα γ w‖ s / 4| ≤ _
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hTpos, abs_of_pos (by norm_num : (0:ℝ) < 4)]
  have hn : 0 ≤ ‖(mixedEmbedding K η).2 w‖ ^ 2 := sq_nonneg _
  calc |(w.1.embedding ((γ : K) * η ^ 2)).re| * s * Tw ‖bα γ w‖ s / 4
      ≤ (‖w.1.embedding (γ : K)‖ * ‖(mixedEmbedding K η).2 w‖ ^ 2) * s * (8 * s * ‖bα γ w‖ ^ 2) / 4 := by
        gcongr
    _ = 2 * s ^ 2 * (‖w.1.embedding (γ : K)‖ * ‖bα γ w‖) * ‖bα γ w‖ *
          ‖(mixedEmbedding K η).2 w‖ ^ 2 := by ring
    _ = 2 * s ^ 2 * ‖bα γ w‖ * ‖(mixedEmbedding K η).2 w‖ ^ 2 := by rw [hgb]; ring
    _ ≤ 2 * s ^ 2 * (∑ w' : CP K, ‖bα γ w'‖) * ‖(mixedEmbedding K η).2 w‖ ^ 2 := by gcongr

/-- The Gaussian sum over `𝔇⁻¹` with weight `s/2`. -/
def Gs (s : ℝ) : ℝ := ∑' η : D1 K, Real.exp (-(π * (s / 2) * nsq (mixedEmbedding K (η : K))))

lemma summable_G {s : ℝ} (hs : 0 < s) :
    Summable fun η : D1 K => Real.exp (-(π * (s / 2) * nsq (mixedEmbedding K (η : K)))) := by
  have := summable_dual_gauss (K := K) 1 (τ := 8 / s) (by positivity)
  refine this.congr fun η => ?_
  congr 1
  field_simp
  ring

lemma summable_sig (γ : 𝓞 K) {s : ℝ} (hs : 0 < s) :
    Summable fun η : D1 K =>
      ((Real.exp (-(π * s * nsq (mixedEmbedding K (η : K))))) : ℂ) * Eα γ s η := by
  have := summable_dual_gauss (K := K) 1 (τ := 4 / s) (by positivity)
  refine Summable.of_norm (this.congr fun η => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hE : ‖Eα γ s η‖ = 1 := by
    unfold Eα
    rw [show -(4 * (π : ℂ) * Complex.I * (((s * ∑ w : CP K,
        ((starRingEnd ℂ) (bα γ w) * (w.1.embedding (η : K)) ^ 2).re / Tα γ s w : ℝ)) : ℂ)) =
        ((-(4 * π * (s * ∑ w : CP K,
        ((starRingEnd ℂ) (bα γ w) * (w.1.embedding (η : K)) ^ 2).re / Tα γ s w)) : ℝ) : ℂ) *
          Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hE, mul_one]
  congr 1
  field_simp

/-- `s^{r₂} G(s)` is bounded near `0`. -/
lemma G_bound : ∀ᶠ s in 𝓝[>] (0 : ℝ),
    s ^ Fintype.card (CP K) * Gs (K := K) s ≤
      2 ^ (Fintype.card (CP K) + 1) / ZLattice.covolume (idealLattice K (dualU 1)) := by
  set c' := ZLattice.covolume (idealLattice K (dualU (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)))
  have hc' : 0 < c' := covol_pos _
  have h2 : Tendsto (fun s : ℝ => s / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => s / 2) (𝓝 0) (𝓝 (0 / 2)) := tendsto_id.div_const 2
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      show 0 < s / 2; positivity
  have herr := ((errE_tendsto (dualU (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))).comp h2).eventually
    (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [herr, self_mem_nhdsWithin] with s hs1 (hs : 0 < s)
  simp only [Function.comp, Set.mem_Iic] at hs1
  have hT : ∀ w : CP K, 0 < (fun _ => s / 2) w := fun _ => by positivity
  have hg := gauss_err (dualU (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) (fun _ => s / 2) hT
    (τ := s / 2) (by positivity) (fun _ => le_rfl) 0
  have hsum : ∑' a : (((dualU (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K), phiS (fun _ => s / 2) 0 (mixedEmbedding K (0 + a)) =
      ((Gs (K := K) s : ℝ) : ℂ) := by
    rw [Gs, Complex.ofReal_tsum]
    refine tsum_congr fun a => ?_
    rw [zero_add, phiS_zero_apply _ hT]
    congr 2
    simp only [nsq, ← Finset.mul_sum]
    ring
  rw [hsum, Finset.prod_const, Finset.card_univ] at hg
  set X := (s / 2) ^ Fintype.card (CP K) * c' * Gs (K := K) s
  have hX : ‖((X : ℝ) : ℂ) - 1‖ ≤ 1 := by
    refine le_trans (le_of_eq ?_) (hg.trans hs1)
    congr 1
    simp only [X]
    push_cast
    ring
  have hX2 : X ≤ 2 := by
    have := (Complex.abs_re_le_norm (((X : ℝ) : ℂ) - 1)).trans hX
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at this
    have := (abs_le.mp this).2
    linarith
  rw [le_div_iff₀ hc']
  simp only [X] at hX2
  rw [div_pow] at hX2
  have h2p : (0 : ℝ) < 2 ^ Fintype.card (CP K) := by positivity
  have : s ^ Fintype.card (CP K) * c' * Gs (K := K) s ≤ 2 * 2 ^ Fintype.card (CP K) := by
    have := mul_le_mul_of_nonneg_left hX2 h2p.le
    rw [show 2 ^ Fintype.card (CP K) * (s ^ Fintype.card (CP K) / 2 ^ Fintype.card (CP K) * c' *
      Gs (K := K) s) = s ^ Fintype.card (CP K) * c' * Gs (K := K) s by field_simp] at this
    linarith
  rw [pow_succ]
  linarith

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_Hk6: the comparison and Hecke's quadratic Gauss sum

`sig_diff`: `s^{r₂} (Σ_α(s) − Σ_1(s)) → 0` for `α ≡ 1 (mod 4𝔇)`;
`hecke_gauss`: `g(α) = √N(α)` for such `α` (`K` totally complex).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical SchwartzMap Real nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.L3M

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]

lemma mem_dual_one (η : D1 K) :
    (η : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h := η.2
  change (η : K) ∈ ((FractionalIdeal.dual ℤ ℚ (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal (𝓞 K)⁰ K)) : FractionalIdeal (𝓞 K)⁰ K) : Set K) at h
  rw [Units.val_one] at h
  exact h

/-- The pointwise bound. -/
lemma term_bound {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 K)} * differentIdeal ℤ (𝓞 K)) {s : ℝ} (hs : 0 < s)
    (hsα : ∀ w, s * ‖bα α w‖ ≤ 1 / 2) (hs1 : ∀ w, s * ‖bα (1 : 𝓞 K) w‖ ≤ 1 / 2) (η : D1 K) :
    ‖((Real.exp (-(π * s * nsq (mixedEmbedding K (η : K))))) : ℂ) * (Eα α s (η : K) - Eα (1 : 𝓞 K) s (η : K))‖ ≤
      2 * s * ((∑ w : CP K, ‖bα α w‖) + ∑ w : CP K, ‖bα (1 : 𝓞 K) w‖) *
        Real.exp (-(π * (s / 2) * nsq (mixedEmbedding K (η : K)))) := by
  have hα0 := ne_zero_of_hecke hα
  rw [Eα_eq α hα0 hs hsα, Eα_eq 1 one_ne_zero hs hs1, dual_phase_agree hα (mem_dual_one η),
    ← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hph : ‖Complex.exp (-(π * Complex.I *
      ((Algebra.trace ℚ K ((1 : 𝓞 K) * (η : K) ^ 2 : K) : ℝ) : ℂ) / 2))‖ = 1 := by
    rw [show -(π * Complex.I * ((Algebra.trace ℚ K ((1 : 𝓞 K) * (η : K) ^ 2 : K) : ℝ) : ℂ) / 2) =
      ((-(π * (Algebra.trace ℚ K ((1 : 𝓞 K) * (η : K) ^ 2 : K) : ℝ) / 2)) : ℝ) * Complex.I by
        push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hph, one_mul]
  set n := nsq (mixedEmbedding K (η : K))
  have hn : 0 ≤ n := nsq_nonneg _
  set B := (∑ w : CP K, ‖bα α w‖) + ∑ w : CP K, ‖bα (1 : 𝓞 K) w‖
  have hB : 0 ≤ B := by positivity
  have h1 := norm_exp_sub_le (eps α s (η : K)) (eps (1 : 𝓞 K) s (η : K))
  have h2 := abs_eps_le α hα0 hs (η : K)
  have h3 := abs_eps_le (1 : 𝓞 K) one_ne_zero hs (η : K)
  have h4 : ‖Complex.exp (π * Complex.I * ((eps α s (η : K) : ℝ) : ℂ)) -
      Complex.exp (π * Complex.I * ((eps (1 : 𝓞 K) s (η : K) : ℝ) : ℂ))‖ ≤ π * (2 * s ^ 2 * B * n) := by
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    simp only [B]
    nlinarith
  have h5 := mul_exp_neg_le (u := π * s * n) (by positivity)
  calc Real.exp (-(π * s * n)) * ‖Complex.exp (π * Complex.I * ((eps α s (η : K) : ℝ) : ℂ)) -
        Complex.exp (π * Complex.I * ((eps (1 : 𝓞 K) s (η : K) : ℝ) : ℂ))‖
      ≤ Real.exp (-(π * s * n)) * (π * (2 * s ^ 2 * B * n)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = 2 * s * B * ((π * s * n) * Real.exp (-(π * s * n))) := by ring
    _ ≤ 2 * s * B * Real.exp (-(π * s * n / 2)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 2 * s * B * Real.exp (-(π * (s / 2) * n)) := by ring_nf

/-- **The comparison.** -/
theorem sig_diff {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 K)} * differentIdeal ℤ (𝓞 K)) :
    Tendsto (fun s : ℝ => ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * (Sig α s - Sig (1 : 𝓞 K) s)) (𝓝[>] 0)
      (𝓝 0) := by
  set B := (∑ w : CP K, ‖bα α w‖) + ∑ w : CP K, ‖bα (1 : 𝓞 K) w‖
  set c' := ZLattice.covolume (idealLattice K (dualU (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)))
  set C := 2 * B * (2 ^ (Fintype.card (CP K) + 1) / c')
  have hlim : Tendsto (fun s : ℝ => C * s) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => C * s) (𝓝 0) (𝓝 (C * 0)) := tendsto_id.const_mul C
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin, eventually_small α, eventually_small (1 : 𝓞 K), G_bound (K := K)]
    with s (hs : 0 < s) hsα hs1 hG
  rw [Sig, Sig, ← (summable_sig α hs).tsum_sub (summable_sig (1 : 𝓞 K) hs)]
  simp_rw [← mul_sub]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsumB : Summable fun η : D1 K => 2 * s * B *
      Real.exp (-(π * (s / 2) * nsq (mixedEmbedding K (η : K)))) :=
    (summable_G hs).mul_left _
  have hsumF : Summable fun η : D1 K =>
      ‖((Real.exp (-(π * s * nsq (mixedEmbedding K (η : K))))) : ℂ) *
        (Eα α s (η : K) - Eα (1 : 𝓞 K) s (η : K))‖ :=
    hsumB.of_nonneg_of_le (fun _ => norm_nonneg _) (fun η => term_bound hα hs hsα hs1 η)
  have hnorm := norm_tsum_le_tsum_norm hsumF
  have hle := Summable.tsum_le_tsum (fun η => term_bound hα hs hsα hs1 η) hsumF hsumB
  rw [tsum_mul_left] at hle
  have hGs : Gs (K := K) s = ∑' η : D1 K, Real.exp (-(π * (s / 2) * nsq (mixedEmbedding K (η : K)))) := rfl
  rw [← hGs] at hle
  have hspos : 0 ≤ s ^ Fintype.card (CP K) := by positivity
  have hB : 0 ≤ B := by positivity
  calc s ^ Fintype.card (CP K) * ‖∑' η : D1 K, ((Real.exp (-(π * s * nsq (mixedEmbedding K (η : K))))) : ℂ) *
        (Eα α s (η : K) - Eα (1 : 𝓞 K) s (η : K))‖
      ≤ s ^ Fintype.card (CP K) * (2 * s * B * Gs (K := K) s) :=
        mul_le_mul_of_nonneg_left (hnorm.trans hle) hspos
    _ = 2 * s * B * (s ^ Fintype.card (CP K) * Gs (K := K) s) := by ring
    _ ≤ 2 * s * B * (2 ^ (Fintype.card (CP K) + 1) / c') :=
        mul_le_mul_of_nonneg_left hG (by positivity)
    _ = C * s := by simp only [C]; ring

/-- **Hecke's quadratic Gauss sum** for a totally complex field. -/
theorem hecke_gauss {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 K)} * differentIdeal ℤ (𝓞 K)) :
    gsum α = ((Real.sqrt (Ideal.absNorm (Ideal.span {α}) : ℝ) : ℝ) : ℂ) := by
  have hα0 := ne_zero_of_hecke hα
  have hLα := sig_limit α hα0
  have hL1 := sig_limit (1 : 𝓞 K) one_ne_zero
  have hD := sig_diff hα
  have hsub := hLα.sub hL1
  have heq : (fun s : ℝ => ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * Sig α s -
      ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * Sig (1 : 𝓞 K) s) =
      fun s : ℝ => ((s ^ Fintype.card (CP K) : ℝ) : ℂ) * (Sig α s - Sig (1 : 𝓞 K) s) := by
    funext s; ring
  rw [heq] at hsub
  have huniq := tendsto_nhds_unique hsub hD
  set c₁ := ZLattice.covolume (idealLattice K 1)
  have hc₁ : 0 < c₁ := covol_pos 1
  set N := Ideal.absNorm (Ideal.span {α})
  have hN : (0 : ℝ) < N := by
    have : N ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hα0
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [covol_Iα α hα0, covol_Iα (1 : 𝓞 K) one_ne_zero, prod_place_eq α, gsum_one] at huniq
  have h1prod : ∏ w : CP K, w.1 ((1 : 𝓞 K) : K) = 1 := by
    simp only [show ((1 : 𝓞 K) : K) = 1 from rfl, map_one, Finset.prod_const_one]
  rw [h1prod, Ideal.span_singleton_one, Ideal.absNorm_top] at huniq
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hc₁C : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁.ne'
  have hNc : ((((N : ℕ) : ℝ) * c₁ : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) * c₁ := mul_pos hN hc₁
    exact_mod_cast this.ne'
  have h1c : ((((1 : ℕ) : ℝ) * c₁ : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ((1 : ℕ) : ℝ) * c₁ := by simp [hc₁]
    exact_mod_cast this.ne'
  rw [sub_eq_zero, div_eq_div_iff hNc h1c] at huniq
  have hsqC : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq0.ne'
  have key : ((Real.sqrt N : ℝ) : ℂ) * gsum α = ((N : ℝ) : ℂ) := by
    have h2 : (c₁ : ℂ) * (c₁ : ℂ) * (((Real.sqrt N : ℝ) : ℂ) * gsum α) =
        (c₁ : ℂ) * (c₁ : ℂ) * ((N : ℝ) : ℂ) := by
      push_cast at huniq ⊢
      linear_combination huniq
    exact mul_left_cancel₀ (mul_ne_zero hc₁C hc₁C) h2
  have hsqC2 : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = ((N : ℝ) : ℂ) := by exact_mod_cast hsq
  calc gsum α = (((Real.sqrt N : ℝ) : ℂ) * gsum α) / ((Real.sqrt N : ℝ) : ℂ) := by field_simp
    _ = ((N : ℝ) : ℂ) / ((Real.sqrt N : ℝ) : ℂ) := by rw [key]
    _ = ((Real.sqrt N : ℝ) : ℂ) := by rw [← hsqC2]; field_simp

end ArtinPrimitiveRoots.L3M

end
end
end

section
section
/-! # L3M_DevH: Hecke's quadratic Gauss sum `finsum_cexp_trace_sq_div_eq_sqrt_absNorm`, sorry-free

The theta series of `L3M_Hk1`–`L3M_Hk6`: lattice Poisson, and comparison of `α` with `1`.
-/

namespace ArtinPrimitiveRoots

open NumberField

theorem finsum_cexp_trace_sq_div_eq_sqrt_absNorm (F : Type*) [Field F] [NumberField F]
    [IsTotallyComplex F] (α : 𝓞 F)
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 F)} * differentIdeal ℤ (𝓞 F)) :
    ∑ᶠ x : 𝓞 F ⧸ Ideal.span {α},
        Complex.exp (2 * Real.pi * Complex.I *
          ((Algebra.trace ℚ F (((Quotient.out x : 𝓞 F) : F) ^ 2 / (α : F)) : ℚ) : ℂ)) =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {α}) : ℝ) : ℝ) : ℂ)
  := L3M.hecke_gauss hα

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (F : Type*) [Field F] [NumberField F]
    [IsTotallyComplex F] (α : 𝓞 F)
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 F)} * differentIdeal ℤ (𝓞 F)) :
    ∑ᶠ x : 𝓞 F ⧸ Ideal.span {α},
        Complex.exp (2 * Real.pi * Complex.I *
          ((Algebra.trace ℚ F (((Quotient.out x : 𝓞 F) : F) ^ 2 / (α : F)) : ℚ) : ℂ)) =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {α}) : ℝ) : ℝ) : ℂ)
  := by
  exact ArtinPrimitiveRoots.finsum_cexp_trace_sq_div_eq_sqrt_absNorm F α hα

end
