-- Prove2me | Definitions.Def_DedekindZeta_Theta
-- name    : DedekindZeta_Theta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:47:43.280364+00:00
-- url     : https://prove2.me/theorems/187ecd35-971b-4932-b418-e958a58887c2
-- title:
--   Theta
-- statement:
--   Definitions and structural lemmas for Theta, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
namespace DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
abbrev minkowskiSpace : Type _ := mixedEmbedding.euclidean.mixedSpace K
def sqrtTwo : ℝˣ := Units.mk0 (Real.sqrt 2) (Real.sqrt_ne_zero'.mpr (by norm_num))
def scaleMixed : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ ({w : InfinitePlace K // InfinitePlace.IsReal w} → ℝ)).prodCongr
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
      (M₁ := {w : InfinitePlace K // InfinitePlace.IsComplex w} → ℂ) sqrtTwo)
def eEmb (x : K) : minkowskiSpace K :=
  (mixedEmbedding.euclidean.toMixed K).symm (scaleMixed K (mixedEmbedding K x))
def toMinkowski : mixedSpace K ≃L[ℝ] minkowskiSpace K :=
  (scaleMixed K).trans (mixedEmbedding.euclidean.toMixed K).symm
abbrev eEmbℝ : mixedSpace K ≃L[ℝ] minkowskiSpace K := toMinkowski K
@[simp]
theorem eEmbℝ_mixedEmbedding (a : K) :
    eEmbℝ K (mixedEmbedding K a) = eEmb K a := rfl
def idealLattice (I : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule ℤ (minkowskiSpace K) :=
  Submodule.span ℤ (eEmb K '' (I : Submodule (𝓞 K) K))
def covolume (𝔞 : Ideal (𝓞 K)) : ℝ :=
  (Ideal.absNorm 𝔞 : ℝ) * Real.sqrt (|(NumberField.discr K : ℝ)|)
abbrev differentFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)
def dualIdeal (𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K :=
  ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) * differentFractionalIdeal K)⁻¹
def conjMixed (ξ : mixedSpace K) : mixedSpace K :=
  ⟨ξ.1, fun w => (starRingEnd ℂ) (ξ.2 w)⟩
@[simp]
theorem conjMixed_fst (ξ : mixedSpace K) : (conjMixed K ξ).1 = ξ.1 := rfl
@[simp]
theorem conjMixed_snd (ξ : mixedSpace K) (w : {w : InfinitePlace K // w.IsComplex}) :
    (conjMixed K ξ).2 w = (starRingEnd ℂ) (ξ.2 w) := rfl
def conjMixedₗ : mixedSpace K ≃L[ℝ] mixedSpace K :=
  (ContinuousLinearEquiv.refl ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)).prodCongr
    (ContinuousLinearEquiv.piCongrRight
      (fun _ : {w : InfinitePlace K // w.IsComplex} =>
        Complex.conjLIE.toContinuousLinearEquiv))
@[simp]
theorem conjMixedₗ_apply (ξ : mixedSpace K) : conjMixedₗ K ξ = conjMixed K ξ := rfl
@[simp]
theorem conjMixedₗ_conjMixedₗ (ξ : mixedSpace K) :
    conjMixedₗ K (conjMixedₗ K ξ) = ξ := by
  apply Prod.ext
  · rfl
  · funext w
    simp only [conjMixedₗ_apply, conjMixed_snd, conjMixed_fst]
    exact Complex.conj_conj _
def conjMink : minkowskiSpace K ≃L[ℝ] minkowskiSpace K :=
  ((eEmbℝ K).symm.trans (conjMixedₗ K)).trans (eEmbℝ K)
theorem conjMink_apply (y : minkowskiSpace K) :
    conjMink K y = eEmbℝ K (conjMixed K ((eEmbℝ K).symm y)) := rfl
@[simp]
theorem conjMink_conjMink (y : minkowskiSpace K) :
    conjMink K (conjMink K y) = y := by
  simp only [conjMink_apply, ContinuousLinearEquiv.symm_apply_apply, ← conjMixedₗ_apply,
    conjMixedₗ_conjMixedₗ, ContinuousLinearEquiv.apply_symm_apply]
@[simp]
theorem conjMink_symm_apply (y : minkowskiSpace K) :
    (conjMink K).symm y = conjMink K y := by
  apply (conjMink K).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, conjMink_conjMink]
def traceForm (ξ : mixedSpace K) (a : K) : ℝ :=
  (∑ w : {w : InfinitePlace K // w.IsReal}, ξ.1 w * (mixedEmbedding K a).1 w) +
  2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
      (ξ.2 w * (mixedEmbedding K a).2 w).re
def eEmbHom : K →+ minkowskiSpace K :=
  ((mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv.toLinearMap.toAddMonoidHom).comp <|
    (((scaleMixed K).toLinearEquiv.toLinearMap.toAddMonoidHom).comp
      (mixedEmbedding K).toAddMonoidHom)
@[simp] theorem eEmbHom_apply (x : K) : eEmbHom K x = eEmb K x := rfl
theorem eEmb_injective : Function.Injective (eEmb K) := by
  intro x y h
  apply mixedEmbedding_injective K
  have h2 := (mixedEmbedding.euclidean.toMixed K).symm.injective.eq_iff.mp
    (by simpa only [eEmb] using h)
  exact (scaleMixed K).injective h2
theorem idealLattice_eq_map (I : FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice K I =
      Submodule.map (eEmbHom K).toIntLinearMap ((I : Submodule (𝓞 K) K).restrictScalars ℤ) := by
  rw [idealLattice, ← Submodule.span_eq
    (Submodule.map (eEmbHom K).toIntLinearMap ((I : Submodule (𝓞 K) K).restrictScalars ℤ))]
  congr 1
theorem mem_idealLattice_iff (I : FractionalIdeal (𝓞 K)⁰ K) (v : minkowskiSpace K) :
    v ∈ idealLattice K I ↔ ∃ a ∈ (I : Submodule (𝓞 K) K), eEmb K a = v := by
  rw [idealLattice_eq_map]
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem, AddMonoidHom.coe_toIntLinearMap,
    eEmbHom_apply]
def traceFormLin (η : mixedSpace K) : mixedSpace K →ₗ[ℝ] ℝ where
  toFun χ := (∑ w : {w : InfinitePlace K // w.IsReal}, η.1 w * χ.1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, (η.2 w * χ.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Complex.add_re,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    have h1 : ∀ w : {w : InfinitePlace K // w.IsReal},
        η.1 w * (c • x).1 w = c * (η.1 w * x.1 w) := by
      intro w; show η.1 w * (c * x.1 w) = _; ring
    have h2 : ∀ w : {w : InfinitePlace K // w.IsComplex},
        (η.2 w * (c • x).2 w).re = c * (η.2 w * x.2 w).re := by
      intro w; show (η.2 w * (c • x.2 w)).re = _
      rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]
    simp only [RingHom.id_apply, smul_eq_mul, h1, h2, ← Finset.mul_sum]
    ring
@[simp] theorem traceFormLin_apply (η χ : mixedSpace K) :
    traceFormLin K η χ =
      (∑ w : {w : InfinitePlace K // w.IsReal}, η.1 w * χ.1 w) +
        2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, (η.2 w * χ.2 w).re := rfl
def idealLatticeEquiv (I : FractionalIdeal (𝓞 K)⁰ K) :
    (I : Submodule (𝓞 K) K) ≃ idealLattice K I :=
  Equiv.ofBijective
    (fun a => ⟨eEmb K (a : K), (mem_idealLattice_iff K I _).mpr ⟨a, a.2, rfl⟩⟩)
    (by
      constructor
      · intro a b h
        exact Subtype.ext (eEmb_injective K (Subtype.ext_iff.mp h))
      · rintro ⟨v, hv⟩
        obtain ⟨a, ha, rfl⟩ := (mem_idealLattice_iff K I v).mp hv
        exact ⟨⟨a, ha⟩, rfl⟩)
open scoped Real in
/-- The Minkowski Gaussian `g(x) = exp(-π ⟨x,x⟩)` on `K_ℝ = mixedSpace K`, where
`⟨x,x⟩ = ∑_w mult w · ‖x_w‖²` is the Minkowski quadratic form (a complex place
contributes `2|x_w|²` via `mult w = 2`). This is the `t = 1` Gaussian whose
lattice sum is the theta series of the standard treatment. Moved here from
`Statements.lean` (theta-layer responsibility). -/
def mixedGaussian (x : mixedEmbedding.mixedSpace K) : ℝ :=
  Real.exp (-Real.pi *
    ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2)
def mixedThetaKernel (I : FractionalIdeal (𝓞 K)⁰ K)
    (x : mixedEmbedding.mixedSpace K) : ℂ :=
  ∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
    (mixedGaussian K (x * mixedEmbedding K (a : K)) : ℂ)
def idealThetaKernel (𝔞 : Ideal (𝓞 K)) (x : mixedEmbedding.mixedSpace K) : ℂ :=
  ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
    (mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)
def gaussV (v : minkowskiSpace K) : ℂ := Complex.exp (-(Real.pi : ℂ) * ‖v‖ ^ 2)
theorem mul_inv_cancel_of_norm_ne_zero {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) : x * x⁻¹ = 1 := by
  classical
  have hcomp : ∀ w : InfinitePlace K, normAtPlace w x ≠ 0 := fun w hw =>
    hx (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, hw⟩)
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have hw : x.1 w ≠ 0 := by
      have := hcomp w.1
      rw [normAtPlace_apply_of_isReal w.2] at this
      simpa using this
    show x.1 w * (x.1 w)⁻¹ = 1
    field_simp
  · have hw : x.2 w ≠ 0 := by
      have := hcomp w.1
      rw [normAtPlace_apply_of_isComplex w.2] at this
      simpa using this
    show x.2 w * (x.2 w)⁻¹ = 1
    field_simp
def mulLeftMixed {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) :
    mixedEmbedding.mixedSpace K ≃L[ℝ] mixedEmbedding.mixedSpace K :=
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel_of_norm_ne_zero K hx
  have hxinv' : x⁻¹ * x = 1 := by rw [mul_comm]; exact hxinv
  (LinearEquiv.ofLinear (LinearMap.mulLeft ℝ x) (LinearMap.mulLeft ℝ x⁻¹)
    (LinearMap.ext fun y => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.id_coe, id_eq, ← mul_assoc, hxinv, one_mul])
    (LinearMap.ext fun y => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.id_coe, id_eq, ← mul_assoc, hxinv', one_mul])).toContinuousLinearEquiv
def A_x {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    minkowskiSpace K ≃L[ℝ] minkowskiSpace K :=
  (toMinkowski K).symm.trans ((mulLeftMixed K hx).trans (toMinkowski K))
@[simp]
theorem A_x_apply {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0)
    (v : minkowskiSpace K) :
    A_x K hx v = toMinkowski K (x * (toMinkowski K).symm v) := rfl
theorem gaussV_contDiff : ContDiff ℝ ∞ (gaussV K) := by
  have h1 : ContDiff ℝ ∞ (fun v : minkowskiSpace K => (‖v‖ ^ 2 : ℝ)) :=
    contDiff_norm_sq ℝ
  have h2 : ContDiff ℝ ∞
      (fun v : minkowskiSpace K => (-(Real.pi : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ))) :=
    contDiff_const.mul ((Complex.ofRealCLM.contDiff).comp h1)
  have h3 : ContDiff ℝ ∞
      (fun v : minkowskiSpace K => Complex.exp (-(Real.pi : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp h2
  have hfun : gaussV K =
      fun v : minkowskiSpace K => Complex.exp (-(Real.pi : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ)) := by
    funext v
    rw [gaussV]
    push_cast
    ring_nf
  rw [hfun]
  exact h3
theorem exp_neg_pi_sq_mul_poly_bddAbove (N : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      (1 + t) ^ N * Real.exp (-Real.pi * t ^ 2) ≤ C := by
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * Real.pi)), fun t ht => ?_⟩
  have hpi := Real.pi_pos
  have h4pi : (0 : ℝ) < 4 * Real.pi := by linarith
  have h1t : (0 : ℝ) ≤ 1 + t := by linarith
  have hexp_pos : (0 : ℝ) < Real.exp (-Real.pi * t ^ 2) := Real.exp_pos _
  have hb : (1 + t) ^ N ≤ Real.exp ((N : ℝ) * t) := by
    calc (1 + t) ^ N
        ≤ (Real.exp t) ^ N :=
          pow_le_pow_left₀ h1t (by linarith [Real.add_one_le_exp t]) N
      _ = Real.exp ((N : ℝ) * t) := (Real.exp_nat_mul t N).symm
  calc (1 + t) ^ N * Real.exp (-Real.pi * t ^ 2)
      ≤ Real.exp ((N : ℝ) * t) * Real.exp (-Real.pi * t ^ 2) :=
        mul_le_mul_of_nonneg_right hb hexp_pos.le
    _ = Real.exp ((N : ℝ) * t + -Real.pi * t ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * Real.pi)) := by
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ h4pi]
        nlinarith [sq_nonneg ((N : ℝ) - 2 * Real.pi * t)]
theorem norm_iteratedFDeriv_cexp (i : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  rw [← (Complex.contDiff_exp (𝕜 := ℂ) (n := (i : ℕ∞ω))).contDiffAt.restrictScalars_iteratedFDeriv
        (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hexp : iteratedDeriv i Complex.exp = Complex.exp := by
    rw [iteratedDeriv_eq_iterate]; exact Complex.iter_deriv_exp i
  rw [hexp, Complex.norm_exp]
theorem norm_iteratedFDeriv_clm_succ {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F →L[ℝ] G) (i : ℕ) (v : F) :
    ‖iteratedFDeriv ℝ (i + 1) (⇑A) v‖ = ‖iteratedFDeriv ℝ i (fun _ : F => A) v‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hfd : (fderiv ℝ (⇑A)) = fun _ : F => A := by
    ext x : 1; exact A.fderiv
  rw [hfd]
theorem norm_iteratedFDeriv_normSq_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (i : ℕ) (hi : 1 ≤ i) (v : F) :
    ‖iteratedFDeriv ℝ i (fun w : F => ‖w‖ ^ 2) v‖ ≤ (2 * (1 + ‖v‖)) ^ i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  set A : F →L[ℝ] F →L[ℝ] ℝ := 2 • innerSL ℝ with hAdef
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hbase : (1 : ℝ) ≤ 2 * (1 + ‖v‖) := by nlinarith
  have hfderiv : ‖iteratedFDeriv ℝ (k + 1) (fun w : F => ‖w‖ ^ 2) v‖
      = ‖iteratedFDeriv ℝ k (⇑A) v‖ := by
    rw [← norm_iteratedFDeriv_fderiv]
    have hh : (fderiv ℝ fun w : F => ‖w‖ ^ 2) = ⇑A := fderiv_norm_sq
    rw [hh]
  rw [hfderiv]
  have hAval : ∀ w : F, A w = 2 • (innerSL ℝ w) := by
    intro w
    have hfd := fderiv_norm_sq_apply (F := F) w
    rw [fderiv_norm_sq] at hfd
    rw [hAdef]; exact hfd
  have hnormAw : ∀ w : F, ‖A w‖ = 2 * ‖w‖ := by
    intro w
    rw [hAval w, RCLike.norm_nsmul (K := ℝ), innerSL_apply_norm, nsmul_eq_mul]; norm_num
  have hAnorm : ‖A‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun w => ?_)
    rw [hnormAw w]
  have hAv : ‖A v‖ = 2 * ‖v‖ := hnormAw v
  match k with
  | 0 =>
    rw [norm_iteratedFDeriv_zero, hAv, pow_one]; nlinarith
  | 1 =>
    rw [norm_iteratedFDeriv_clm_succ A 0 v, norm_iteratedFDeriv_zero]
    have hexp : (2 * (1 + ‖v‖)) ^ (1 + 1) = (2 * (1 + ‖v‖)) * (2 * (1 + ‖v‖)) := by ring
    rw [hexp]; nlinarith [hAnorm, hnv, sq_nonneg ‖v‖]
  | l + 2 =>
    rw [norm_iteratedFDeriv_clm_succ A (l + 1) v,
      iteratedFDeriv_const_of_ne (by omega) A, Pi.zero_apply, norm_zero]
    positivity
theorem gaussV_iteratedFDeriv_bound (n : ℕ) :
    ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ v : minkowskiSpace K,
      ‖iteratedFDeriv ℝ n (gaussV K) v‖
        ≤ C * (1 + ‖v‖) ^ d * Real.exp (-Real.pi * ‖v‖ ^ 2) := by
  have hpi := Real.pi_pos
  set p : minkowskiSpace K → ℝ := fun v => (-Real.pi) • (‖v‖ ^ 2 : ℝ) with hpdef
  set u : minkowskiSpace K → ℂ := fun v => Complex.ofRealLI (p v) with hudef
  have hp_cd : ContDiff ℝ ∞ p := (contDiff_norm_sq ℝ).const_smul _
  have hu_cd : ContDiff ℝ ∞ u :=
    Complex.ofRealLI.toContinuousLinearMap.contDiff.comp hp_cd
  have hgauss : gaussV K = Complex.exp ∘ u := by
    funext v
    simp only [gaussV, Function.comp_apply, hudef, hpdef, Complex.ofRealLI_apply]
    congr 1
    push_cast [smul_eq_mul]
    ring
  refine ⟨n, (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n, by positivity, fun v => ?_⟩
  set D : ℝ := 2 * Real.pi * (1 + ‖v‖) with hDdef
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u v‖ ≤ D ^ i := by
    intro i hi _
    have hcomp : ‖iteratedFDeriv ℝ i u v‖ = ‖iteratedFDeriv ℝ i p v‖ :=
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hp_cd.contDiffAt) (by exact_mod_cast le_top)
    have hpe : p = (-Real.pi) • (fun w : minkowskiSpace K => ‖w‖ ^ 2) := by
      funext w; simp [hpdef, smul_eq_mul]
    have hsmul : ‖iteratedFDeriv ℝ i p v‖
        = Real.pi * ‖iteratedFDeriv ℝ i (fun w : minkowskiSpace K => ‖w‖ ^ 2) v‖ := by
      rw [hpe, iteratedFDeriv_const_smul_apply (contDiff_norm_sq ℝ).contDiffAt,
        _root_.norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hpi.le]
    rw [hcomp, hsmul]
    have hns := norm_iteratedFDeriv_normSq_le (F := minkowskiSpace K) i hi v
    have h1 : Real.pi ≤ Real.pi ^ i := by
      calc Real.pi = Real.pi ^ 1 := (pow_one _).symm
        _ ≤ Real.pi ^ i := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hi
    have hexpand : D ^ i = Real.pi ^ i * (2 * (1 + ‖v‖)) ^ i := by
      rw [hDdef, show 2 * Real.pi * (1 + ‖v‖) = Real.pi * (2 * (1 + ‖v‖)) from by ring, mul_pow]
    calc Real.pi * ‖iteratedFDeriv ℝ i (fun w : minkowskiSpace K => ‖w‖ ^ 2) v‖
        ≤ Real.pi * (2 * (1 + ‖v‖)) ^ i :=
          mul_le_mul_of_nonneg_left hns hpi.le
      _ ≤ Real.pi ^ i * (2 * (1 + ‖v‖)) ^ i :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = D ^ i := hexpand.symm
  have hure : (u v).re = -Real.pi * ‖v‖ ^ 2 := by
    simp only [hudef, hpdef, Complex.ofRealLI_apply, Complex.ofReal_re, smul_eq_mul]
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Complex.exp (u v)‖
      ≤ Real.exp (-Real.pi * ‖v‖ ^ 2) := by
    intro i _
    rw [norm_iteratedFDeriv_cexp, hure]
  have hmain := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := u)
    Complex.contDiff_exp hu_cd (by exact_mod_cast le_top) v
    (C := Real.exp (-Real.pi * ‖v‖ ^ 2)) (D := D) hC hD
  rw [hgauss]
  calc ‖iteratedFDeriv ℝ n (Complex.exp ∘ u) v‖
      ≤ (Nat.factorial n : ℝ) * Real.exp (-Real.pi * ‖v‖ ^ 2) * D ^ n := hmain
    _ = (Nat.factorial n : ℝ) * (2 * Real.pi) ^ n * (1 + ‖v‖) ^ n
          * Real.exp (-Real.pi * ‖v‖ ^ 2) := by
        rw [hDdef, mul_pow]; ring
theorem gaussV_decay :
    ∀ (k n : ℕ), ∃ C : ℝ, ∀ v : minkowskiSpace K,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (gaussV K) v‖ ≤ C := by
  intro k n
  obtain ⟨d, C, hC0, hbound⟩ := gaussV_iteratedFDeriv_bound K n
  obtain ⟨C', hC'⟩ := exp_neg_pi_sq_mul_poly_bddAbove (k + d)
  refine ⟨C * C', fun v => ?_⟩
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hexp : (0 : ℝ) ≤ Real.exp (-Real.pi * ‖v‖ ^ 2) := (Real.exp_pos _).le
  have hpoly : ‖v‖ ^ k * (1 + ‖v‖) ^ d ≤ (1 + ‖v‖) ^ (k + d) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv (by linarith) k) (by positivity)
  calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (gaussV K) v‖
      ≤ ‖v‖ ^ k * (C * (1 + ‖v‖) ^ d * Real.exp (-Real.pi * ‖v‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hbound v) (by positivity)
    _ = C * (‖v‖ ^ k * (1 + ‖v‖) ^ d) * Real.exp (-Real.pi * ‖v‖ ^ 2) := by ring
    _ ≤ C * (1 + ‖v‖) ^ (k + d) * Real.exp (-Real.pi * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC0) hexp
    _ = C * ((1 + ‖v‖) ^ (k + d) * Real.exp (-Real.pi * ‖v‖ ^ 2)) := by ring
    _ ≤ C * C' := mul_le_mul_of_nonneg_left (hC' ‖v‖ hv) hC0
def gaussVSchwartz : SchwartzMap (minkowskiSpace K) ℂ where
  toFun := gaussV K
  smooth' := gaussV_contDiff K
  decay' := gaussV_decay K
def mixedGaussianSchwartz {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) : SchwartzMap (minkowskiSpace K) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (A_x K hx) (gaussVSchwartz K)
section LinearChangeOfVariables
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
end LinearChangeOfVariables
end
end DedekindZeta.Theta


