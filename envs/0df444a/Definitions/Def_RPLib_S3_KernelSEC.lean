-- Prove2me | Definitions.Def_RPLib_S3_KernelSEC
-- name    : RPLib_S3_KernelSEC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:58:37.438456+00:00
-- url     : https://prove2.me/theorems/4d44f125-b7de-4b94-a0fc-2a72711db47f
-- title:
--   The Eichler-Selberg trace formula in weight two: `⟪ω_s(·, W), f⟫ → ⟪Ω(·, W), f⟫` as `s → 0+`
-- statement:
--   `⟪ω_s(·, W), f⟫ → ⟪Ω(·, W), f⟫` as `s → 0+`.
--
--   * `integrableOn_im_rpow_strip` (`t < 1`), `integrableOn_fd_im_rpow`: `Im^(1/2)` is integrable on `𝒟`.
--   * `norm_petersson_two`, `exists_bound_cusp`, `norm_mul_im_smul`.
--   * `Bk`, `norm_omegaS_smul_le` (`0 < s ≤ 1/2`), `norm_Omega_smul_le`: `‖G(ρz)‖ Im(ρz) ≤ Bk Im(z)^(1/2)` on `Im z ≥ 1/2`.
--   * `integrableOn_petersson_omegaSH`, `integrableOn_fd_comp`, `setIntegral_fdom_eq_tsum`.
--   * `tendsto_integral_fd` (dominated convergence on each translate of `𝒟`), **`tendsto_peterssonInner`**.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSEB
import Definitions.Def_RPLib_S3_KernelSC
import Definitions.Def_RPLib_S3_EllipticTermB

/-!
# S3-ES-Wt2, part KS_E (C): `⟪ω_s(·, W), f⟫ → ⟪Ω(·, W), f⟫` as `s → 0+`

* `integrableOn_im_rpow_strip` (`t < 1`), `integrableOn_fd_im_rpow`: `Im^(1/2)` is integrable on `𝒟`.
* `norm_petersson_two`, `exists_bound_cusp`, `norm_mul_im_smul`.
* `Bk`, `norm_omegaS_smul_le` (`0 < s ≤ 1/2`), `norm_Omega_smul_le`: `‖G(ρz)‖ Im(ρz) ≤ Bk Im(z)^(1/2)` on `Im z ≥ 1/2`.
* `integrableOn_petersson_omegaSH`, `integrableOn_fd_comp`, `setIntegral_fdom_eq_tsum`.
* `tendsto_integral_fd` (dominated convergence on each translate of `𝒟`), **`tendsto_peterssonInner`**.
-/

open Complex Filter Topology UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Manifold ComplexConjugate Modular Pointwise

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RP.FundDomain RP.Petersson RamanujanPetersson.Kernel RamanujanPetersson.KernelS
  RamanujanPetersson.GSA RamanujanPetersson.EllTerm

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl

/-! ### (1) `Im^t` is integrable on the strip (`t < 1`) -/

def stripH : Set ℍ := {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im}

def stripC : Set ℂ := {w : ℂ | |w.re| ≤ 1 / 2 ∧ 1 / 2 ≤ w.im}

lemma measurableSet_stripH : MeasurableSet stripH :=
  ((isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const).inter
    (isClosed_le continuous_const UpperHalfPlane.continuous_im)).measurableSet

lemma measurableSet_stripC : MeasurableSet stripC :=
  ((isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_im)).measurableSet

theorem integrableOn_im_rpow_strip {t : ℝ} (ht : t < 1) :
    IntegrableOn (fun z : ℍ => ((z.im ^ t : ℝ) : ℂ)) stripH := by
  rw [← integrable_indicator_iff measurableSet_stripH, RamanujanPetersson.Bergman.integrable_iff_integrableOn]
  have hT' : stripC = Complex.measurableEquivRealProd ⁻¹'
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Ici (1 / 2)) := by
    ext w
    simp [stripC, abs_le]
  have h2 : IntegrableOn (fun y : ℝ => ((y ^ (t - 2) : ℝ) : ℂ)) (Set.Ici (1 / 2 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : t - 2 < -1)
      (by norm_num : (0 : ℝ) < 1 / 2)).ofReal
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hP : IntegrableOn (fun p : ℝ × ℝ => ((p.2 ^ (t - 2) : ℝ) : ℂ))
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Ici (1 / 2)) := by
    have h := Integrable.mul_prod h1 h2
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
    rw [IntegrableOn]
    simpa only [one_mul] using h
  have hC : IntegrableOn (fun w : ℂ => ((w.im ^ (t - 2) : ℝ) : ℂ)) stripC := by
    have h := (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).2 hP
    rw [← hT'] at h
    refine h.congr_fun (fun w _ => ?_) measurableSet_stripC
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply]
  have hC' : IntegrableOn (stripC.indicator fun w : ℂ => ((w.im ^ (t - 2) : ℝ) : ℂ))
      {w : ℂ | 0 < w.im} := (hC.integrable_indicator measurableSet_stripC).integrableOn
  refine hC'.congr_fun (fun w hw => ?_) (measurableSet_lt measurable_const Complex.measurable_im)
  have hw' : 0 < w.im := hw
  show stripC.indicator (fun w : ℂ => ((w.im ^ (t - 2) : ℝ) : ℂ)) w =
    (w.im ^ 2)⁻¹ • stripH.indicator (fun z : ℍ => ((z.im ^ t : ℝ) : ℂ)) (ofComplex w)
  rw [ofComplex_apply_of_im_pos hw']
  by_cases h : w ∈ stripC
  · have h' : (⟨w, hw'⟩ : ℍ) ∈ stripH := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    show ((w.im ^ (t - 2) : ℝ) : ℂ) = (w.im ^ 2)⁻¹ • ((w.im ^ t : ℝ) : ℂ)
    rw [Real.rpow_sub hw', Real.rpow_two, ← inv_mul_eq_div, Complex.real_smul, Complex.ofReal_mul]
  · have h' : (⟨w, hw'⟩ : ℍ) ∉ stripH := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', smul_zero]

lemma integrableOn_fd_im_rpow : IntegrableOn (fun z : ℍ => z.im ^ (1 / 2 : ℝ)) 𝒟 := by
  have h := Integrable.norm ((integrableOn_im_rpow_strip (by norm_num : (1 / 2 : ℝ) < 1)).mono_set
    fd_subset_strip)
  refine IntegrableOn.congr_fun h (fun z _ => ?_) ModularGroup.isClosed_fd.measurableSet
  show ‖((z.im ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ = z.im ^ (1 / 2 : ℝ)
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _)]

/-! ### (2) Pointwise bounds -/

lemma norm_petersson_two (G g : ℍ → ℂ) (τ : ℍ) :
    ‖petersson ((2 : ℕ) : ℤ) G g τ‖ = (‖G τ‖ * τ.im) * (‖g τ‖ * τ.im) := by
  rw [petersson_nat, norm_mul, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg τ.im_pos.le]
  ring

lemma norm_petersson_le {G : ℍ → ℂ} {B Cf : ℝ} (g : ℍ → ℂ) (τ : ℍ) (hG : ‖G τ‖ * τ.im ≤ B)
    (hg : ‖g τ‖ * τ.im ≤ Cf) : ‖petersson ((2 : ℕ) : ℤ) G g τ‖ ≤ B * Cf := by
  rw [norm_petersson_two]
  exact mul_le_mul hG hg (mul_nonneg (norm_nonneg _) τ.im_pos.le)
    ((mul_nonneg (norm_nonneg _) τ.im_pos.le).trans hG)

lemma exists_bound_cusp {M : ℕ} [NeZero M] (f : RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ)) :
    ∃ C, 0 ≤ C ∧ ∀ τ : ℍ, ‖f τ‖ * τ.im ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨max C 0, le_max_right _ _, fun τ => ?_⟩
  have h := hC τ
  have e : ((((2 : ℕ) : ℤ) : ℝ) / 2) = 1 := by norm_num
  rw [e, Real.rpow_one, le_div_iff₀ τ.im_pos] at h
  exact h.trans (le_max_left _ _)

lemma norm_mul_im_smul (ρ : SL(2, ℤ)) (z : ℍ) (A : ℂ) :
    ‖A‖ * (ρ • z).im = ‖A * denom ρ z ^ (-((2 : ℕ) : ℤ))‖ * z.im := by
  have e : ‖denom ρ z ^ (-((2 : ℕ) : ℤ))‖ = (‖denom ρ z‖ ^ 2)⁻¹ := by
    rw [norm_zpow, zpow_neg, zpow_natCast]
  rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, norm_mul, e]
  ring

lemma sum_bound_aux {ι : Type*} (s : Finset ι) (A : ι → ℂ) (B : ι → ℝ) {y : ℝ} (hy : 0 < y)
    (h : ∀ x ∈ s, ‖A x‖ ≤ B x * y ^ (-(1 / 2) : ℝ)) :
    ‖∑ x ∈ s, A x‖ * y ≤ (∑ x ∈ s, B x) * y ^ (1 / 2 : ℝ) := by
  have e : y ^ (-(1 / 2) : ℝ) * y = y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hy.ne']; norm_num
  calc ‖∑ x ∈ s, A x‖ * y ≤ (∑ x ∈ s, B x * y ^ (-(1 / 2) : ℝ)) * y :=
        mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum h)) hy.le
    _ = (∑ x ∈ s, B x) * y ^ (1 / 2 : ℝ) := by rw [← Finset.sum_mul, mul_assoc, e]

variable {M : ℕ} [NeZero M]

/-- The constant of the kernel bound on `ρ • 𝒟`. -/
def Bk (M : ℕ) [NeZero M] (n : ℕ) (u : (ZMod M)ˣ) (ρ : SL(2, ℤ)) (W : ℂ) : ℝ :=
  ∑ x : HNFIdx n × ZMod M, ‖(denW (hX n u x) W ^ 2)⁻¹‖ *
    ‖(denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W) ^ 2)⁻¹‖ *
      CKG M (1 / 2) (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W)).im

theorem norm_omegaS_smul_le (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    {W : ℂ} (hW : 0 < W.im) (ρ : SL(2, ℤ)) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) {z : ℍ}
    (hz : 1 / 2 ≤ z.im) :
    ‖omegaS M 2 n (u : ZMod M) s ((ρ • z : ℍ) : ℂ) W‖ * (ρ • z).im ≤ Bk M n u ρ W * z.im ^ (1 / 2 : ℝ) := by
  rw [norm_mul_im_smul, omegaS_eq_sum hn hnM u hs (ρ • z).im_pos hW, Finset.sum_mul]
  unfold Bk
  refine sum_bound_aux _ _ _ z.im_pos (fun x _ => ?_)
  have hv' := im_natPt_pos (det_hX_pos hn hnM u x) hW
  rw [mul_assoc, KGs_slash M s ρ z hv', ← KG_eq_KGs, norm_mul, norm_mul]
  have hK := norm_KG_le hM hs hs1 (by norm_num : (0 : ℝ) < 1 / 2) hz (im_natPt_SL_pos ρ hv')
  calc _ ≤ ‖(denW (hX n u x) W ^ 2)⁻¹‖ *
        (‖(denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W) ^ 2)⁻¹‖ *
          (CKG M (1 / 2) (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W)).im *
            z.im ^ (-(1 / 2) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem norm_Omega_smul_le (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    {W : ℂ} (hW : 0 < W.im) (ρ : SL(2, ℤ)) {z : ℍ} (hz : 1 / 2 ≤ z.im) :
    ‖Omega M n u ((ρ • z : ℍ) : ℂ) W‖ * (ρ • z).im ≤ Bk M n u ρ W * z.im ^ (1 / 2 : ℝ) := by
  rw [norm_mul_im_smul, Omega_slash hM hn hnM u ρ z hW]
  unfold Bk
  refine sum_bound_aux _ _ _ z.im_pos (fun x _ => ?_)
  have hv' := im_natPt_pos (det_hX_pos hn hnM u x) hW
  rw [norm_mul, norm_mul]
  have hK := norm_K0_le (M := M) (by norm_num : (0 : ℝ) < 1 / 2) hz (im_natPt_SL_pos ρ hv')
  calc _ ≤ ‖(denW (hX n u x) W ^ 2)⁻¹‖ *
        (‖(denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W) ^ 2)⁻¹‖ *
          (CKG M (1 / 2) (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W)).im *
            z.im ^ (-(1 / 2) : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-! ### (3) Integrability and the decomposition of `fdom` -/

set_option maxHeartbeats 400000 in
theorem integrableOn_petersson_omegaSH (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (u : (ZMod M)ˣ) {s : ℝ} (hs : 0 < s) (f : RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ)) (w : ℍ) :
    IntegrableOn (petersson ((2 : ℕ) : ℤ) (omegaSH M 2 n (u : ZMod M) s (-conj (w : ℂ))) f)
      (fdom (Gamma1 M)) := by
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hpos : ∀ i, 0 < (alphaHNF n u i).det := fun i => by
    rw [(mem_DeltaSet.1 (alphaHNF_mem hnM u i)).1]; exact hn'
  have hint : Integrable (fun z => ∑ i, PhiAS 2 s (alphaHNF n u i) f w z) :=
    integrable_finsetSum _ fun i _ => (integral_termS le_rfl hσ f (hpos i) w).1
  have e : petersson ((2 : ℕ) : ℤ) (omegaSH M 2 n (u : ZMod M) s (-conj (w : ℂ))) f =
      fun z => ∑' γ : Gamma1 M, (fun z' => ∑ i, PhiAS 2 s (alphaHNF n u i) f w z') ((γ : SL(2, ℤ)) • z) := by
    funext z
    exact petersson_omegaS_eq_tsum hn' hσ (alphaHNF n u) (alphaHNF_mem hnM u)
      (repMap_HNF_bijective hn hnM u) f w z
  rw [e]
  exact integrableOn_fdom_tsum (Φ := fun z' => ∑ i, PhiAS 2 s (alphaHNF n u i) f w z') hM hint

lemma integrableOn_fd_comp {F : ℍ → ℂ} (hI : IntegrableOn F (fdom (Gamma1 M)))
    (c : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) : IntegrableOn (fun z => F (c.out⁻¹ • z)) 𝒟 := by
  have h1 : IntegrableOn F (c.out⁻¹ • 𝒟) :=
    hI.mono_set (Set.subset_iUnion (fun c : SL(2, ℤ) ⧸ pmSL (Gamma1 M) => c.out⁻¹ • 𝒟) c)
  rw [← toPGLR_smul_set, ← Set.image_smul, (measurePreserving_smul (toPGLR c.out⁻¹)
    volume).integrableOn_image (measurableEmbedding_const_smul _)] at h1
  refine h1.congr_fun (fun z _ => ?_) ModularGroup.isClosed_fd.measurableSet
  show F (toPGLR c.out⁻¹ • z) = F (c.out⁻¹ • z)
  rw [toPGLR_smul]

theorem setIntegral_fdom_eq_tsum {F : ℍ → ℂ} (hI : IntegrableOn F (fdom (Gamma1 M))) :
    ∫ z in fdom (Gamma1 M), F z = ∑' c : SL(2, ℤ) ⧸ pmSL (Gamma1 M), ∫ z in 𝒟, F (c.out⁻¹ • z) :=
  setIntegral_iUnion_inv_smul_fd (Gamma1 M) (fun c => c.out) (fun c => QuotientGroup.out_eq' c) hI

/-! ### (4) Dominated convergence -/

theorem tendsto_integral_fd (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    (f : RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ)) (w : ℍ) (c : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) :
    Tendsto (fun s => ∫ z in 𝒟,
        petersson ((2 : ℕ) : ℤ) (omegaSH M 2 n (u : ZMod M) s (-conj (w : ℂ))) f (c.out⁻¹ • z))
      (𝓝[>] 0) (𝓝 (∫ z in 𝒟, petersson ((2 : ℕ) : ℤ) (OmegaH M n u (-conj (w : ℂ))) f (c.out⁻¹ • z))) := by
  have hW : 0 < (-conj (w : ℂ)).im := by simpa using w.im_pos
  obtain ⟨Cf, -, hCf⟩ := exists_bound_cusp f
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => Bk M n u c.out⁻¹ (-conj (w : ℂ)) * Cf * z.im ^ (1 / 2 : ℝ)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact Integrable.aestronglyMeasurable
      (integrableOn_fd_comp (integrableOn_petersson_omegaSH hM hn hnM u hs f w) c)
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    refine ae_restrict_of_forall_mem ModularGroup.isClosed_fd.measurableSet (fun z hz => ?_)
    have hz2 : 1 / 2 ≤ z.im := (fd_subset_strip hz).2
    have hG := norm_omegaS_smul_le hM hn hnM u hW c.out⁻¹ hs.1 hs.2 hz2
    have h := norm_petersson_le (G := omegaSH M 2 n (u : ZMod M) s (-conj (w : ℂ))) f
      (c.out⁻¹ • z) hG (hCf _)
    calc _ ≤ Bk M n u c.out⁻¹ (-conj (w : ℂ)) * z.im ^ (1 / 2 : ℝ) * Cf := h
      _ = _ := by ring
  · exact Integrable.const_mul integrableOn_fd_im_rpow _
  · refine ae_of_all _ (fun z => ?_)
    have h := tendsto_omegaS hM hn hnM u (c.out⁻¹ • z).im_pos hW
    have h2 : Tendsto (fun s => conj (omegaS M 2 n (u : ZMod M) s ((c.out⁻¹ • z : ℍ) : ℂ) (-conj (w : ℂ))))
        (𝓝[>] 0) (𝓝 (conj (Omega M n u ((c.out⁻¹ • z : ℍ) : ℂ) (-conj (w : ℂ))))) :=
      (Complex.continuous_conj.tendsto _).comp h
    simp only [petersson_nat, omegaSH, OmegaH, mul_assoc]
    exact h2.mul_const _

/-- **`⟪ω_s(·, -conj w), f⟫ → ⟪Ω(·, -conj w), f⟫` as `s → 0+`** (`M ≥ 3`, `(n, M) = 1`). -/
theorem tendsto_peterssonInner (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    (f : RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ)) (w : ℍ) :
    Tendsto (fun s => peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ)
        (omegaSH M 2 n (u : ZMod M) s (-conj (w : ℂ))) f) (𝓝[>] 0)
      (𝓝 (peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ) (OmegaH M n u (-conj (w : ℂ))) f)) := by
  have hW : 0 < (-conj (w : ℂ)).im := by simpa using w.im_pos
  have : (pmSL (Gamma1 M)).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSL _)
  have : Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M)) := Fintype.ofFinite _
  have h0 : IntegrableOn (petersson ((2 : ℕ) : ℤ) (OmegaH M n u (-conj (w : ℂ))) f)
      (fdom (Gamma1 M)) := by
    have h := integrableOn_petersson (Γ := Gamma1 M) (OmegaCF hM hn hnM u _ hW) f
    rwa [coe_OmegaCF] at h
  have hR : peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ) (OmegaH M n u (-conj (w : ℂ))) f =
      ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        ∫ z in 𝒟, petersson ((2 : ℕ) : ℤ) (OmegaH M n u (-conj (w : ℂ))) f (c.out⁻¹ • z) := by
    rw [peterssonInner, setIntegral_fdom_eq_tsum h0, tsum_fintype]
  have e : (fun s => peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ)
        (omegaSH M 2 n (u : ZMod M) s (-conj (w : ℂ))) f) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s => ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M), ∫ z in 𝒟,
        petersson ((2 : ℕ) : ℤ) (omegaSH M 2 n (u : ZMod M) s (-conj (w : ℂ))) f (c.out⁻¹ • z)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [peterssonInner, setIntegral_fdom_eq_tsum (integrableOn_petersson_omegaSH hM hn hnM u hs f w),
      tsum_fintype]
  rw [hR]
  exact Tendsto.congr' e.symm (tendsto_finsetSum _ (fun c _ => tendsto_integral_fd hM hn hnM u f w c))

end RamanujanPetersson.KernelSD


