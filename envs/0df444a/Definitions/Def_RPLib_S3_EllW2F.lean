-- Prove2me | Definitions.Def_RPLib_S3_EllW2F
-- name    : RPLib_S3_EllW2F
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:15:58.877757+00:00
-- url     : https://prove2.me/theorems/70f4dcd4-ddbf-4088-b03e-c2f69482fff5
-- title:
--   The Eichler-Selberg trace formula in weight two: the limit `Y → ∞` and the trace-down at `s > 0`
-- statement:
--   The limit `Y → ∞` and the trace-down at `s > 0`.
--
--   * `tendsto_trunc_integral`: `∫_{𝒟 ∩ {Im ≤ Y}} F → ∫_𝒟 F` as `Y → ∞` for `F` integrable on `𝒟`.
--   * `tendsto_trunc_restPart0`: `Σ_c ∫_{𝒟 ∩ {Im ≤ Y}} restPart0 (c.out⁻¹ τ) → ∫_{Γ₁(M)\ℍ} restPart0`.
--   * `ratQ_diag_eq`, `ratQ_diag_conj`, `phiGS_conj`: conjugation invariance of the regularised integrand.
--   * `KtilS`, `KtilS_eq_sum` (`s > 0`): `KtilS_s τ = Σ_c restPartS_s (c.out⁻¹ τ)`.
--   * `integrableOn_trunc_restPartS`, `integral_trunc_KtilS`, **`tendsto_trunc_KtilS`**:
--     `∫_{𝒟 ∩ {Im ≤ Y}} KtilS_s → Σ_c ∫_{𝒟 ∩ {Im ≤ Y}} restPart0 (c.out⁻¹ τ)` as `s → 0+`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2E
import Definitions.Def_RPLib_S3_HypParC

/-!
# S3-ES-Wt2 (O6, part F): the limit `Y → ∞` and the trace-down at `s > 0`

* `tendsto_trunc_integral`: `∫_{𝒟 ∩ {Im ≤ Y}} F → ∫_𝒟 F` as `Y → ∞` for `F` integrable on `𝒟`.
* `tendsto_trunc_restPart0`: `Σ_c ∫_{𝒟 ∩ {Im ≤ Y}} restPart0 (c.out⁻¹ τ) → ∫_{Γ₁(M)\ℍ} restPart0`.
* `ratQ_diag_eq`, `ratQ_diag_conj`, `phiGS_conj`: conjugation invariance of the regularised integrand.
* `KtilS`, `KtilS_eq_sum` (`s > 0`): `KtilS_s τ = Σ_c restPartS_s (c.out⁻¹ τ)`.
* `integrableOn_trunc_restPartS`, `integral_trunc_KtilS`, **`tendsto_trunc_KtilS`**:
  `∫_{𝒟 ∩ {Im ≤ Y}} KtilS_s → Σ_c ∫_{𝒟 ∩ {Im ≤ Y}} restPart0 (c.out⁻¹ τ)` as `s → 0+`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups Topology Modular Pointwise
  RamanujanPetersson.S3.Conj

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm RamanujanPetersson.KernelSD

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl

variable {M : ℕ}

/-! ## Part 1: `Y → ∞` -/

lemma measurableSet_trunc (Y : ℝ) : MeasurableSet (𝒟 ∩ {z : ℍ | z.im ≤ Y}) :=
  (ModularGroup.isClosed_fd.inter (isClosed_le UpperHalfPlane.continuous_im continuous_const)).measurableSet

lemma iUnion_trunc : (⋃ Y : ℝ, 𝒟 ∩ {z : ℍ | z.im ≤ Y}) = 𝒟 := by
  ext z
  simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨z.im, h, le_rfl⟩⟩

theorem tendsto_trunc_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℍ → E}
    (hI : IntegrableOn F 𝒟) :
    Tendsto (fun Y : ℝ => ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, F τ) atTop (𝓝 (∫ τ in 𝒟, F τ)) := by
  have hmono : Monotone fun Y : ℝ => 𝒟 ∩ {z : ℍ | z.im ≤ Y} :=
    fun Y Y' hY z hz => ⟨hz.1, (show z.im ≤ Y from hz.2).trans hY⟩
  have h := tendsto_setIntegral_of_monotone (μ := volume) (f := F) measurableSet_trunc hmono
    (by rw [iUnion_trunc]; exact hI)
  rwa [iUnion_trunc] at h

theorem tendsto_trunc_restPart0 [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) [Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M))] :
    Tendsto (fun Y : ℝ => ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, restPart0 M n δ (c.out⁻¹ • τ)) atTop
      (𝓝 (∫ z in fdom (Gamma1 M), restPart0 M n δ z)) := by
  rw [setIntegral_fdom_eq_tsum (integrableOn_restPart0 hM hn hnM δ), tsum_fintype]
  exact tendsto_finsetSum _ fun c _ =>
    tendsto_trunc_integral (integrableOn_fd_comp' (integrableOn_restPart0 hM hn hnM δ) c)

/-! ## Part 2: conjugation invariance of `phiGS` -/

lemma ratQ_diag_eq (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) :
    KernelS.ratQ g z (-conj (z : ℂ)) = (g.det : ℝ) * ‖phiG 1 g z‖ ^ 2 := by
  have hv : (-conj (z : ℂ)).im = z.im := by simp
  have hy : (z : ℂ).im = z.im := rfl
  simp only [KernelS.ratQ, EllTerm.phiG, pow_one, norm_mul, Complex.norm_conj, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos, hv, hy]
  ring

lemma ratQ_diag_conj (h : SL(2, ℤ)) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) :
    KernelS.ratQ (S3.Conj.conj h g) ((h • z : ℍ) : ℂ) (-conj ((h • z : ℍ) : ℂ)) =
      KernelS.ratQ g z (-conj (z : ℂ)) := by
  rw [ratQ_diag_eq, ratQ_diag_eq, phiG_conj, S3.Conj.det_conj]

lemma phiGS_conj (k : ℕ) (s : ℝ) (h : SL(2, ℤ)) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) :
    phiGS k s (S3.Conj.conj h g) (h • z) = phiGS k s g z := by
  rw [phiGS, phiGS, phiG_conj, ratQ_diag_conj]

/-! ## Part 3: the trace-down at `s > 0` -/

open Classical in
/-- The traced-down regularised rest kernel on `𝒟`. -/
def KtilS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' g : S3.Conj.Mat, if g.det = n ∧ HypPar.IsRest g then
    ((S3.levelCount M δ' g : ℂ) / 2) * phiGS 2 s g z else 0

open Classical in
lemma restPartS_smul_aux {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (h : SL(2, ℤ)) (z : ℍ) :
    Summable (fun g : S3.Conj.Mat =>
        if S3.Conj.conj h g ∈ DeltaSet M n δ' ∧ HypPar.IsRest g then phiGS 2 s g z else 0) ∧
      restPartS 2 M n δ' s (h • z) = ∑' g : S3.Conj.Mat,
        if S3.Conj.conj h g ∈ DeltaSet M n δ' ∧ HypPar.IsRest g then phiGS 2 s g z else 0 := by
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
  set F : S3.Conj.Mat → ℂ := (DeltaSet M n δ').indicator
    (fun x => if HypPar.IsRest x then phiGS 2 s x (h • z) else 0) with hF
  have hsF : Summable F := by
    rw [hF, ← summable_subtype_iff_indicator]
    exact summable_iteS 2 hσ hn δ' (h • z) HypPar.IsRest
  have hpt : ∀ g, F (HypPar.conjEquiv h g) =
      if S3.Conj.conj h g ∈ DeltaSet M n δ' ∧ HypPar.IsRest g then phiGS 2 s g z else 0 := by
    intro g
    show (DeltaSet M n δ').indicator _ (S3.Conj.conj h g) = _
    by_cases hm : S3.Conj.conj h g ∈ DeltaSet M n δ'
    · rw [Set.indicator_of_mem hm]
      by_cases hr : HypPar.IsRest g
      · rw [if_pos ((HypPar.isRest_conj h g).2 hr), if_pos ⟨hm, hr⟩, phiGS_conj]
      · rw [if_neg (fun h' => hr ((HypPar.isRest_conj h g).1 h')), if_neg (fun h' => hr h'.2)]
    · rw [Set.indicator_of_notMem hm, if_neg (fun h' => hm h'.1)]
  refine ⟨?_, ?_⟩
  · rw [← funext hpt]
    exact (HypPar.conjEquiv h).summable_iff.2 hsF
  · rw [← funext hpt, (HypPar.conjEquiv h).tsum_eq F, hF, ← tsum_subtype]
    rfl

open Classical in
lemma KtilS_eq_sum [NeZero M] (hM : 3 ≤ M) {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    [Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M))] (z : ℍ) :
    KtilS M n δ' s z = ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M), restPartS 2 M n δ' s (c.out⁻¹ • z) := by
  rw [Finset.sum_congr rfl fun c _ => (restPartS_smul_aux hs hn δ' (c.out)⁻¹ z).2]
  rw [← Summable.tsum_finsetSum (fun c _ => (restPartS_smul_aux hs hn δ' _ z).1), KtilS]
  refine tsum_congr fun g => ?_
  simp_rw [HypPar.conj_mem_DeltaSet_iff]
  by_cases hg : g.det = n ∧ HypPar.IsRest g
  · rw [if_pos hg]
    have e : ∀ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        (if (g.det = n ∧ S3.Conj.Eig M δ' g (c.out • S3.Conj.e1 M)) ∧ HypPar.IsRest g then
          phiGS 2 s g z else 0) =
          (if S3.Conj.Eig M δ' g (c.out • S3.Conj.e1 M) then 1 else 0) * phiGS 2 s g z := by
      intro c
      by_cases he : S3.Conj.Eig M δ' g (c.out • S3.Conj.e1 M)
      · rw [if_pos ⟨⟨hg.1, he⟩, hg.2⟩, if_pos he, one_mul]
      · rw [if_neg (fun h' => he h'.1.2), if_neg he, zero_mul]
    rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.sum_mul, Finset.sum_boole, HypPar.levelCount_eq hM,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    push_cast
    ring
  · rw [if_neg hg]
    exact (Finset.sum_eq_zero fun c _ => if_neg fun h' => hg ⟨h'.1.1, h'.2⟩).symm

/-! ## Part 4: integrability on `𝒟 ∩ {Im ≤ Y}` and the limit `s → 0+` -/

theorem integrableOn_trunc_restPartS [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) (c : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) (Y : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    IntegrableOn (fun τ => restPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (c.out⁻¹ • τ))
      (𝒟 ∩ {z : ℍ | z.im ≤ Y}) := by
  set δ'' : ZMod M := ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) with hδ''
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hmT := measurableSet_trunc Y
  obtain ⟨B, hB⟩ := diag_bound_trunc hM hn hnM (unitOf M n * δ) c.out⁻¹ Y
  have hE := integrableOn_fd_comp' (integrableOn_ellDom hM 0 δ'' n) c
  have hEb := ae_fd_of_ae_fdom (norm_ellPartS_le_ae hM 0 δ'' hn) c
  have hsm : Measurable fun τ : ℍ => c.out⁻¹ • τ := by
    have h := measurable_const_smul (toPGLR c.out⁻¹) (α := ℍ)
    simpa only [toPGLR_smul] using h
  set C : ℝ := |B| + ‖scalVal 2 M n δ''‖ with hC
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _) (norm_nonneg _)
  have hI : IntegrableOn (fun τ : ℍ => C * (2 * τ.im ^ (1 / 2 : ℝ)) + ellDom 0 M n δ'' (c.out⁻¹ • τ)) 𝒟 :=
    ((integrableOn_fd_im_rpow.const_mul 2).const_mul C).add hE
  refine Integrable.mono' (hI.mono_set inter_subset_left)
    ((measurable_restPartS hn' δ'' hs0).comp hsm).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hEb, ae_restrict_mem hmT]
    with τ hτE hτm
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
  have hsplit := diagS_split (k := 2) hσ hn' δ'' (c.out⁻¹ • τ)
  have e : restPartS 2 M n δ'' s (c.out⁻¹ • τ) =
      conj (KernelS.omegaS M 2 n δ'' s ((c.out⁻¹ • τ : ℍ) : ℂ) (-conj ((c.out⁻¹ • τ : ℍ) : ℂ))) *
        (((c.out⁻¹ • τ : ℍ).im : ℂ) ^ 2) - scalPartS 2 M n δ'' s (c.out⁻¹ • τ) -
          ellPartS 2 M n δ'' s (c.out⁻¹ • τ) := by
    rw [hsplit]; ring
  have hD := hB s hs0 hs1 τ hτm.1 hτm.2
  have hS : ‖scalPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ ≤ ‖scalVal 2 M n δ''‖ := by
    rw [scalPartS_eq 2 M δ'' hn s, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num) s)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one (by norm_num) (by norm_num) hs0.le)
  have hEl : ‖ellPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ ≤ ellDom 0 M n δ'' (c.out⁻¹ • τ) := hτE s hs0.le
  have h1 := one_le_two_mul_sqrt_im hτm.1
  rw [e]
  calc _ ≤ ‖conj (KernelS.omegaS M 2 n δ'' s ((c.out⁻¹ • τ : ℍ) : ℂ) (-conj ((c.out⁻¹ • τ : ℍ) : ℂ))) *
        (((c.out⁻¹ • τ : ℍ).im : ℂ) ^ 2)‖ + ‖scalPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ +
          ‖ellPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ |B| + ‖scalVal 2 M n δ''‖ + ellDom 0 M n δ'' (c.out⁻¹ • τ) :=
        add_le_add (add_le_add (hD.trans (le_abs_self B)) hS) hEl
    _ ≤ C * (2 * τ.im ^ (1 / 2 : ℝ)) + ellDom 0 M n δ'' (c.out⁻¹ • τ) := by
        rw [← hC]
        exact add_le_add (le_mul_of_one_le_right hC0 h1) le_rfl

theorem integral_trunc_KtilS [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) [Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M))] (Y : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    IntegrableOn (KtilS M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s) (𝒟 ∩ {z : ℍ | z.im ≤ Y}) ∧
      ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, KtilS M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s τ =
        ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M), ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y},
          restPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (c.out⁻¹ • τ) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hK : KtilS M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s = fun τ =>
      ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        restPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (c.out⁻¹ • τ) :=
    funext fun τ => KtilS_eq_sum hM hs0 hn' _ τ
  have hpiece := fun c => integrableOn_trunc_restPartS hM hn hnM δ c Y hs0 hs1
  rw [hK]
  exact ⟨integrable_finsetSum _ fun c _ => hpiece c, integral_finsetSum _ fun c _ => hpiece c⟩

/-- **The truncated trace-down limit**: `∫_{𝒟 ∩ {Im ≤ Y}} KtilS_s → Σ_c ∫_{𝒟 ∩ {Im ≤ Y}} restPart0 (c.out⁻¹ τ)`. -/
theorem tendsto_trunc_KtilS [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) [Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M))] (Y : ℝ) :
    Tendsto (fun s => ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, KtilS M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s τ)
      (𝓝[>] 0) (𝓝 (∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, restPart0 M n δ (c.out⁻¹ • τ))) := by
  refine (tendsto_finsetSum _ fun c _ => tendsto_trunc_restPartS hM hn hnM δ c Y).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
  exact (integral_trunc_KtilS hM hn hnM δ Y hs.1 hs.2).2.symm

end RamanujanPetersson.EllW2


