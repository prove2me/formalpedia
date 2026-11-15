-- Prove2me | Definitions.Def_RPLib_S3_EllW2Z2
-- name    : RPLib_S3_EllW2Z2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:44:07.419532+00:00
-- url     : https://prove2.me/theorems/b8795234-70c2-480b-872c-c682c2cd5267
-- title:
--   The Eichler-Selberg trace formula in weight two: the zero mode of the non-split hyperbolic rest, trivial bound
-- statement:
--   The zero mode of the non-split hyperbolic rest, trivial bound.
--
--   * `summable_unfold_T`: the representative sum in `unfold_T` is summable.
--   * `zA g = ‖wtN g‖ ∫_{-1/2}^{1/2} R_g(x, y)^(-s-1) dx` (`zA_nonneg`, `zA_le`, `summable_zA` for `y ≥ 1/2`).
--   * `VZ`, `wZ`, `zmF_eq`: the data of `zero_mode_ct` for the absolute zero mode.
--   * **`zA_eq`**: `Σ'_g zA g = Σ'_{(c,t)} WN c t ∫_u VS(c,t,u)`.
--   * **`tsum_zA_le`**: `Σ'_g zA g ≤ KZ (2π² (y²)^(-s)) Σ'_c |c|^(-(1+2s))`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2Z

/-!
# S3-ES-Wt2 (O6, file Z2): the zero mode of the non-split hyperbolic rest, trivial bound

* `summable_unfold_T`: the representative sum in `unfold_T` is summable.
* `zA g = ‖wtN g‖ ∫_{-1/2}^{1/2} R_g(x, y)^(-s-1) dx` (`zA_nonneg`, `zA_le`, `summable_zA` for `y ≥ 1/2`).
* `VZ`, `wZ`, `zmF_eq`: the data of `zero_mode_ct` for the absolute zero mode.
* **`zA_eq`**: `Σ'_g zA g = Σ'_{(c,t)} WN c t ∫_u VS(c,t,u)`.
* **`tsum_zA_le`**: `Σ'_g zA g ≤ KZ (2π² (y²)^(-s)) Σ'_c |c|^(-(1+2s))`.
-/

open MeasureTheory Set Filter Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- The representative sum of `unfold_T` is summable. -/
theorem summable_unfold_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : S3.Conj.Mat → ℝ → E) (hf : ∀ g x, f (tconj 1 g) (x + 1) = f g x)
    (h0 : ∀ g, g 1 0 = 0 → ∀ x, f g x = 0) (hint : ∀ g, Integrable (f g))
    (hsum : Summable fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f g x) :
    Summable fun r : {g // IsRep g} => ∫ x, f r.1 x := by
  set F : S3.Conj.Mat → E := fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f g x with hF
  have hsP : Summable (fun p : {g // IsRep g} × ℤ => F (repEquiv p).1) :=
    repEquiv.summable_iff.2 (hsum.subtype _)
  refine hsP.prod.congr fun r => HasSum.tsum_eq ?_
  have hk : ∀ k : ℤ, F (tconj k r.1) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f r.1 (x + ((-k : ℤ) : ℝ)) := by
    intro k
    show (∫ x in (-(1 / 2 : ℝ))..(1 / 2), f (tconj k r.1) x) = _
    congr 1; funext x
    have := tconj_equivariant f hf k r.1 (x + ((-k : ℤ) : ℝ))
    rw [← this]; congr 1; push_cast; ring
  have hH := (hint r.1).hasSum_intervalIntegral (-(1 / 2 : ℝ))
  have hfun : (fun n : ℤ => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f r.1 (x + (n : ℝ))) =
      fun n : ℤ => ∫ x in (-(1 / 2 : ℝ)) + n..(-(1 / 2 : ℝ)) + n + 1, f r.1 x := by
    funext n
    rw [intervalIntegral.integral_comp_add_right]
    ring_nf
  rw [← hfun] at hH
  have h2 := (Equiv.neg ℤ).hasSum_iff.2 hH
  convert h2 using 1
  funext k
  show F (tconj k r.1) = _
  rw [hk]
  rfl

/-! ## The absolute zero-mode summand -/

lemma Rc_nonneg' (g : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℝ) : 0 ≤ Rc g x y := by
  unfold Rc; positivity

lemma integral_Rc_nonneg (g : Matrix (Fin 2) (Fin 2) ℤ) (s y : ℝ) :
    0 ≤ ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Rc g x y ^ (-s - 1) :=
  intervalIntegral.integral_nonneg (by norm_num) fun x _ => Real.rpow_nonneg (Rc_nonneg' g x y) _

/-- `‖wtN g‖ ∫_{-1/2}^{1/2} R^(-s-1)`. -/
def zA (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s y : ℝ) (g : S3.Conj.Mat) : ℝ :=
  ‖wtN M n δ' g‖ * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Rc g x y ^ (-s - 1)

lemma zA_nonneg (n : ℤ) (δ' : ZMod M) (s y : ℝ) (g : S3.Conj.Mat) : 0 ≤ zA M n δ' s y g :=
  mul_nonneg (norm_nonneg _) (integral_Rc_nonneg g s y)

lemma zA_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 1 / 2 ≤ y)
    (g : S3.Conj.Mat) :
    zA M n δ' s y g ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) *
      {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s (max 1 y)) g := by
  by_cases hd : g.det = n
  · rw [Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from hd)]
    have hdet : 0 < g.det := hd ▸ hn
    have hpt : ∀ x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2),
        ‖Rc g x y ^ (-s - 1)‖ ≤ ENs s (max 1 y) g := by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      have hre : ((x : ℂ) + y * Complex.I).re = x := by simp
      have him : ((x : ℂ) + y * Complex.I).im = y := by simp
      have hz : HypPar.InK (max 1 y) ((x : ℂ) + y * Complex.I) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [hre, abs_le]; constructor <;> linarith [hx.1, hx.2]
        · rw [him]; exact hy
        · rw [him]; exact le_max_right 1 y
      have hK := Rc_ge_K hdet (le_max_left 1 y) hz
      rw [hre, him] at hK
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Rc_nonneg' g x y) _)]
      exact Real.rpow_le_rpow_of_nonpos (div_pos (N_pos hdet) (by positivity)) hK (by linarith)
    have hI : (∫ x in (-(1 / 2 : ℝ))..(1 / 2), Rc g x y ^ (-s - 1)) ≤ ENs s (max 1 y) g := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [Real.norm_of_nonneg (integral_Rc_nonneg g s y)] at h
      have e : |(1 / 2 : ℝ) - -(1 / 2)| = 1 := by norm_num
      rw [e, mul_one] at h
      exact h
    exact mul_le_mul (norm_wtN_le n δ' g) hI (integral_Rc_nonneg g s y) (by positivity)
  · rw [Set.indicator_of_notMem (show g ∉ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from hd),
      mul_zero]
    unfold zA; rw [wtN_det n δ' g hd, norm_zero, zero_mul]

lemma summable_zA {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 1 / 2 ≤ y) :
    Summable (zA M n δ' s y) :=
  Summable.of_nonneg_of_le (zA_nonneg n δ' s y) (zA_le hn δ' hs.le hy)
    ((summable_ENs hn hs (max 1 y)).mul_left _)

/-! ## The data of `zero_mode_ct` -/

/-- The zero-mode profile: `VS` for `c ≠ 0`, `0` for `c = 0`. -/
def VZ (n : ℤ) (s y : ℝ) (c t : ℤ) (u : ℝ) : ℂ :=
  if c = 0 then 0 else ((VS s c n u y t : ℝ) : ℂ)

/-- The weight `‖wtN‖` as a complex number. -/
def wZ (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) : ℂ :=
  ((‖wtN M n δ' g‖ : ℝ) : ℂ)

lemma VS_nonneg' (s c n u y t : ℝ) : 0 ≤ VS s c n u y t :=
  Real.rpow_nonneg (by unfold Rp RcN; positivity) _

lemma integrable_VZ {n : ℤ} (hn : 0 ≤ n) {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) (c t : ℤ) :
    Integrable (VZ n s y c t) := by
  by_cases hc : c = 0
  · have e : VZ n s y c t = fun _ => (0 : ℂ) := by funext u; unfold VZ; rw [if_pos hc]
    rw [e]; exact integrable_zero _ _ _
  · have e : VZ n s y c t = fun u => ((VS s c n u y t : ℝ) : ℂ) := by
      funext u; unfold VZ; rw [if_neg hc]
    rw [e]
    exact (integrable_VS_u hs (by exact_mod_cast hc) hy (by exact_mod_cast hn) (t : ℝ)).ofReal

lemma zmF_eq (n : ℤ) (δ' : ZMod M) (s y : ℝ) (g : S3.Conj.Mat) (x : ℝ) :
    zmF (wZ M n δ') (VZ n s y) g x = ((‖wtN M n δ' g‖ * Rc g x y ^ (-s - 1) : ℝ) : ℂ) := by
  by_cases h : g 1 0 ≠ 0 ∧ g.det = n
  · obtain ⟨hc, hd⟩ := h
    unfold zmF wZ VZ
    rw [if_neg hc, ← Complex.ofReal_mul]
    congr 2
    rw [Rc_eq_RcN g hc x y]
    unfold VS Rp trR
    rw [hd, Int.cast_add]
  · have hw : wtN M n δ' g = 0 := by
      by_cases hc : g 1 0 = 0
      · exact wtN_c0 n δ' g hc
      · exact wtN_det n δ' g fun hd => h ⟨hc, hd⟩
    unfold zmF wZ
    rw [hw, norm_zero, zero_mul, Complex.ofReal_zero, zero_mul]

lemma integral_zmF_eq (n : ℤ) (δ' : ZMod M) (s y : ℝ) (g : S3.Conj.Mat) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), zmF (wZ M n δ') (VZ n s y) g x) = ((zA M n δ' s y g : ℝ) : ℂ) := by
  simp_rw [zmF_eq]
  unfold zA
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]

/-! ## The zero-mode identity and the trivial bound -/

/-- **The absolute zero mode in `(c, t)` form.** -/
theorem zA_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ∑' g, zA M n δ' s y g =
      ∑' ct : ℤ × ℤ, WN M n δ' ct.1 ct.2 * ∫ u, VS s ct.1 n u y ct.2 := by
  have hy0 : 0 < y := by linarith
  have hw : ∀ g, wZ M n δ' (tconj 1 g) = wZ M n δ' g := fun g => by
    unfold wZ; rw [wtN_tconj]
  have hw0 : ∀ g, g 1 0 = 0 → wZ M n δ' g = 0 := fun g h => by
    unfold wZ; rw [wtN_c0 n δ' g h, norm_zero, Complex.ofReal_zero]
  have hwd : ∀ g, g.det ≠ n → wZ M n δ' g = 0 := fun g h => by
    unfold wZ; rw [wtN_det n δ' g h, norm_zero, Complex.ofReal_zero]
  have hV : ∀ c t, Integrable (VZ n s y c t) := integrable_VZ hn.le hs.le hy0
  have hsum : Summable fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), zmF (wZ M n δ') (VZ n s y) g x := by
    simp_rw [integral_zmF_eq]
    exact Complex.summable_ofReal.2 (summable_zA hn δ' hs hy)
  have hint : ∀ g, Integrable (zmF (wZ M n δ') (VZ n s y) g) := fun g =>
    ((hV _ _).comp_add_right _).const_mul (wZ M n δ' g)
  have h0 : ∀ g, g 1 0 = 0 → ∀ x, zmF (wZ M n δ') (VZ n s y) g x = 0 := by
    intro g hg x; unfold zmF; rw [hw0 g hg, zero_mul]
  have hsumR : Summable fun r : {g // IsRep g} =>
      wZ M n δ' r.1 * ∫ u, VZ n s y (r.1 1 0) (r.1 0 0 + r.1 1 1) u := by
    refine (summable_unfold_T _ (zmF_tconj _ _ hw hw0) h0 hint hsum).congr fun r => ?_
    unfold zmF; rw [integral_const_mul, integral_add_right_eq_self]
  have hZ := zero_mode_ct n (wZ M n δ') (VZ n s y) hw hw0 hwd hV hsum hsumR
  simp_rw [integral_zmF_eq] at hZ
  rw [← Complex.ofReal_tsum] at hZ
  apply Complex.ofReal_injective
  rw [hZ, Complex.ofReal_tsum]
  refine tsum_congr fun ct => ?_
  obtain ⟨c, t⟩ := ct
  dsimp only
  by_cases hc : c = 0
  · subst hc
    have e : VZ n s y 0 t = fun _ => (0 : ℂ) := by funext u; unfold VZ; rw [if_pos rfl]
    simp [e, WN, fib]
  · have e : VZ n s y c t = fun u => ((VS s c n u y t : ℝ) : ℂ) := by
      funext u; unfold VZ; rw [if_neg hc]
    simp only [e]
    rw [integral_complex_ofReal, Complex.ofReal_mul]
    congr 1
    unfold WN wZ
    rw [Complex.ofReal_sum]

/-- `(c²y²)^(-s) · 2π²/|c| = 2π² (y²)^(-s) |c|^(-(1+2s))`. -/
lemma rpow_c_identity {c : ℝ} (hc : c ≠ 0) (s y : ℝ) :
    (c ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |c|) = 2 * π ^ 2 * (y ^ 2) ^ (-s) * |c| ^ (-(1 + 2 * s)) := by
  have hca : 0 < |c| := abs_pos.2 hc
  have h1 : (c ^ 2 * y ^ 2) ^ (-s) = (c ^ 2) ^ (-s) * (y ^ 2) ^ (-s) :=
    Real.mul_rpow (sq_nonneg c) (sq_nonneg y)
  have h2 : (c ^ 2) ^ (-s) = |c| ^ (2 * (-s)) := by
    rw [Real.rpow_mul hca.le, Real.rpow_two, sq_abs]
  have h3 : |c| ^ (-(1 + 2 * s)) = |c| ^ (2 * (-s)) / |c| := by
    rw [← Real.rpow_sub_one hca.ne']; congr 1; ring
  rw [h1, h2, h3, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **Trivial bound for the absolute zero mode.** -/
theorem tsum_zA_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ∑' g, zA M n δ' s y g ≤
      KZ M n s y * (2 * π ^ 2 * (y ^ 2) ^ (-s)) * ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s)) := by
  have hy0 : 0 < y := by linarith
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  set G : ℤ × ℤ → ℝ := fun ct => WN M n δ' ct.1 ct.2 * ∫ u, VS s ct.1 n u y ct.2 with hG
  have hG0 : 0 ≤ G := fun ct =>
    mul_nonneg (WN_nonneg _ _ _ _) (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _)
  set K := KZ M n s y * (2 * π ^ 2 * (y ^ 2) ^ (-s)) with hK
  have hK0 : 0 ≤ K := mul_nonneg (KZ_nonneg n hs.le hy0) (by positivity)
  have hfib : ∀ c : ℤ, Summable (fun t => G (c, t)) ∧
      ∑' t, G (c, t) ≤ K * |(c : ℝ)| ^ (-(1 + 2 * s)) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have h0 : ∀ t, G (0, t) = 0 := fun t => by simp [hG, WN, fib]
      simp only [h0, tsum_zero]
      exact ⟨summable_zero, mul_nonneg hK0 (by positivity)⟩
    · obtain ⟨hsu, hle⟩ := tsum_WcF_IU_le hn δ' hc hs.le hy0
      have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      have hle' : ∀ t, G (c, t) ≤ ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t := fun t =>
        mul_le_mul_of_nonneg_right (WN_le n δ' c t)
          (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _)
      have hsG : Summable fun t => G (c, t) :=
        Summable.of_nonneg_of_le (fun t => hG0 (c, t)) hle' hsu
      refine ⟨hsG, (hsG.tsum_le_tsum hle' hsu).trans (hle.trans_eq ?_)⟩
      rw [rpow_c_identity hc' s y, hK]; ring
  have hsZ := Real.summable_abs_int_rpow (show 1 < 1 + 2 * s by linarith)
  have hsC : Summable fun c : ℤ => ∑' t, G (c, t) :=
    Summable.of_nonneg_of_le (fun c => tsum_nonneg fun t => hG0 (c, t)) (fun c => (hfib c).2)
      (hsZ.mul_left K)
  have hsG : Summable G := (summable_prod_of_nonneg hG0).2 ⟨fun c => (hfib c).1, hsC⟩
  rw [zA_eq hn δ' hs hy]
  calc ∑' ct : ℤ × ℤ, WN M n δ' ct.1 ct.2 * ∫ u, VS s ct.1 n u y ct.2 = ∑' ct, G ct := rfl
    _ = ∑' c, ∑' t, G (c, t) := hsG.tsum_prod
    _ ≤ ∑' c : ℤ, K * |(c : ℝ)| ^ (-(1 + 2 * s)) :=
        hsC.tsum_le_tsum (fun c => (hfib c).2) (hsZ.mul_left K)
    _ = K * ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s)) := tsum_mul_left

end RamanujanPetersson.EllW2


