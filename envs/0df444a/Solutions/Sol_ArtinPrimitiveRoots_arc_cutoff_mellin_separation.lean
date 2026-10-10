-- Prove2me | solution 1 for ArtinPrimitiveRoots.arc_cutoff_mellin_separation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T20:27:25.753298+00:00
-- url     : https://prove2.me/submissions/89d761f4-46a8-4570-a081-4ec8d5994cc2

import Mathlib
import Definitions.Def_ArtinMarkedSquare

section
/-!
# L102M: shared basic definitions and lemmas

`arcCutoff` facts, `ψ_λ = psiL`, `n^{iτ}` helpers, and the Cauchy weight `ω_a`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

lemma arcCutoff_eq_fun : arcCutoff = fun t => Real.smoothTransition (5 - t) *
    Real.smoothTransition (5 + t) := rfl

lemma arcCutoff_eq_zero {y : ℝ} (h : 5 ≤ |y|) : arcCutoff y = 0 := by
  unfold arcCutoff
  rcases le_abs'.mp h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + y ≤ 0), mul_zero]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 - y ≤ 0), zero_mul]

lemma arcCutoff_eq_one {y : ℝ} (h : |y| ≤ 4) : arcCutoff y = 1 := by
  unfold arcCutoff
  rw [abs_le] at h
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 5 - y),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 5 + y), one_mul]

lemma arcCutoff_ne_zero {y : ℝ} (h : arcCutoff y ≠ 0) : |y| < 5 := by
  by_contra h'
  exact h (arcCutoff_eq_zero (not_lt.mp h'))

/-- The complexified cutoff. -/
def arcC (y : ℝ) : ℂ := (arcCutoff y : ℂ)

/-- The phase `e(λ y) = exp(2π i λ y)`. -/
def eL (lam y : ℝ) : ℂ := Complex.exp (2 * π * I * lam * y)

lemma eL_eq (lam : ℝ) : eL lam = fun y : ℝ => Complex.exp ((2 * π * I * lam) * y) := by
  funext y; unfold eL; ring_nf

lemma hasDerivAt_cexp_mul_ofReal (c : ℂ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y)) (c * Complex.exp (c * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c y := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul c
  have := h1.cexp
  simpa [mul_comm] using this

/-- `ψ_λ(y) = ψ(y) e(λ y)`. -/
def psiL (lam y : ℝ) : ℂ := arcC y * eL lam y

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: one-variable smooth bounds for the Mellin separation

`arcCutoff` is smooth with compact support; `ψ_λ(y) = ψ(y) e(λ y)` has `n`-th derivatives
bounded by `M (1 + 2π|λ|)^n`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

lemma arcCutoff_contDiff : ContDiff ℝ ∞ arcCutoff := by
  rw [arcCutoff_eq_fun]
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

lemma arcC_contDiff : ContDiff ℝ ∞ arcC :=
  Complex.ofRealCLM.contDiff.comp arcCutoff_contDiff

lemma arcC_hasCompactSupport : HasCompactSupport arcC := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-5) 5) isCompact_Icc
  intro y hy
  have h : arcCutoff y ≠ 0 := by
    intro h0; apply hy; simp [arcC, h0]
  have := arcCutoff_ne_zero h
  rw [abs_lt] at this
  exact ⟨this.1.le, this.2.le⟩

lemma arcC_deriv_bound : ∃ M : ℝ, 1 ≤ M ∧ ∀ n : ℕ, n ≤ 4 → ∀ y : ℝ,
    ‖iteratedFDeriv ℝ n arcC y‖ ≤ M := by
  have hb : ∀ n : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ n arcC y‖ ≤ C := by
    intro n
    exact (arcC_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (arcC_hasCompactSupport.iteratedFDeriv n)
  choose C hC using hb
  refine ⟨1 + ∑ n ∈ Finset.range 5, |C n|, ?_, ?_⟩
  · have : 0 ≤ ∑ n ∈ Finset.range 5, |C n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · intro n hn y
    have h1 : C n ≤ |C n| := le_abs_self _
    have h2 : |C n| ≤ ∑ n ∈ Finset.range 5, |C n| :=
      Finset.single_le_sum (f := fun n => |C n|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    linarith [hC n y]

lemma eL_contDiff (lam : ℝ) : ContDiff ℝ ∞ (eL lam) := by
  rw [eL_eq]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

lemma iteratedDeriv_cexp_mul_ofReal (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (c * y)) =
      fun y : ℝ => c ^ n * Complex.exp (c * y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have := (hasDerivAt_cexp_mul_ofReal c y).const_mul (c ^ n)
    rw [this.deriv]; ring

lemma norm_iteratedFDeriv_eL (lam : ℝ) (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n (eL lam) y‖ = (2 * π * |lam|) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [eL_eq, iteratedDeriv_cexp_mul_ofReal]
  simp only [norm_mul, norm_pow]
  have h1 : ‖Complex.exp (2 * π * I * lam * y)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [h1, mul_one]
  congr 1
  simp [abs_of_pos Real.pi_pos]

lemma psiL_contDiff (lam : ℝ) : ContDiff ℝ ∞ (psiL lam) :=
  arcC_contDiff.mul (eL_contDiff lam)

lemma psiL_deriv_bound (M : ℝ) (hM : ∀ n : ℕ, n ≤ 4 → ∀ y : ℝ,
    ‖iteratedFDeriv ℝ n arcC y‖ ≤ M) (lam : ℝ) (n : ℕ) (hn : n ≤ 4) (y : ℝ) :
    ‖iteratedFDeriv ℝ n (psiL lam) y‖ ≤ M * (1 + 2 * π * |lam|) ^ n := by
  have h := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ∞) arcC_contDiff (eL_contDiff lam) y
    (n := n) (by exact_mod_cast le_top)
  have hpsi : (fun y => arcC y * eL lam y) = psiL lam := rfl
  rw [hpsi] at h
  refine h.trans ?_
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [norm_iteratedFDeriv_eL]
  have := hM i (hi'.trans hn) y
  rw [one_pow, one_mul]
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i arcC y‖ * (2 * π * |lam|) ^ (n - i)
      ≤ (n.choose i : ℝ) * M * (2 * π * |lam|) ^ (n - i) := by gcongr
    _ = M * ((2 * π * |lam|) ^ (n - i) * (n.choose i : ℝ)) := by ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the two-variable kernel `g(ζ, z) = ψ_λ(e^z X (e^{ζ/X} - 1)) ψ(z)`

Smoothness, support in a fixed box, and derivative bounds `‖D^n g‖ ≤ K (1 + 2π|λ|)^4`
(`n ≤ 4`), uniformly for `X ≥ 10 e^6`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

abbrev V2 := EuclideanSpace ℝ (Fin 2)

lemma abs_apply_le_norm (p : V2) (i : Fin 2) : |p i| ≤ ‖p‖ := by
  have h : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
  have hn : 0 ≤ ‖p‖ := norm_nonneg _
  rw [← abs_of_nonneg hn, ← sq_le_sq]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]

lemma norm_le_abs_add_abs (p : V2) : ‖p‖ ≤ |p 0| + |p 1| := by
  have h : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
  have hn : 0 ≤ ‖p‖ := norm_nonneg _
  have h2 : 0 ≤ |p 0| + |p 1| := by positivity
  rw [← abs_of_nonneg hn, ← abs_of_nonneg h2, ← sq_le_sq, h]
  nlinarith [sq_abs (p 0), sq_abs (p 1), abs_nonneg (p 0), abs_nonneg (p 1)]

/-- The coordinate projections. -/
def pr (i : Fin 2) : V2 →L[ℝ] ℝ := EuclideanSpace.proj i

lemma pr_apply (i : Fin 2) (p : V2) : pr i p = p i := rfl

lemma norm_pr_le (i : Fin 2) : ‖pr i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  rw [pr_apply, one_mul, Real.norm_eq_abs]
  exact abs_apply_le_norm p i

lemma norm_iteratedFDeriv_comp_pr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (hf : ContDiff ℝ ∞ f) (i : Fin 2) (n : ℕ) (p : V2) :
    ‖iteratedFDeriv ℝ n (f ∘ pr i) p‖ ≤ ‖iteratedFDeriv ℝ n f (p i)‖ := by
  rw [(pr i).iteratedFDeriv_comp_right hf p (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _j : Fin n, ‖pr i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun _ _ => norm_pr_le i)
  calc ‖iteratedFDeriv ℝ n f (pr i p)‖ * ∏ _j : Fin n, ‖pr i‖
      ≤ ‖iteratedFDeriv ℝ n f (pr i p)‖ * 1 := by gcongr
    _ = ‖iteratedFDeriv ℝ n f (p i)‖ := by rw [mul_one, pr_apply]

/-- `u_X(ζ) = X (e^{ζ/X} - 1)`. -/
def uX (X ζ : ℝ) : ℝ := X * (Real.exp (ζ / X) - 1)

lemma uX_eq (X : ℝ) : uX X = fun ζ => -X + X * Real.exp ((1 / X) * ζ) := by
  funext ζ; unfold uX; ring_nf

lemma uX_contDiff (X : ℝ) : ContDiff ℝ ∞ (uX X) := by
  rw [uX_eq]; fun_prop

lemma iteratedDeriv_uX (X : ℝ) (k : ℕ) (hk : 0 < k) (ζ : ℝ) :
    iteratedDeriv k (uX X) ζ = X * (1 / X) ^ k * Real.exp ((1 / X) * ζ) := by
  rw [uX_eq, iteratedDeriv_const_add hk, iteratedDeriv_const_mul_field,
    iteratedDeriv_exp_const_mul]
  ring

/-- `|u_X(ζ)| ≤ 2|ζ|` for `|ζ| ≤ X`. -/
lemma abs_uX_le (X ζ : ℝ) (hX : 0 < X) (hζ : |ζ| ≤ X) : |uX X ζ| ≤ 2 * |ζ| := by
  unfold uX
  have h1 : |ζ / X| ≤ 1 := by rw [abs_div, abs_of_pos hX, div_le_one hX]; exact hζ
  have h2 := Real.abs_exp_sub_one_le h1
  rw [abs_mul, abs_of_pos hX]
  calc X * |Real.exp (ζ / X) - 1| ≤ X * (2 * |ζ / X|) := by gcongr
    _ = 2 * |ζ| := by rw [abs_div, abs_of_pos hX]; field_simp

lemma norm_iteratedFDeriv_uX_le (X ζ R : ℝ) (hR : 2 ≤ R) (hX : R ≤ X) (hζ : |ζ| ≤ R)
    (k : ℕ) : ‖iteratedFDeriv ℝ k (uX X) ζ‖ ≤ 2 * R := by
  have hX0 : 0 < X := by linarith
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [iteratedDeriv_zero]
    calc |uX X ζ| ≤ 2 * |ζ| := abs_uX_le X ζ hX0 (hζ.trans hX)
      _ ≤ 2 * R := by linarith
  · rw [iteratedDeriv_uX X k hk ζ]
    have he : Real.exp ((1 / X) * ζ) ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      rw [one_div_mul_eq_div, div_le_one hX0]
      exact (le_abs_self ζ).trans (hζ.trans hX)
    have hp : X * (1 / X) ^ k ≤ 1 := by
      have : X * (1 / X) ^ k = (1 / X) ^ (k - 1) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ]; field_simp; simp
      rw [this]
      apply pow_le_one₀ (by positivity)
      rw [div_le_one hX0]; linarith
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (by positivity)]
    calc X * (1 / X) ^ k * Real.exp ((1 / X) * ζ) ≤ 1 * Real.exp 1 := by
          gcongr
      _ ≤ 2 * R := by
          have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
          linarith

/-- `Φ_X(p) = e^{p_1} u_X(p_0)`. -/
def PhiX (X : ℝ) (p : V2) : ℝ := Real.exp (p 1) * uX X (p 0)

lemma PhiX_eq (X : ℝ) : PhiX X = fun p => (Real.exp ∘ pr 1) p * (uX X ∘ pr 0) p := rfl

lemma PhiX_contDiff (X : ℝ) : ContDiff ℝ ∞ (PhiX X) := by
  rw [PhiX_eq]
  exact (Real.contDiff_exp.comp (pr 1).contDiff).mul ((uX_contDiff X).comp (pr 0).contDiff)

lemma norm_iteratedFDeriv_PhiX_le (X R : ℝ) (hR : 2 ≤ R) (hX : R ≤ X) (p : V2)
    (hp0 : |p 0| ≤ R) (hp1 : |p 1| ≤ 5) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (PhiX X) p‖ ≤ 2 ^ n * (Real.exp 5 * (2 * R)) := by
  rw [PhiX_eq]
  refine (norm_iteratedFDeriv_mul_le (N := ∞) (Real.contDiff_exp.comp (pr 1).contDiff)
    ((uX_contDiff X).comp (pr 0).contDiff) p (n := n) (by exact_mod_cast le_top)).trans ?_
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [← hsum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 : ‖iteratedFDeriv ℝ i (Real.exp ∘ pr 1) p‖ ≤ Real.exp 5 := by
    refine (norm_iteratedFDeriv_comp_pr Real.exp Real.contDiff_exp 1 i p).trans ?_
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hp1)
  have h2 : ‖iteratedFDeriv ℝ (n - i) (uX X ∘ pr 0) p‖ ≤ 2 * R :=
    (norm_iteratedFDeriv_comp_pr (uX X) (uX_contDiff X) 0 (n - i) p).trans
      (norm_iteratedFDeriv_uX_le X (p 0) R hR hX hp0 (n - i))
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (Real.exp ∘ pr 1) p‖ *
        ‖iteratedFDeriv ℝ (n - i) (uX X ∘ pr 0) p‖
      ≤ (n.choose i : ℝ) * Real.exp 5 * (2 * R) := by gcongr
    _ = (n.choose i : ℝ) * (Real.exp 5 * (2 * R)) := by ring

/-- The separation kernel `g(p) = ψ_λ(Φ_X(p)) ψ(p_1)`. -/
def gSep (X lam : ℝ) (p : V2) : ℂ := psiL lam (PhiX X p) * arcC (p 1)

lemma gSep_eq (X lam : ℝ) : gSep X lam = fun p => (psiL lam ∘ PhiX X) p * (arcC ∘ pr 1) p := rfl

lemma gSep_contDiff (X lam : ℝ) : ContDiff ℝ ∞ (gSep X lam) := by
  rw [gSep_eq]
  exact ((psiL_contDiff lam).comp (PhiX_contDiff X)).mul (arcC_contDiff.comp (pr 1).contDiff)

/-- The support radius. -/
def R0 : ℝ := 5 * Real.exp 6

lemma two_le_R0 : 2 ≤ R0 := by
  unfold R0
  have : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  linarith

/-- Support: `g(p) ≠ 0` forces `|p_0| ≤ R0`, `|p_1| ≤ 5` once `X ≥ 10 e^6`. -/
lemma gSep_support (X lam : ℝ) (hX : 10 * Real.exp 6 ≤ X) (p : V2) (hp : gSep X lam p ≠ 0) :
    |p 0| ≤ R0 ∧ |p 1| ≤ 5 := by
  unfold gSep psiL at hp
  have ha : arcCutoff (p 1) ≠ 0 := by
    intro h; apply hp; simp [arcC, h]
  have hb : arcCutoff (PhiX X p) ≠ 0 := by
    intro h; apply hp; simp [arcC, h]
  have h1 := arcCutoff_ne_zero ha
  have h2 := arcCutoff_ne_zero hb
  refine ⟨?_, h1.le⟩
  have he6 : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  have hX0 : 0 < X := by linarith
  -- |u_X(p 0)| < 5 e^5
  have hu : |uX X (p 0)| < 5 * Real.exp 5 := by
    unfold PhiX at h2
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h2
    have hlow : Real.exp (-5) ≤ Real.exp (p 1) :=
      Real.exp_le_exp.mpr (by have := (abs_lt.mp h1).1; linarith)
    have hpos : 0 < Real.exp (-5) := Real.exp_pos _
    have : Real.exp (-5) * |uX X (p 0)| < 5 := by
      calc Real.exp (-5) * |uX X (p 0)| ≤ Real.exp (p 1) * |uX X (p 0)| := by gcongr
        _ < 5 := h2
    have he : Real.exp (-5) * Real.exp 5 = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos 5]
  have he56 : Real.exp 5 ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
  unfold R0
  set ζ := p 0 with hζ
  rcases le_or_gt 0 ζ with hz | hz
  · -- ζ ≥ 0: u ≥ ζ
    have : ζ ≤ uX X ζ := by
      unfold uX
      have := Real.add_one_le_exp (ζ / X)
      have h' : X * (ζ / X) ≤ X * (Real.exp (ζ / X) - 1) := by
        apply mul_le_mul_of_nonneg_left _ hX0.le; linarith
      rwa [mul_div_cancel₀ _ hX0.ne'] at h'
    rw [abs_of_nonneg hz]
    have := (le_abs_self (uX X ζ))
    nlinarith
  · rcases le_or_gt (-X) ζ with hz' | hz'
    · -- -X ≤ ζ < 0: |u| ≥ -ζ / e
      have hs : ζ / X ≤ 0 := div_nonpos_of_nonpos_of_nonneg hz.le hX0.le
      have hs' : -1 ≤ ζ / X := by rw [le_div_iff₀ hX0]; linarith
      have key : -(ζ / X) * Real.exp (ζ / X) ≤ 1 - Real.exp (ζ / X) := by
        have := Real.add_one_le_exp (-(ζ / X))
        have h3 : Real.exp (ζ / X) * Real.exp (-(ζ / X)) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (ζ / X)]
      have hem : Real.exp (-1) ≤ Real.exp (ζ / X) := Real.exp_le_exp.mpr hs'
      have hu' : -ζ * Real.exp (-1) ≤ |uX X ζ| := by
        unfold uX
        have : X * (Real.exp (ζ / X) - 1) ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos hX0.le
          linarith [Real.exp_le_one_iff.mpr hs]
        rw [abs_of_nonpos this]
        have h4 : -ζ * Real.exp (ζ / X) ≤ X * (1 - Real.exp (ζ / X)) := by
          have := mul_le_mul_of_nonneg_left key hX0.le
          rw [show X * (-(ζ / X) * Real.exp (ζ / X)) = -ζ * Real.exp (ζ / X) by
            field_simp] at this
          exact this
        have h5 : -ζ * Real.exp (-1) ≤ -ζ * Real.exp (ζ / X) := by
          apply mul_le_mul_of_nonneg_left hem; linarith
        linarith
      rw [abs_of_neg hz]
      have he1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      have he6' : Real.exp 1 * Real.exp 5 = Real.exp 6 := by rw [← Real.exp_add]; norm_num
      have : -ζ * Real.exp (-1) < 5 * Real.exp 5 := lt_of_le_of_lt hu' hu
      have h7 : -ζ < 5 * Real.exp 5 * Real.exp 1 := by
        have := mul_lt_mul_of_pos_right this (Real.exp_pos 1)
        rw [mul_assoc, he1, mul_one] at this
        exact this
      nlinarith [Real.exp_pos 1, Real.exp_pos 5]
    · -- ζ < -X: |u| ≥ X/2, contradiction
      exfalso
      have hs : ζ / X < -1 := by rw [div_lt_iff₀ hX0]; linarith
      have hem : Real.exp (ζ / X) ≤ Real.exp (-1) := Real.exp_le_exp.mpr hs.le
      have he1 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.add_one_le_exp 1
        linarith
      have hu' : X / 2 ≤ |uX X ζ| := by
        unfold uX
        have : X * (Real.exp (ζ / X) - 1) ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos hX0.le; linarith
        rw [abs_of_nonpos this]
        nlinarith
      nlinarith

/-- Uniform derivative bounds for `g`. -/
lemma gSep_deriv_bound (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ n : ℕ, n ≤ 4 → ∀ y : ℝ,
    ‖iteratedFDeriv ℝ n arcC y‖ ≤ M) (X lam : ℝ) (hX : 10 * Real.exp 6 ≤ X)
    (n : ℕ) (hn : n ≤ 4) (p : V2) :
    ‖iteratedFDeriv ℝ n (gSep X lam) p‖ ≤
      2 ^ n * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * (1 + 2 * π * |lam|) ^ 4 := by
  by_cases hp : p ∈ tsupport (gSep X lam)
  · -- p is in the closed box
    have hbox : |p 0| ≤ R0 ∧ |p 1| ≤ 5 := by
      have hclosed : IsClosed {q : V2 | |q 0| ≤ R0 ∧ |q 1| ≤ 5} := by
        apply IsClosed.inter
        · exact isClosed_le (continuous_abs.comp (pr 0).continuous) continuous_const
        · exact isClosed_le (continuous_abs.comp (pr 1).continuous) continuous_const
      have hsub : Function.support (gSep X lam) ⊆ {q : V2 | |q 0| ≤ R0 ∧ |q 1| ≤ 5} :=
        fun q hq => gSep_support X lam hX q hq
      exact closure_minimal hsub hclosed hp
    have hR : R0 ≤ X := by unfold R0; linarith [Real.exp_pos 6]
    set D := 2 * (Real.exp 5 * (2 * R0)) with hD
    have hD1 : 1 ≤ D := by
      have : 1 ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
      have := two_le_R0
      rw [hD]; nlinarith
    -- composition bound
    have hcomp : ∀ i, i ≤ 4 → ‖iteratedFDeriv ℝ i (psiL lam ∘ PhiX X) p‖ ≤
        i.factorial * (M * (1 + 2 * π * |lam|) ^ 4) * D ^ i := by
      intro i hi
      apply norm_iteratedFDeriv_comp_le (N := ∞) (psiL_contDiff lam) (PhiX_contDiff X)
        (by exact_mod_cast le_top)
      · intro j hj
        refine (psiL_deriv_bound M hM lam j (hj.trans hi) _).trans ?_
        gcongr
        · have : 0 ≤ 2 * π * |lam| := by positivity
          linarith
        · exact hj.trans hi
      · intro j hj1 _
        refine (norm_iteratedFDeriv_PhiX_le X R0 two_le_R0 hR p hbox.1 hbox.2 j).trans ?_
        rw [hD, mul_pow]
        gcongr
        calc Real.exp 5 * (2 * R0) = (Real.exp 5 * (2 * R0)) ^ 1 := (pow_one _).symm
          _ ≤ (Real.exp 5 * (2 * R0)) ^ j := by
            apply pow_le_pow_right₀ _ hj1
            have : 1 ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
            have := two_le_R0
            nlinarith
    rw [gSep_eq]
    refine (norm_iteratedFDeriv_mul_le (N := ∞) ((psiL_contDiff lam).comp (PhiX_contDiff X))
      (arcC_contDiff.comp (pr 1).contDiff) p (n := n) (by exact_mod_cast le_top)).trans ?_
    have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [← hsum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hcomp i (hi'.trans hn)
    have h2 : ‖iteratedFDeriv ℝ (n - i) (arcC ∘ pr 1) p‖ ≤ M :=
      (norm_iteratedFDeriv_comp_pr arcC arcC_contDiff 1 (n - i) p).trans (hM _ (by omega) _)
    have hfac : (i.factorial : ℝ) ≤ 24 := by
      have : i.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le (hi'.trans hn)
      have h24 : (4 : ℕ).factorial = 24 := rfl
      rw [h24] at this; exact_mod_cast this
    have hDi : D ^ i ≤ D ^ 4 := pow_le_pow_right₀ hD1 (hi'.trans hn)
    have hl : 0 ≤ (1 + 2 * π * |lam|) ^ 4 := by positivity
    have hM0 : 0 ≤ M := by linarith
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psiL lam ∘ PhiX X) p‖ *
          ‖iteratedFDeriv ℝ (n - i) (arcC ∘ pr 1) p‖
        ≤ (n.choose i : ℝ) * (i.factorial * (M * (1 + 2 * π * |lam|) ^ 4) * D ^ i) * M := by
          gcongr
      _ ≤ (n.choose i : ℝ) * (24 * (M * (1 + 2 * π * |lam|) ^ 4) * D ^ 4) * M := by
          gcongr
      _ = (n.choose i : ℝ) * 24 * M ^ 2 * D ^ 4 * (1 + 2 * π * |lam|) ^ 4 := by ring
  · have : iteratedFDeriv ℝ n (gSep X lam) p = 0 := by
      by_contra h
      exact hp (support_iteratedFDeriv_subset n h)
    rw [this, norm_zero]
    positivity

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the Mellin separation (5.15)–(5.16) of [21]

For `X ≥ 10 e^6` and real `λ` there is a continuous `F : ℝ × ℝ → ℂ` with
`|F(q)| ≤ K (1 + |λ|)^4 / ((1 + q₁²)(1 + q₂²))` and, for `w, w' ∈ [1, 16]`,
`ψ_λ(X(w - w')) = ∫ F(q) e(q₁ X log w + (q₂ - X q₁) log w') dq`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff RealInnerProductSpace FourierTransform

noncomputable section

lemma gSep_support_ball (X lam : ℝ) (hX : 10 * Real.exp 6 ≤ X) :
    Function.support (gSep X lam) ⊆ Metric.closedBall (0 : V2) (R0 + 5) := by
  intro p hp
  have h := gSep_support X lam hX p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_abs_add_abs p).trans (by linarith [h.1, h.2])

lemma gSep_hasCompactSupport (X lam : ℝ) (hX : 10 * Real.exp 6 ≤ X) :
    HasCompactSupport (gSep X lam) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
    (gSep_support_ball X lam hX)

lemma integrable_iteratedFDeriv_gSep (X lam : ℝ) (hX : 10 * Real.exp 6 ≤ X) (n : ℕ) :
    Integrable (iteratedFDeriv ℝ n (gSep X lam)) :=
  ((gSep_contDiff X lam).continuous_iteratedFDeriv (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    ((gSep_hasCompactSupport X lam hX).iteratedFDeriv n)

/-- The volume of the support ball. -/
def VB : ℝ := (volume (Metric.closedBall (0 : V2) (R0 + 5))).toReal

lemma integral_norm_iteratedFDeriv_gSep_le (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ n : ℕ, n ≤ 4 →
    ∀ y : ℝ, ‖iteratedFDeriv ℝ n arcC y‖ ≤ M) (X lam : ℝ) (hX : 10 * Real.exp 6 ≤ X)
    (n : ℕ) (hn : n ≤ 4) :
    ∫ p, ‖iteratedFDeriv ℝ n (gSep X lam) p‖ ≤
      VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * (1 + 2 * π * |lam|) ^ 4) := by
  set Kd := 16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * (1 + 2 * π * |lam|) ^ 4
    with hKd
  set B := Metric.closedBall (0 : V2) (R0 + 5) with hB
  have hpt : ∀ p, ‖iteratedFDeriv ℝ n (gSep X lam) p‖ ≤ B.indicator (fun _ => Kd) p := by
    intro p
    by_cases hp : p ∈ B
    · rw [Set.indicator_of_mem hp]
      refine (gSep_deriv_bound M hM1 hM X lam hX n hn p).trans ?_
      rw [hKd]
      have h2 : (2 : ℝ) ^ n ≤ 16 := by
        calc (2 : ℝ) ^ n ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
          _ = 16 := by norm_num
      have : 0 ≤ 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * (1 + 2 * π * |lam|) ^ 4 := by
        have := two_le_R0
        positivity
      nlinarith
    · rw [Set.indicator_of_notMem hp]
      have : iteratedFDeriv ℝ n (gSep X lam) p = 0 := by
        by_contra h
        have h1 := support_iteratedFDeriv_subset n h
        have h2 : tsupport (gSep X lam) ⊆ B :=
          closure_minimal (gSep_support_ball X lam hX) Metric.isClosed_closedBall
        exact hp (h2 h1)
      rw [this, norm_zero]
  have hint : Integrable (B.indicator fun _ : V2 => Kd) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (measure_closedBall_lt_top).ne
  calc ∫ p, ‖iteratedFDeriv ℝ n (gSep X lam) p‖ ≤ ∫ p, B.indicator (fun _ => Kd) p :=
        integral_mono (integrable_iteratedFDeriv_gSep X lam hX n).norm hint hpt
    _ = VB * Kd := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
        rfl

/-- Pointwise Fourier decay: `(1 + ‖w‖^4) ‖𝓕 g (w)‖ ≤ 85 VB Kd`. -/
lemma fourier_gSep_decay (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ n : ℕ, n ≤ 4 →
    ∀ y : ℝ, ‖iteratedFDeriv ℝ n arcC y‖ ≤ M) (X lam : ℝ) (hX : 10 * Real.exp 6 ≤ X) (w : V2) :
    (1 + ‖w‖ ^ 4) * ‖𝓕 (gSep X lam) w‖ ≤
      85 * (VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 *
        (1 + 2 * π * |lam|) ^ 4)) := by
  set Kd := VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 *
        (1 + 2 * π * |lam|) ^ 4) with hKd
  have hcd : ContDiff ℝ (4 : ℕ∞) (gSep X lam) := (gSep_contDiff X lam).of_le (by
    exact_mod_cast le_top)
  have hint : ∀ (k n : ℕ), (k : ℕ∞) ≤ (0 : ℕ∞) → (n : ℕ∞) ≤ (4 : ℕ∞) →
      Integrable (fun v ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (gSep X lam) v‖) := by
    intro k n hk _
    have hk0 : k = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk
    subst hk0
    simpa using (integrable_iteratedFDeriv_gSep X lam hX n).norm
  have hsum : ∀ n : ℕ, n ≤ 4 → ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
      ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (gSep X lam) v‖ ≤ 5 * Kd := by
    intro n hn
    simp only [zero_add, Finset.range_one, Finset.singleton_product, Finset.sum_map,
      Function.Embedding.coeFn_mk, pow_zero, one_mul]
    calc ∑ x ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ x (gSep X lam) v‖
        ≤ ∑ x ∈ Finset.range (n + 1), Kd := by
          apply Finset.sum_le_sum; intro i hi
          have : i ≤ 4 := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
          exact integral_norm_iteratedFDeriv_gSep_le M hM1 hM X lam hX i this
      _ = (n + 1) * Kd := by simp
      _ ≤ 5 * Kd := by
          have : 0 ≤ Kd := by
            rw [hKd]; unfold VB; have := two_le_R0; positivity
          have : ((n : ℝ) + 1) ≤ 5 := by
            have : (n : ℝ) ≤ 4 := by exact_mod_cast hn
            linarith
          nlinarith
  have h4 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := 4) hcd hint
    (k := 0) (n := 4) le_rfl le_rfl w
  have h0 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := 4) hcd hint
    (k := 0) (n := 0) le_rfl (by norm_num) w
  rw [norm_iteratedFDeriv_zero] at h4 h0
  have hs4 := hsum 4 le_rfl
  have hs0 := hsum 0 (by norm_num)
  have e4 : (2 * π) ^ (0 : ℕ) * (2 * ((0 : ℕ) : ℝ) + 2) ^ (4 : ℕ) = 16 := by norm_num
  have e0 : (2 * π) ^ (0 : ℕ) * (2 * ((0 : ℕ) : ℝ) + 2) ^ (0 : ℕ) = 1 := by norm_num
  rw [e4] at h4
  rw [e0, pow_zero, one_mul, one_mul] at h0
  have hKd0 : 0 ≤ Kd := by rw [hKd]; unfold VB; have := two_le_R0; positivity
  nlinarith

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the Mellin separation, final form

`sep_exists`: there is `K > 0` such that for `X ≥ 10 e^6` and every real `λ` there is a
continuous `F : ℝ × ℝ → ℂ` with `‖F q‖ ≤ K (1 + |λ|)^4 / ((1 + q₁²)(1 + q₂²))` and, for
`w, w' ∈ [1, 16]`,
`ψ_λ(X (w - w')) = ∫ F(q) exp(2πi (q₁ X log w + (q₂ - X q₁) log w')) dq`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff RealInnerProductSpace FourierTransform

noncomputable section

/-- The measurable identification `ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2)`. -/
def eV : ℝ × ℝ ≃ᵐ V2 :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma eV_eq (q : ℝ × ℝ) : eV q = WithLp.toLp 2 ![q.1, q.2] := by
  ext i; fin_cases i <;> simp [eV]

lemma eV_apply0 (q : ℝ × ℝ) : eV q 0 = q.1 := by rw [eV_eq]; simp

lemma eV_apply1 (q : ℝ × ℝ) : eV q 1 = q.2 := by rw [eV_eq]; simp

lemma eV_mp : MeasurePreserving eV volume volume := by
  unfold eV
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

lemma eV_continuous : Continuous eV := by
  have : (eV : ℝ × ℝ → V2) = fun q => WithLp.toLp 2 ![q.1, q.2] := funext eV_eq
  rw [this]
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

lemma inner_eV (q r : ℝ × ℝ) : ⟪eV q, eV r⟫ = q.1 * r.1 + q.2 * r.2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, eV_apply0, eV_apply1]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma norm_eV_sq (q : ℝ × ℝ) : ‖eV q‖ ^ 2 = q.1 ^ 2 + q.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two, eV_apply0, eV_apply1]

lemma one_add_norm_pow_four_le (a : ℝ) (ha : 0 ≤ a) : (1 + a) ^ 4 ≤ 8 * (1 + a ^ 4) := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2 - a), mul_nonneg ha
    (sq_nonneg (a - 1)), mul_nonneg (mul_nonneg ha ha) (sq_nonneg (a - 1))]

lemma prod_le_two_mul (a b : ℝ) : (1 + a ^ 2) * (1 + b ^ 2) ≤ 2 * (1 + (a ^ 2 + b ^ 2) ^ 2) := by
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a ^ 2 + b ^ 2 - 1), sq_nonneg (a ^ 2 - b ^ 2)]

/-- **Mellin separation** ([21] (5.15)–(5.16)). -/
theorem sep_exists : ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 10 * Real.exp 6 ≤ X → ∀ lam : ℝ,
    ∃ F : ℝ × ℝ → ℂ, Continuous F ∧
      (∀ q : ℝ × ℝ, ‖F q‖ ≤ K * (1 + |lam|) ^ 4 / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2))) ∧
      ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
        psiL lam (X * (w - w')) = ∫ q : ℝ × ℝ, F q *
          Complex.exp (2 * π * I * (q.1 * X * Real.log w + (q.2 - X * q.1) * Real.log w')) := by
  obtain ⟨M, hM1, hM⟩ := arcC_deriv_bound
  set K0 : ℝ := 2 * 85 * (VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * 8 ^ 4))
    with hK0
  have hVB : 0 ≤ VB := ENNReal.toReal_nonneg
  have hR0 := two_le_R0
  have hK00 : 0 ≤ K0 := by rw [hK0]; positivity
  refine ⟨max K0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro X hX lam
  set g := gSep X lam with hg
  have hgc : Continuous g := (gSep_contDiff X lam).continuous
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport (gSep_hasCompactSupport X lam hX)
  set Kd := VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * (1 + 2 * π * |lam|) ^ 4)
    with hKd
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  have hdec := fourier_gSep_decay M hM1 hM X lam hX
  have hFc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by simp only [innerₗ_apply_apply]; exact continuous_fst.inner continuous_snd) hgi
  -- (1 + 2π|λ|)^4 ≤ 8^4 (1 + |λ|)^4
  have hlam : (1 + 2 * π * |lam|) ^ 4 ≤ 8 ^ 4 * (1 + |lam|) ^ 4 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have := Real.pi_lt_four
    have := abs_nonneg lam
    nlinarith
  have hKdle : Kd ≤ VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * 8 ^ 4) *
      (1 + |lam|) ^ 4 := by
    rw [hKd]
    have : 0 ≤ 16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 := by positivity
    calc VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 * (1 + 2 * π * |lam|) ^ 4)
        ≤ VB * (16 * 24 * M ^ 2 * (2 * (Real.exp 5 * (2 * R0))) ^ 4 *
            (8 ^ 4 * (1 + |lam|) ^ 4)) := by gcongr
      _ = _ := by ring
  -- integrability of 𝓕 g
  have hFi : Integrable (𝓕 g) := by
    have hfin : ((Module.finrank ℝ V2 : ℕ) : ℝ) < (4 : ℝ) := by
      rw [finrank_euclideanSpace_fin]; norm_num
    have hI := (integrable_one_add_norm (E := V2) (μ := volume) hfin).const_mul (8 * (85 * Kd))
    refine hI.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    have hw := hdec w
    have h1 : 0 < 1 + ‖w‖ := by positivity
    have h2 : (1 + ‖w‖) ^ 4 ≤ 8 * (1 + ‖w‖ ^ 4) := one_add_norm_pow_four_le _ (norm_nonneg _)
    have h3 : (1 + ‖w‖) ^ (-(4 : ℝ)) = ((1 + ‖w‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg h1.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h3]
    have h4 : 0 < 1 + ‖w‖ ^ 4 := by positivity
    have h5 : ‖𝓕 g w‖ ≤ 85 * Kd / (1 + ‖w‖ ^ 4) := by
      rw [le_div_iff₀ h4]; linarith
    calc ‖𝓕 g w‖ ≤ 85 * Kd / (1 + ‖w‖ ^ 4) := h5
      _ ≤ 85 * Kd / ((1 + ‖w‖) ^ 4 / 8) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith
      _ = 8 * (85 * Kd) * ((1 + ‖w‖) ^ 4)⁻¹ := by
          field_simp
  refine ⟨fun q => 𝓕 g (eV q), hFc.comp eV_continuous, ?_, ?_⟩
  · intro q
    have hw := hdec (eV q)
    have hn := norm_eV_sq q
    have hpr : 0 < (1 + q.1 ^ 2) * (1 + q.2 ^ 2) := by positivity
    have h4 : 0 < 1 + ‖eV q‖ ^ 4 := by positivity
    have hle : (1 + q.1 ^ 2) * (1 + q.2 ^ 2) ≤ 2 * (1 + ‖eV q‖ ^ 4) := by
      have := prod_le_two_mul q.1 q.2
      rw [show ‖eV q‖ ^ 4 = (‖eV q‖ ^ 2) ^ 2 by ring, hn]
      exact this
    rw [le_div_iff₀ hpr]
    have hA : ‖𝓕 g (eV q)‖ * ((1 + q.1 ^ 2) * (1 + q.2 ^ 2)) ≤ 2 * (85 * Kd) := by
      calc ‖𝓕 g (eV q)‖ * ((1 + q.1 ^ 2) * (1 + q.2 ^ 2))
          ≤ ‖𝓕 g (eV q)‖ * (2 * (1 + ‖eV q‖ ^ 4)) := by gcongr
        _ = 2 * ((1 + ‖eV q‖ ^ 4) * ‖𝓕 g (eV q)‖) := by ring
        _ ≤ 2 * (85 * Kd) := by linarith
    have hB : 2 * (85 * Kd) ≤ K0 * (1 + |lam|) ^ 4 := by
      rw [hK0]
      have := hKdle
      nlinarith
    have hC : K0 * (1 + |lam|) ^ 4 ≤ max K0 1 * (1 + |lam|) ^ 4 := by
      gcongr; exact le_max_left _ _
    linarith
  · intro w w' hw1 hw2 hw'1 hw'2
    have hw0 : 0 < w := by linarith
    have hw'0 : 0 < w' := by linarith
    have hX0 : 0 < X := by linarith [Real.exp_pos 6]
    set p : V2 := eV (X * (Real.log w - Real.log w'), Real.log w') with hp
    have hgp : g p = psiL lam (X * (w - w')) := by
      rw [hg]
      unfold gSep PhiX uX
      rw [hp, eV_apply0, eV_apply1]
      have hl : |Real.log w'| ≤ 4 := by
        have h0 : 0 ≤ Real.log w' := Real.log_nonneg hw'1
        rw [abs_of_nonneg h0]
        have : Real.log w' ≤ Real.log 16 := Real.log_le_log hw'0 hw'2
        have h16 : Real.log 16 < 4 := by
          rw [Real.log_lt_iff_lt_exp (by norm_num)]
          have := Real.add_one_le_exp (4 : ℝ)
          have h2 : (16 : ℝ) < Real.exp 4 := by
            have e : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
            have := Real.add_one_le_exp (2 : ℝ)
            have h7 : (7.3 : ℝ) < Real.exp 2 := by
              have := Real.exp_one_gt_d9
              have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
                rw [← Real.exp_add]; norm_num
              nlinarith
            nlinarith
          exact h2
        linarith
      have harc : arcC (Real.log w') = 1 := by simp [arcC, arcCutoff_eq_one hl]
      rw [harc, mul_one, Real.exp_log hw'0]
      congr 1
      rw [mul_div_cancel_left₀ _ hX0.ne', ← Real.log_div hw0.ne' hw'0.ne',
        Real.exp_log (div_pos hw0 hw'0)]
      field_simp
    have hinv := hgc.fourierInv_fourier_eq hgi hFi
    have hgp' : g p = 𝓕⁻ (𝓕 g) p := by rw [hinv]
    rw [← hgp, hgp', fourierInv_eq', ← eV_mp.integral_comp']
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun q => ?_
    simp only [smul_eq_mul]
    rw [hp, inner_eV, mul_comm]
    congr 2
    push_cast
    ring

end

end ArtinPrimitiveRoots.L102M
end

section
namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution : ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 10 * Real.exp 6 ≤ X → ∀ lam : ℝ,
    ∃ F : ℝ × ℝ → ℂ, Continuous F ∧
      (∀ q : ℝ × ℝ, ‖F q‖ ≤ K * (1 + |lam|) ^ 4 / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2))) ∧
      ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
        (arcCutoff (X * (w - w')) : ℂ) *
            Complex.exp (2 * π * Complex.I * lam * ((X * (w - w') : ℝ) : ℂ)) =
          ∫ q : ℝ × ℝ, F q * Complex.exp (2 * π * Complex.I *
            (q.1 * X * Real.log w + (q.2 - X * q.1) * Real.log w')) := by
  exact L102M.sep_exists
end
