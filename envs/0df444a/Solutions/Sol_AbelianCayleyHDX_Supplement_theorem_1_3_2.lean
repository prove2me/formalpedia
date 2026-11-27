-- Prove2me | solution 2 for AbelianCayleyHDX.Supplement.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:05:35.907732+00:00
-- url     : https://prove2.me/submissions/ce7cbbf3-e43b-427f-bd8e-a778ab2a6b7e

import Mathlib
import Definitions.Def_AbelianCayleyHDX_Supplement_cubeLabelComplex
import Definitions.Def_AbelianCayleyHDX_edges
import Definitions.Def_AbelianCayleyHDX_Supplement_faceMass
import Definitions.Def_AbelianCayleyHDX_Supplement_wLinkVerts
import Definitions.Def_AbelianCayleyHDX_Supplement_wLinkWeight
import Definitions.Def_AbelianCayleyHDX_Supplement_LinkConnected
import Definitions.Def_AbelianCayleyHDX_Supplement_IsFace
import Definitions.Def_AbelianCayleyHDX_IsTwoSidedSpectralExpander
import Theorems.Thm_AbelianCayleyHDX_Supplement_explicit_cube_label_family_log
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Theorems.Thm_AbelianCayleyHDX_lemma_2_1
import Definitions.Def_AbelianCayleyHDX_cayleyGraph
import Definitions.Def_AbelianCayleyHDX_Supplement_IsWeightedCayleyComplex
import Definitions.Def_AbelianCayleyHDX_Supplement_IsWeightedTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_Supplement_HasCodimTwoLocalSpectralNorm

namespace AbelianCayleyHDX.Tensor

open Finset

variable {W : Type*} [Fintype W]

/-- Weighted Cauchy–Schwarz: the random walk is a contraction in `L²(D)`. -/
lemma contraction (aW : W → W → ℝ) (hsym : ∀ w w', aW w w' = aW w' w)
    (hnn : ∀ w w', 0 ≤ aW w w') (hD : ∀ w, 0 < ∑ w', aW w w') (g : W → ℝ) :
    ∑ w, (∑ w', aW w w') * ((∑ w', aW w w' * g w') / (∑ w', aW w w')) ^ 2 ≤
      ∑ w, (∑ w', aW w w') * g w ^ 2 := by
  have h1 : ∀ w, (∑ w', aW w w') * ((∑ w', aW w w' * g w') / (∑ w', aW w w')) ^ 2 ≤
      ∑ w', aW w w' * g w' ^ 2 := by
    intro w
    have hDw := hD w
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    -- Cauchy–Schwarz: (∑ a g)² ≤ (∑ a)(∑ a g²)
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w' => Real.sqrt (aW w w'))
      (fun w' => Real.sqrt (aW w w') * g w')
    have e1 : ∀ w', Real.sqrt (aW w w') * (Real.sqrt (aW w w') * g w') = aW w w' * g w' := by
      intro w'; rw [← mul_assoc, Real.mul_self_sqrt (hnn w w')]
    have e2 : ∀ w', Real.sqrt (aW w w') ^ 2 = aW w w' := fun w' => Real.sq_sqrt (hnn w w')
    have e3 : ∀ w', (Real.sqrt (aW w w') * g w') ^ 2 = aW w w' * g w' ^ 2 := by
      intro w'; rw [mul_pow, e2]
    simp only [e1, e2, e3] at cs
    nlinarith [cs]
  calc ∑ w, (∑ w', aW w w') * ((∑ w', aW w w' * g w') / (∑ w', aW w w')) ^ 2
      ≤ ∑ w, ∑ w', aW w w' * g w' ^ 2 := Finset.sum_le_sum (fun w _ => h1 w)
    _ = ∑ w', (∑ w, aW w w') * g w' ^ 2 := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun w' _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ w, (∑ w', aW w w') * g w ^ 2 := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        congr 1; exact Finset.sum_congr rfl (fun w' _ => hsym w' w)

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The product weight on `W × L`: position weight times "labels differ". -/
def prodW (aW : W → W → ℝ) (p q : W × L) : ℝ := aW p.1 q.1 * (if p.2 = q.2 then 0 else 1)

lemma deg_prodW (aW : W → W → ℝ) (p : W × L) :
    ∑ q, prodW aW p q = (∑ w', aW p.1 w') * ((Fintype.card L : ℝ) - 1) := by
  rw [Fintype.sum_prod_type]
  simp only [prodW]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun w' _ => ?_)
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.univ.filter fun l : L => ¬ p.2 = l) = Finset.univ.erase p.2 := by
    ext l; simp [eq_comm]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [Nat.cast_sub (Fintype.card_pos_iff.2 ⟨p.2⟩)]; simp

/-- **Tensor lemma.** If the position chain has norm `≤ λ` on mean-zero functions and
`λ ≥ 1/(|L| - 1)`, the product chain (positions × complete graph on labels) has norm `≤ λ`. -/
theorem tensor_bound (aW : W → W → ℝ) (hsym : ∀ w w', aW w w' = aW w' w)
    (hnn : ∀ w w', 0 ≤ aW w w') (hD : ∀ w, 0 < ∑ w', aW w w') (lam : ℝ) (hlam : 0 ≤ lam)
    (hL : 2 ≤ Fintype.card L) (hlamL : 1 / ((Fintype.card L : ℝ) - 1) ≤ lam)
    (hW : ∀ g : W → ℝ, ∑ w, (∑ w', aW w w') * g w = 0 →
      ∑ w, (∑ w', aW w w') * ((∑ w', aW w w' * g w') / (∑ w', aW w w')) ^ 2 ≤
        lam ^ 2 * ∑ w, (∑ w', aW w w') * g w ^ 2)
    (f : W × L → ℝ) (hf : ∑ p, (∑ q, prodW aW p q) * f p = 0) :
    ∑ p, (∑ q, prodW aW p q) * ((∑ q, prodW aW p q * f q) / (∑ q, prodW aW p q)) ^ 2 ≤
      lam ^ 2 * ∑ p, (∑ q, prodW aW p q) * f p ^ 2 := by
  set m : ℝ := (Fintype.card L : ℝ) with hmdef
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hL
  have hm1 : 0 < m - 1 := by linarith
  set D : W → ℝ := fun w => ∑ w', aW w w' with hDdef
  set PW : (W → ℝ) → W → ℝ := fun g w => (∑ w', aW w w' * g w') / D w with hPW
  -- label averages and fluctuations
  set G : W → ℝ := fun w => (∑ l, f (w, l)) / m with hG
  set h : W × L → ℝ := fun p => f p - G p.1 with hh
  have hsumh : ∀ w, ∑ l, h (w, l) = 0 := by
    intro w
    simp only [hh, hG, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [← hmdef]; field_simp; ring
  have hdeg : ∀ p : W × L, ∑ q, prodW aW p q = D p.1 * (m - 1) := fun p => deg_prodW aW p
  -- the numerator of the walk
  have hnum : ∀ p : W × L, ∑ q, prodW aW p q * f q =
      ∑ w', aW p.1 w' * ((m - 1) * G w' - h (w', p.2)) := by
    intro p
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun w' _ => ?_)
    simp only [prodW, mul_assoc, ← Finset.mul_sum]
    congr 1
    have e : ∑ l', (if p.2 = l' then (0 : ℝ) else 1) * f (w', l') = ∑ l', f (w', l') - f (w', p.2) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p.2)]
      simp only [if_true, zero_mul, add_zero]
      rw [← Finset.sum_erase_add (Finset.univ : Finset L) (fun l' => f (w', l'))
        (Finset.mem_univ p.2)]
      simp only [add_sub_cancel_right]
      refine Finset.sum_congr rfl (fun l' hl' => ?_)
      rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hl')), one_mul]
    rw [e]
    simp only [hh, hG]
    field_simp
    ring
  have hP : ∀ p : W × L, (∑ q, prodW aW p q * f q) / (∑ q, prodW aW p q) =
      PW G p.1 - (1 / (m - 1)) * PW (fun w => h (w, p.2)) p.1 := by
    intro p
    rw [hnum, hdeg]
    have hDp : 0 < D p.1 := hD p.1
    simp only [hPW]
    field_simp
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun w' _ => ?_)
    ring
  -- mean zero of `G`
  have hG0 : ∑ w, D w * G w = 0 := by
    have : ∑ p : W × L, (∑ q, prodW aW p q) * f p = (m - 1) * m * ∑ w, D w * G w := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [hdeg, hG]
      rw [← Finset.mul_sum]
      field_simp
    rw [this] at hf
    rcases mul_eq_zero.1 hf with h1 | h1
    · exfalso; nlinarith
    · exact h1
  -- the key identity for the sum of squares of `P f`
  have hPW_sum : ∀ w, ∑ l, PW (fun w => h (w, l)) w = 0 := by
    intro w
    simp only [hPW]
    rw [← Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hsumh, mul_zero, Finset.sum_const_zero, zero_div]
  set c : ℝ := 1 / (m - 1) with hc
  have hLHS : ∑ p, (∑ q, prodW aW p q) * ((∑ q, prodW aW p q * f q) / (∑ q, prodW aW p q)) ^ 2 =
      (m - 1) * (m * ∑ w, D w * PW G w ^ 2 +
        c ^ 2 * ∑ l, ∑ w, D w * PW (fun w => h (w, l)) w ^ 2) := by
    have step1 : ∀ w, ∑ l, D w * (m - 1) * (PW G w - c * PW (fun w => h (w, l)) w) ^ 2 =
        (m - 1) * (m * (D w * PW G w ^ 2) + c ^ 2 * ∑ l, D w * PW (fun w => h (w, l)) w ^ 2) := by
      intro w
      have e : ∀ l, D w * (m - 1) * (PW G w - c * PW (fun w => h (w, l)) w) ^ 2 =
          (m - 1) * (D w * PW G w ^ 2) - (m - 1) * (2 * c * D w * PW G w) *
            PW (fun w => h (w, l)) w + (m - 1) * c ^ 2 * (D w * PW (fun w => h (w, l)) w ^ 2) := by
        intro l; ring
      simp only [e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, hPW_sum w, ← hmdef]
      ring
    calc ∑ p, (∑ q, prodW aW p q) * ((∑ q, prodW aW p q * f q) / (∑ q, prodW aW p q)) ^ 2
        = ∑ w, ∑ l, D w * (m - 1) * (PW G w - c * PW (fun w => h (w, l)) w) ^ 2 := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun l _ => ?_))
          rw [hP (w, l), hdeg (w, l)]
      _ = ∑ w, (m - 1) * (m * (D w * PW G w ^ 2) +
            c ^ 2 * ∑ l, D w * PW (fun w => h (w, l)) w ^ 2) := Finset.sum_congr rfl (fun w _ => step1 w)
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_comm (f := fun w l => D w * PW (fun w => h (w, l)) w ^ 2)]
  have hRHS : ∑ p, (∑ q, prodW aW p q) * f p ^ 2 =
      (m - 1) * (m * ∑ w, D w * G w ^ 2 + ∑ l, ∑ w, D w * h (w, l) ^ 2) := by
    have step1 : ∀ w, ∑ l, D w * (m - 1) * f (w, l) ^ 2 =
        (m - 1) * (m * (D w * G w ^ 2) + ∑ l, D w * h (w, l) ^ 2) := by
      intro w
      have e : ∀ l, D w * (m - 1) * f (w, l) ^ 2 =
          (m - 1) * (D w * G w ^ 2) + (m - 1) * (2 * D w * G w) * h (w, l) +
            (m - 1) * (D w * h (w, l) ^ 2) := by
        intro l
        have : f (w, l) = G w + h (w, l) := by simp only [hh]; ring
        rw [this]; ring
      simp only [e]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, hsumh w, ← hmdef]
      ring
    calc ∑ p, (∑ q, prodW aW p q) * f p ^ 2
        = ∑ w, ∑ l, D w * (m - 1) * f (w, l) ^ 2 := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun l _ => ?_))
          rw [hdeg (w, l)]
      _ = ∑ w, (m - 1) * (m * (D w * G w ^ 2) + ∑ l, D w * h (w, l) ^ 2) :=
          Finset.sum_congr rfl (fun w _ => step1 w)
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_comm (f := fun w l => D w * h (w, l) ^ 2)]
  rw [hLHS, hRHS]
  -- bound the two pieces
  have hb1 : ∑ w, D w * PW G w ^ 2 ≤ lam ^ 2 * ∑ w, D w * G w ^ 2 := hW G hG0
  have hb2 : ∀ l, ∑ w, D w * PW (fun w => h (w, l)) w ^ 2 ≤ ∑ w, D w * h (w, l) ^ 2 :=
    fun l => contraction aW hsym hnn hD (fun w => h (w, l))
  have hb2' : ∑ l, ∑ w, D w * PW (fun w => h (w, l)) w ^ 2 ≤ ∑ l, ∑ w, D w * h (w, l) ^ 2 :=
    Finset.sum_le_sum (fun l _ => hb2 l)
  have hq : c ^ 2 ≤ lam ^ 2 := pow_le_pow_left₀ (by positivity) hlamL 2
  have hnn2 : 0 ≤ ∑ l, ∑ w, D w * h (w, l) ^ 2 :=
    Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun w _ =>
      mul_nonneg (hD w).le (sq_nonneg _)))
  have hnn1 : 0 ≤ ∑ l, ∑ w, D w * PW (fun w => h (w, l)) w ^ 2 :=
    Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun w _ =>
      mul_nonneg (hD w).le (sq_nonneg _)))
  have : m * ∑ w, D w * PW G w ^ 2 + c ^ 2 * ∑ l, ∑ w, D w * PW (fun w => h (w, l)) w ^ 2
      ≤ lam ^ 2 * (m * ∑ w, D w * G w ^ 2 + ∑ l, ∑ w, D w * h (w, l) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hb1 (by linarith : (0 : ℝ) ≤ m)
    have h2 : c ^ 2 * ∑ l, ∑ w, D w * PW (fun w => h (w, l)) w ^ 2 ≤
        lam ^ 2 * ∑ l, ∑ w, D w * h (w, l) ^ 2 :=
      mul_le_mul hq hb2' hnn1 (by positivity)
    nlinarith
  nlinarith

end AbelianCayleyHDX.Tensor


namespace AbelianCayleyHDX.Pos

open Finset

/-! ### The centre-with-pages chain (a face inside one fibre) -/

/-- Positions: `none` = the fibre of the face, `some i` = the neighbouring fibre in direction `i`.
Weights: centre–centre `(d-1)kβ`, centre–page `β`, page–page (same page) `β/(d-1)`. -/
noncomputable def starW (d k : ℕ) (β : ℝ) : Option (Fin k) → Option (Fin k) → ℝ
  | none, none => ((d : ℝ) - 1) * k * β
  | none, some _ => β
  | some _, none => β
  | some i, some j => if i = j then β / ((d : ℝ) - 1) else 0

lemma starW_symm (d k : ℕ) (β : ℝ) (w w' : Option (Fin k)) : starW d k β w w' = starW d k β w' w := by
  cases w <;> cases w' <;> simp [starW, eq_comm]

lemma starW_nn (d k : ℕ) (hd : 2 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (w w' : Option (Fin k)) :
    0 ≤ starW d k β w w' := by
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  cases w <;> cases w' <;> simp only [starW]
  · positivity
  · exact hβ
  · exact hβ
  · split_ifs <;> positivity

lemma starW_deg_none (d k : ℕ) (β : ℝ) :
    ∑ w', starW d k β none w' = (d : ℝ) * k * β := by
  rw [Fintype.sum_option]; simp [starW]; ring

lemma starW_deg_some (d k : ℕ) (hd : 2 ≤ d) (β : ℝ) (i : Fin k) :
    ∑ w', starW d k β (some i) w' = (d : ℝ) * β / ((d : ℝ) - 1) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h; linarith
  rw [Fintype.sum_option]; simp only [starW]
  rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]
  field_simp; ring

lemma starW_deg_pos (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (β : ℝ) (hβ : 0 < β)
    (w : Option (Fin k)) : 0 < ∑ w', starW d k β w w' := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  cases w with
  | none => rw [starW_deg_none]; have : (1 : ℝ) ≤ k := by exact_mod_cast hk
            positivity
  | some i => rw [starW_deg_some d k hd]; apply div_pos (by positivity); linarith

theorem star_bound (d k : ℕ) (hd : 2 ≤ d) (hk : 1 ≤ k) (β : ℝ) (hβ : 0 < β)
    (g : Option (Fin k) → ℝ)
    (hg : ∑ w, (∑ w', starW d k β w w') * g w = 0) :
    ∑ w, (∑ w', starW d k β w w') *
        ((∑ w', starW d k β w w' * g w') / (∑ w', starW d k β w w')) ^ 2 ≤
      (1 / (d : ℝ)) ^ 2 * ∑ w, (∑ w', starW d k β w w') * g w ^ 2 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- numerators
  have hNn : ∑ w', starW d k β none w' * g w' =
      ((d : ℝ) - 1) * k * β * g none + β * ∑ i : Fin k, g (some i) := by
    rw [Fintype.sum_option]; simp [starW, Finset.mul_sum]
  have hNs : ∀ i, ∑ w', starW d k β (some i) w' * g w' =
      β * g none + β / ((d : ℝ) - 1) * g (some i) := by
    intro i
    rw [Fintype.sum_option]; simp only [starW]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- mean zero
  rw [Fintype.sum_option (fun w => (∑ w', starW d k β w w') * g w), starW_deg_none] at hg
  simp only [starW_deg_some d k hd] at hg
  rw [← Finset.mul_sum] at hg
  have hS1v : ∑ i : Fin k, g (some i) = -((d : ℝ) - 1) * k * g none := by
    have : (d : ℝ) * β / ((d : ℝ) - 1) * ∑ i : Fin k, g (some i) = -((d : ℝ) * k * β * g none) := by
      linarith
    field_simp at this
    rw [this]; ring
  rw [Fintype.sum_option (fun w => (∑ w', starW d k β w w') *
      ((∑ w', starW d k β w w' * g w') / (∑ w', starW d k β w w')) ^ 2),
    Fintype.sum_option (fun w => (∑ w', starW d k β w w') * g w ^ 2), starW_deg_none, hNn]
  simp only [starW_deg_some d k hd, hNs]
  have hNn0 : ((d : ℝ) - 1) * k * β * g none + β * ∑ i : Fin k, g (some i) = 0 := by
    rw [hS1v]; ring
  rw [hNn0]
  -- the page terms
  have hpage : ∀ i, (d : ℝ) * β / ((d : ℝ) - 1) *
      ((β * g none + β / ((d : ℝ) - 1) * g (some i)) / ((d : ℝ) * β / ((d : ℝ) - 1))) ^ 2 =
      β / ((d : ℝ) * ((d : ℝ) - 1)) * (((d : ℝ) - 1) * g none + g (some i)) ^ 2 := by
    intro i; field_simp
  simp only [hpage]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hexp : ∑ i : Fin k, (((d : ℝ) - 1) * g none + g (some i)) ^ 2 =
      k * ((d : ℝ) - 1) ^ 2 * g none ^ 2 + 2 * ((d : ℝ) - 1) * g none * ∑ i : Fin k, g (some i) +
        ∑ i : Fin k, g (some i) ^ 2 := by
    have : ∀ i : Fin k, (((d : ℝ) - 1) * g none + g (some i)) ^ 2 =
        ((d : ℝ) - 1) ^ 2 * g none ^ 2 + (2 * ((d : ℝ) - 1) * g none) * g (some i) +
          g (some i) ^ 2 := by
      intro i; ring
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hexp, hS1v]
  have hS2nn : 0 ≤ ∑ i : Fin k, g (some i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have e0 : ((d : ℝ) * k * β) * (0 / ((d : ℝ) * k * β)) ^ 2 = 0 := by simp
  rw [e0, zero_add]
  set S2 := ∑ i : Fin k, g (some i) ^ 2
  set gn := g none
  have hgn : 0 ≤ gn ^ 2 := sq_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hβ.le hgn) (by positivity : (0 : ℝ) ≤ (k : ℝ) * (d : ℝ)),
    mul_nonneg hβ.le hS2nn, mul_nonneg (mul_nonneg hβ.le hgn) (by positivity : (0 : ℝ) ≤ (k : ℝ)),
    mul_nonneg (mul_nonneg (mul_nonneg hβ.le hgn) (by positivity : (0 : ℝ) ≤ (k : ℝ)))
      (by positivity : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) - 1))]

/-! ### The two-point chain (a face split across an edge) -/

/-- Weights `p` (inside the first fibre), `r` (across), `s` (inside the second fibre). -/
def pairW (p r s : ℝ) : Bool → Bool → ℝ
  | true, true => p
  | true, false => r
  | false, true => r
  | false, false => s

lemma pairW_symm (p r s : ℝ) (w w' : Bool) : pairW p r s w w' = pairW p r s w' w := by
  cases w <;> cases w' <;> rfl

theorem pair_bound (p r s μ : ℝ) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hμ : (p * s - r ^ 2) / ((p + r) * (r + s)) = μ) (g : Bool → ℝ)
    (hg : ∑ w, (∑ w', pairW p r s w w') * g w = 0) :
    ∑ w, (∑ w', pairW p r s w w') *
        ((∑ w', pairW p r s w w' * g w') / (∑ w', pairW p r s w w')) ^ 2 =
      μ ^ 2 * ∑ w, (∑ w', pairW p r s w w') * g w ^ 2 := by
  simp only [Fintype.sum_bool, pairW] at hg ⊢
  -- `g false = -(p+r)/(r+s) * g true`
  have hgf : g false = -(p + r) / (r + s) * g true := by
    field_simp; linarith
  rw [hgf, ← hμ]
  field_simp
  ring

end AbelianCayleyHDX.Pos

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset

/-! ### Positions and labels -/

section Basic
variable {k a : ℕ}

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma vadd_self' {m : ℕ} (x : Vec m) : x + x = 0 := by
  ext i; simp only [Pi.add_apply, Pi.zero_apply]; exact z2_add_self _

lemma pos_add (x y : Vec (k + a)) : pos (x + y) = pos x + pos y := rfl
lemma lab_add (x y : Vec (k + a)) : lab (x + y) = lab x + lab y := rfl
lemma pos_zero : pos (0 : Vec (k + a)) = 0 := rfl
lemma lab_zero : lab (0 : Vec (k + a)) = 0 := rfl

/-- Assemble a vertex from its cube coordinate and its label. -/
def emb (u : Vec k) (b : Vec a) : Vec (k + a) := Fin.append u b

@[simp] lemma pos_emb (u : Vec k) (b : Vec a) : pos (emb u b) = u := by
  funext i; simp [pos, emb, Fin.append_left]

@[simp] lemma lab_emb (u : Vec k) (b : Vec a) : lab (emb u b) = b := by
  funext i; simp [lab, emb, Fin.append_right]

lemma emb_pos_lab (x : Vec (k + a)) : emb (pos x) (lab x) = x := by
  simp only [emb, pos, lab]
  exact Fin.append_castAdd_natAdd

lemma ext_pl {x y : Vec (k + a)} (h1 : pos x = pos y) (h2 : lab x = lab y) : x = y := by
  rw [← emb_pos_lab x, ← emb_pos_lab y, h1, h2]

lemma emb_add (u u' : Vec k) (b b' : Vec a) : emb u b + emb u' b' = emb (u + u') (b + b') := by
  apply ext_pl <;> simp [pos_add, lab_add]

lemma vec_eq_iff_add_eq_zero {m : ℕ} (x y : Vec m) : x = y ↔ x + y = 0 := by
  constructor
  · rintro rfl; exact vadd_self' x
  · intro h; have := congrArg (· + y) h; simpa [add_assoc, vadd_self'] using this

/-- Two cube coordinates are equal or adjacent. -/
def PosAdj (u v : Vec k) : Prop := u + v = 0 ∨ ∃ i : Fin k, u + v = Pi.single i 1

lemma posAdj_symm {u v : Vec k} : PosAdj u v → PosAdj v u := by
  unfold PosAdj; rw [add_comm]; exact id

lemma mem_gens {s : Vec (k + a)} :
    s ∈ gens k a ↔ lab s ≠ 0 ∧ PosAdj (pos s) 0 := by
  simp [gens, PosAdj]

lemma add_mem_gens {x y : Vec (k + a)} :
    x + y ∈ gens k a ↔ lab x ≠ lab y ∧ PosAdj (pos x) (pos y) := by
  rw [mem_gens, lab_add, pos_add]
  simp only [PosAdj, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by rw [h, vadd_self']), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 ((vec_eq_iff_add_eq_zero _ _).2 h), h2⟩

/-- Unit vectors: `e_i + e_j` is neither `0` nor a unit vector when `i ≠ j`. -/
lemma single_add_single_ne {i j : Fin k} (hij : i ≠ j) :
    (Pi.single i 1 + Pi.single j 1 : Vec k) ≠ 0 ∧
      ∀ l, (Pi.single i 1 + Pi.single j 1 : Vec k) ≠ Pi.single l 1 := by
  constructor
  · intro h; have := congrFun h i; simp [Pi.single_apply, hij] at this
  · intro l h
    have hi : (Pi.single l (1 : ZMod 2) : Vec k) i = 1 := by rw [← h]; simp [hij]
    have hj : (Pi.single l (1 : ZMod 2) : Vec k) j = 1 := by rw [← h]; simp [Ne.symm hij]
    have h1 : i = l := by
      by_contra hne; rw [Pi.single_apply, if_neg hne] at hi; exact zero_ne_one hi
    have h2 : j = l := by
      by_contra hne; rw [Pi.single_apply, if_neg hne] at hj; exact zero_ne_one hj
    exact hij (h1.trans h2.symm)

lemma single_ne_zero' (i : Fin k) : (Pi.single i 1 : Vec k) ≠ 0 := by
  intro h; have := congrFun h i; simp at this

lemma single_inj' {i j : Fin k} (h : (Pi.single i 1 : Vec k) = Pi.single j 1) : i = j := by
  by_contra hij
  have := congrFun h i
  simp [Pi.single_apply, hij] at this

end Basic

/-! ### Cliques -/

section Cliques
variable {d k a : ℕ}

/-- A clique of the Cayley graph. -/
def IsClique (T : Finset (Vec (k + a))) : Prop := ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x + y ∈ gens k a

lemma mem_tops {T : Finset (Vec (k + a))} : T ∈ tops d k a ↔ T.card = d + 1 ∧ IsClique T := by
  simp [tops, IsClique]

lemma IsClique.subset {T T' : Finset (Vec (k + a))} (h : IsClique T) (hs : T' ⊆ T) :
    IsClique T' := fun x hx y hy hxy => h x (hs hx) y (hs hy) hxy

lemma IsClique.lab_inj {T : Finset (Vec (k + a))} (h : IsClique T) {x y : Vec (k + a)}
    (hx : x ∈ T) (hy : y ∈ T) (hl : lab x = lab y) : x = y := by
  by_contra hxy
  exact (add_mem_gens.1 (h x hx y hy hxy)).1 hl

lemma IsClique.posAdj {T : Finset (Vec (k + a))} (h : IsClique T) {x y : Vec (k + a)}
    (hx : x ∈ T) (hy : y ∈ T) : PosAdj (pos x) (pos y) := by
  by_cases hxy : x = y
  · subst hxy; left; exact vadd_self' _
  · exact (add_mem_gens.1 (h x hx y hy hxy)).2

/-- The positions of a clique lie in one cube edge: if `x, y, z` are in a clique and
`pos y ≠ pos x`, then `pos z ∈ {pos x, pos y}`. -/
lemma IsClique.pos_two {T : Finset (Vec (k + a))} (h : IsClique T) {x y z : Vec (k + a)}
    (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T) (hxy : pos x ≠ pos y) :
    pos z = pos x ∨ pos z = pos y := by
  have h1 := h.posAdj hx hy
  have h2 := h.posAdj hx hz
  have h3 := h.posAdj hy hz
  rcases h1 with h1 | ⟨i, hi⟩
  · exact absurd ((vec_eq_iff_add_eq_zero _ _).2 h1) hxy
  rcases h2 with h2 | ⟨j, hj⟩
  · left; exact ((vec_eq_iff_add_eq_zero _ _).2 h2).symm
  rcases h3 with h3 | ⟨l, hl⟩
  · right; exact ((vec_eq_iff_add_eq_zero _ _).2 h3).symm
  -- pos y = pos x + e_i, pos z = pos x + e_j, pos y + pos z = e_l
  exfalso
  have : (Pi.single i 1 + Pi.single j 1 : Vec k) = Pi.single l 1 := by
    rw [← hi, ← hj, ← hl]
    ext t; simp only [Pi.add_apply]
    generalize pos x t = p; generalize pos y t = q; generalize pos z t = r
    revert p q r; decide
  by_cases hij : i = j
  · subst hij
    rw [vadd_self'] at this
    exact single_ne_zero' l this.symm
  · exact (single_add_single_ne hij).2 l this

/-- A nonempty clique with at most `d + 1` points extends to a top face, when there are at least
`d + 1` labels. -/
lemma exists_top_of_clique (ha : d + 1 ≤ 2 ^ a) {σ : Finset (Vec (k + a))} (hσ : IsClique σ)
    (hne : σ.Nonempty) (hcard : σ.card ≤ d + 1) : ∃ τ ∈ tops d k a, σ ⊆ τ := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  -- fresh labels
  set fresh := (Finset.univ : Finset (Vec a)) \ σ.image lab with hfresh
  have hfc : d + 1 - σ.card ≤ fresh.card := by
    rw [hfresh, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have : (σ.image lab).card ≤ σ.card := Finset.card_image_le
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    omega
  obtain ⟨Λ, hΛ, hΛc⟩ := Finset.exists_subset_card_eq hfc
  set new := Λ.image (emb (pos x0)) with hnew
  have hnewc : new.card = Λ.card := Finset.card_image_of_injective _ (fun b b' h => by
    simpa using congrArg lab h)
  have hdisj : Disjoint σ new := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy'
    have := hΛ hb
    rw [hfresh, Finset.mem_sdiff] at this
    exact this.2 (Finset.mem_image.2 ⟨_, hy, by simp⟩)
  refine ⟨σ ∪ new, ?_, Finset.subset_union_left⟩
  rw [mem_tops]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hnewc, hΛc]; omega
  · intro y hy z hz hyz
    rw [Finset.mem_union] at hy hz
    rw [add_mem_gens]
    have hfr : ∀ b ∈ Λ, b ∉ σ.image lab := by
      intro b hb; have := hΛ hb; rw [hfresh, Finset.mem_sdiff] at this; exact this.2
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact add_mem_gens.1 (hσ y hy z hz hyz)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hz
      refine ⟨fun h => hfr b hb (Finset.mem_image.2 ⟨y, hy, by simpa using h⟩), ?_⟩
      simpa using hσ.posAdj hy hx0
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      refine ⟨fun h => hfr b hb (Finset.mem_image.2 ⟨z, hz, by simpa using h.symm⟩), ?_⟩
      simpa using hσ.posAdj hx0 hz
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hz
      refine ⟨fun h => hyz (by simp at h; rw [h]), ?_⟩
      left; simp [vadd_self']

end Cliques

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset

variable {d k a : ℕ}

/-- The number of points of `T` in the fibre of `x`. -/
def cnt (T : Finset (Vec (k + a))) (x : Vec (k + a)) : ℕ := (T.filter fun y => pos y = pos x).card

lemma cnt_pos {T : Finset (Vec (k + a))} {x : Vec (k + a)} (hx : x ∈ T) : 1 ≤ cnt T x :=
  Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hx, rfl⟩⟩

lemma cnt_add_cnt {T : Finset (Vec (k + a))} (hT : IsClique T) {x y : Vec (k + a)} (hx : x ∈ T)
    (hy : y ∈ T) (hxy : pos x ≠ pos y) : cnt T x + cnt T y = T.card := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext z
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro hz
      rcases hT.pos_two hx hy hz hxy with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  · rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_filter] at hz hz'
    exact hxy (hz.2.symm.trans hz'.2)

lemma choose_cnt_eq (hd : 1 ≤ d) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a)
    {x y : Vec (k + a)} (hx : x ∈ T) (hy : y ∈ T) :
    Nat.choose (d - 1) (cnt T x - 1) = Nat.choose (d - 1) (cnt T y - 1) := by
  rw [mem_tops] at hT
  by_cases hxy : pos x = pos y
  · unfold cnt; rw [hxy]
  · have h := cnt_add_cnt hT.2 hx hy hxy
    rw [hT.1] at h
    have h1 := cnt_pos (T := T) hx
    have h2 := cnt_pos (T := T) hy
    rw [← Nat.choose_symm (by omega : cnt T x - 1 ≤ d - 1)]
    congr 1; omega

lemma weight_single {T : Finset (Vec (k + a))} (h : ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) :
    weight d k a T = ((d : ℚ) - 1) * k := by
  unfold weight; rw [if_pos h]

lemma weight_split (hd : 1 ≤ d) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a)
    (h : ¬ ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) {x : Vec (k + a)} (hx : x ∈ T) :
    weight d k a T = 1 / (Nat.choose (d - 1) (cnt T x - 1) : ℚ) := by
  unfold weight
  rw [if_neg h]
  have hcard := (mem_tops.1 hT).1
  have : ∀ y ∈ T, (1 : ℚ) / (Nat.choose (d - 1) ((T.filter fun z => pos z = pos y).card - 1) : ℚ) =
      1 / (Nat.choose (d - 1) (cnt T x - 1) : ℚ) := by
    intro y hy
    have := choose_cnt_eq hd hT hy hx
    unfold cnt at this
    rw [this]; rfl
  rw [Finset.sum_congr rfl this, Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  field_simp

lemma choose_pos_of_mem (hd : 1 ≤ d) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a)
    (h : ¬ ∀ x ∈ T, ∀ y ∈ T, pos x = pos y) {x : Vec (k + a)} (hx : x ∈ T) :
    0 < Nat.choose (d - 1) (cnt T x - 1) := by
  apply Nat.choose_pos
  push Not at h
  obtain ⟨y, hy, z, hz, hyz⟩ := h
  have hT' := mem_tops.1 hT
  -- `x` has a point of `T` in another fibre
  obtain ⟨w, hw, hxw⟩ : ∃ w ∈ T, pos x ≠ pos w := by
    by_cases h1 : pos x = pos y
    · exact ⟨z, hz, h1 ▸ hyz⟩
    · exact ⟨y, hy, h1⟩
  have := cnt_add_cnt hT'.2 hx hw hxw
  have := cnt_pos (T := T) hw
  omega

lemma weight_pos (hd : 2 ≤ d) (hk : 1 ≤ k) {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a) :
    0 < weight d k a T := by
  by_cases h : ∀ x ∈ T, ∀ y ∈ T, pos x = pos y
  · rw [weight_single h]
    have : (2 : ℚ) ≤ d := by exact_mod_cast hd
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    nlinarith
  · have hne : T.Nonempty := by
      rw [← Finset.card_pos, (mem_tops.1 hT).1]; omega
    obtain ⟨x, hx⟩ := hne
    rw [weight_split (by omega) hT h hx]
    have := choose_pos_of_mem (by omega) hT h hx
    positivity

/-! ### Translation invariance -/

lemma image_add_injective (g : Vec (k + a)) : Function.Injective fun x : Vec (k + a) => x + g :=
  add_left_injective g

lemma clique_image_add {T : Finset (Vec (k + a))} (hT : IsClique T) (g : Vec (k + a)) :
    IsClique (T.image (· + g)) := by
  intro x hx y hy hxy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
  have : x' + g + (y' + g) = x' + y' := by
    rw [add_add_add_comm, vadd_self', add_zero]
  rw [this]
  exact hT x' hx' y' hy' (fun h => hxy (by rw [h]))

lemma tops_image_add {T : Finset (Vec (k + a))} (hT : T ∈ tops d k a) (g : Vec (k + a)) :
    T.image (· + g) ∈ tops d k a := by
  rw [mem_tops] at hT ⊢
  refine ⟨?_, clique_image_add hT.2 g⟩
  rw [Finset.card_image_of_injective _ (image_add_injective g), hT.1]

lemma filter_card_image_add (T : Finset (Vec (k + a))) (g x : Vec (k + a)) :
    ((T.image (· + g)).filter fun y => pos y = pos (x + g)).card =
      (T.filter fun y => pos y = pos x).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (image_add_injective g)]
  congr 1
  apply Finset.filter_congr
  intro y _
  simp only [Function.comp, pos_add]
  exact ⟨fun h => add_right_cancel h, fun h => by rw [h]⟩

lemma weight_image_add (T : Finset (Vec (k + a))) (g : Vec (k + a)) :
    weight d k a (T.image (· + g)) = weight d k a T := by
  unfold weight
  have hall : (∀ x ∈ T.image (· + g), ∀ y ∈ T.image (· + g), pos x = pos y) ↔
      ∀ x ∈ T, ∀ y ∈ T, pos x = pos y := by
    constructor
    · intro h x hx y hy
      have := h (x + g) (Finset.mem_image_of_mem _ hx) (y + g) (Finset.mem_image_of_mem _ hy)
      rw [pos_add, pos_add] at this
      exact add_right_cancel this
    · intro h x hx y hy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
      rw [pos_add, pos_add, h x' hx' y' hy']
  by_cases h : ∀ x ∈ T, ∀ y ∈ T, pos x = pos y
  · rw [if_pos (hall.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hall.1 h')), if_neg h]
    congr 1
    rw [Finset.sum_image (fun x _ y _ hxy => image_add_injective g hxy)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [filter_card_image_add]

lemma image_add_image_add (T : Finset (Vec (k + a))) (g : Vec (k + a)) :
    (T.image (· + g)).image (· + g) = T := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := T)]
  congr 1; funext x; simp [add_assoc, vadd_self']

/-! ### The normalized distribution -/

lemma total_pos (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : d + 1 ≤ 2 ^ a) :
    0 < ∑ τ ∈ tops d k a, weight d k a τ := by
  obtain ⟨τ, hτ, -⟩ := exists_top_of_clique (d := d) ha (σ := {0})
    (fun x hx y hy hxy => by simp at hx hy; rw [hx, hy] at hxy; exact absurd rfl hxy)
    (Finset.singleton_nonempty _) (by simp)
  exact Finset.sum_pos (fun τ hτ => weight_pos hd hk hτ) ⟨τ, hτ⟩

lemma mu_pos (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : d + 1 ≤ 2 ^ a) {T : Finset (Vec (k + a))}
    (hT : T ∈ tops d k a) : 0 < mu d k a T :=
  div_pos (weight_pos hd hk hT) (total_pos hd hk ha)

lemma mu_sum (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : d + 1 ≤ 2 ^ a) :
    ∑ τ ∈ tops d k a, mu d k a τ = 1 := by
  unfold mu
  rw [← Finset.sum_div, div_self (total_pos hd hk ha).ne']

lemma mu_image_add (T : Finset (Vec (k + a))) (g : Vec (k + a)) :
    mu d k a (T.image (· + g)) = mu d k a T := by
  unfold mu; rw [weight_image_add]

/-! ### Edges -/

lemma edges_eq (hd : 1 ≤ d) (ha : d + 1 ≤ 2 ^ a) :
    AbelianCayleyHDX.edges (tops d k a) =
      (Finset.univ ×ˢ gens k a).image (fun p : Vec (k + a) × Vec (k + a) => ({p.1, p.1 + p.2} : Finset _)) := by
  ext e
  simp only [AbelianCayleyHDX.edges, Finset.mem_biUnion, Finset.mem_powersetCard,
    Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨τ, hτ, hsub, hcard⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
    have hc := (mem_tops.1 hτ).2
    refine ⟨x, x + y, hc x (hsub (by simp)) y (hsub (by simp)) hxy, ?_⟩
    rw [← add_assoc, vadd_self', zero_add]
  · rintro ⟨x, s, hs, rfl⟩
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; exact (mem_gens.1 hs).1 rfl
    have hxs : x ≠ x + s := by
      intro h; apply hs0
      have := congrArg (x + ·) h; simpa [← add_assoc, vadd_self'] using this.symm
    have hcl : IsClique ({x, x + s} : Finset (Vec (k + a))) := by
      intro y hy z hz hyz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
      have e1 : x + (x + s) = s := by rw [← add_assoc, vadd_self', zero_add]
      have e2 : x + s + x = s := by
        ext i; simp only [Pi.add_apply]; grind
      rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
      · exact absurd rfl hyz
      · rw [e1]; exact hs
      · rw [e2]; exact hs
      · exact absurd rfl hyz
    obtain ⟨τ, hτ, hsub⟩ := exists_top_of_clique ha hcl (by simp)
      (by rw [Finset.card_pair hxs]; omega)
    exact ⟨τ, hτ, hsub, Finset.card_pair hxs⟩

/-! ### Edge masses depend only on the generator -/

lemma faceMass_translate (σ : Finset (Vec (k + a))) (g : Vec (k + a)) :
    faceMass (tops d k a) (mu d k a) (σ.image (· + g)) = faceMass (tops d k a) (mu d k a) σ := by
  unfold faceMass
  apply Finset.sum_nbij' (fun τ => τ.image (· + g)) (fun τ => τ.image (· + g))
  · intro τ hτ
    simp only [Finset.mem_filter] at hτ ⊢
    refine ⟨tops_image_add hτ.1 g, ?_⟩
    have := Finset.image_subset_image (f := (· + g)) hτ.2
    rwa [image_add_image_add] at this
  · intro τ hτ
    simp only [Finset.mem_filter] at hτ ⊢
    exact ⟨tops_image_add hτ.1 g, Finset.image_subset_image hτ.2⟩
  · intro τ _; exact image_add_image_add τ g
  · intro τ _; exact image_add_image_add τ g
  · intro τ _
    exact (mu_image_add τ g).symm

lemma faceMass_edge (s x y : Vec (k + a)) :
    faceMass (tops d k a) (mu d k a) {x, x + s} = faceMass (tops d k a) (mu d k a) {y, y + s} := by
  rw [← faceMass_translate {y, y + s} (x + y)]
  congr 1
  simp only [Finset.image_insert, Finset.image_singleton]
  congr 1
  · rw [add_comm x y, ← add_assoc, vadd_self', zero_add]
  · congr 1
    rw [add_comm x y]
    ext i; simp only [Pi.add_apply]; grind

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset

variable {d k a : ℕ}

lemma isClique_of_face {σ : Finset (Vec (k + a))} (hσ : IsFace (tops d k a) σ) : IsClique σ := by
  obtain ⟨τ, hτ, hsub⟩ := hσ
  exact (mem_tops.1 hτ).2.subset hsub

lemma card_le_of_face {σ : Finset (Vec (k + a))} (hσ : IsFace (tops d k a) σ) :
    σ.card ≤ d + 1 := by
  obtain ⟨τ, hτ, hsub⟩ := hσ
  have := Finset.card_le_card hsub
  rw [(mem_tops.1 hτ).1] at this; exact this

/-- Containment in a top face is the clique condition, for small sets. -/
lemma sub_top_iff (ha : d + 1 ≤ 2 ^ a) {T : Finset (Vec (k + a))} (hne : T.Nonempty)
    (hT : T.card ≤ d + 1) : (∃ τ ∈ tops d k a, T ⊆ τ) ↔ IsClique T := by
  constructor
  · rintro ⟨τ, hτ, hsub⟩; exact (mem_tops.1 hτ).2.subset hsub
  · intro h; exact exists_top_of_clique ha h hne hT

lemma mem_linkVerts (ha : d + 1 ≤ 2 ^ a) {σ : Finset (Vec (k + a))} (hσ : σ.card ≤ d)
    {x : Vec (k + a)} :
    x ∈ wLinkVerts (tops d k a) σ ↔ x ∉ σ ∧ IsClique (insert x σ) := by
  simp only [wLinkVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [sub_top_iff ha (Finset.insert_nonempty _ _)]
  exact le_trans (Finset.card_insert_le _ _) (by omega)

/-- Adding one point to a clique. -/
lemma isClique_insert {σ : Finset (Vec (k + a))} (hσ : IsClique σ) {x : Vec (k + a)} :
    IsClique (insert x σ) ↔ ∀ y ∈ σ, y ≠ x → x + y ∈ gens k a := by
  constructor
  · intro h y hy hyx
    exact h x (Finset.mem_insert_self _ _) y (Finset.mem_insert_of_mem hy) (Ne.symm hyx)
  · intro h y hy z hz hyz
    rw [Finset.mem_insert] at hy hz
    rcases hy with rfl | hy <;> rcases hz with rfl | hz
    · exact absurd rfl hyz
    · exact h z hz (Ne.symm hyz)
    · rw [add_comm y z]; exact h y hy hyz
    · exact hσ y hy z hz hyz

/-! ### Connectivity of the links -/

/-- A fresh label avoiding a small set. -/
lemma exists_fresh (ha : d + 3 ≤ 2 ^ a) (s : Finset (Vec a)) (hs : s.card ≤ d + 2) :
    ∃ ℓ : Vec a, ℓ ∉ s := by
  by_contra h; push Not at h
  have : (Finset.univ : Finset (Vec a)) ⊆ s := fun x _ => h x
  have := Finset.card_le_card this
  simp only [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at this
  omega

lemma linkConnected_nonempty (ha : d + 3 ≤ 2 ^ a) {σ : Finset (Vec (k + a))}
    (hσf : IsFace (tops d k a) σ) (hne : σ.Nonempty) (hσ : σ.card ≤ d - 1) :
    LinkConnected (tops d k a) σ := by
  have ha' : d + 1 ≤ 2 ^ a := by omega
  have hcl := isClique_of_face hσf
  obtain ⟨x0, hx0⟩ := hne
  have hσd : σ.card ≤ d := by omega
  have hσpos : 1 ≤ σ.card := Finset.card_pos.2 ⟨x0, hx0⟩
  -- hub vertices: label fresh, position `pos x0`
  have hub_mem : ∀ ℓ : Vec a, ℓ ∉ σ.image lab →
      emb (pos x0) ℓ ∈ wLinkVerts (tops d k a) σ := by
    intro ℓ hℓ
    rw [mem_linkVerts ha' hσd]
    have hnot : emb (pos x0) ℓ ∉ σ := fun h => hℓ (Finset.mem_image.2 ⟨_, h, by simp⟩)
    refine ⟨hnot, (isClique_insert hcl).2 (fun y hy _ => ?_)⟩
    rw [add_mem_gens]
    refine ⟨fun h => hℓ (Finset.mem_image.2 ⟨y, hy, by simpa using h.symm⟩), ?_⟩
    simpa using hcl.posAdj hx0 hy
  -- every link vertex is adjacent to a hub
  have to_hub : ∀ u ∈ wLinkVerts (tops d k a) σ, ∀ ℓ : Vec a, ℓ ∉ σ.image lab → ℓ ≠ lab u →
      u ≠ emb (pos x0) ℓ ∧ ∃ τ ∈ tops d k a, insert u (insert (emb (pos x0) ℓ) σ) ⊆ τ := by
    intro u hu ℓ hℓ hℓu
    rw [mem_linkVerts ha' hσd] at hu
    have hz := hub_mem ℓ hℓ
    rw [mem_linkVerts ha' hσd] at hz
    have hne' : u ≠ emb (pos x0) ℓ := fun h => hℓu (by rw [h]; simp)
    refine ⟨hne', ?_⟩
    rw [sub_top_iff ha' (Finset.insert_nonempty _ _)]
    · rw [isClique_insert hz.2]
      intro y hy hyu
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rw [add_mem_gens]
        refine ⟨fun h => hℓu (by simpa using h.symm), ?_⟩
        have := hu.2.posAdj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hx0)
        simpa using this
      · exact hu.2 u (Finset.mem_insert_self _ _) y (Finset.mem_insert_of_mem hy) (Ne.symm hyu)
    · calc (insert u (insert (emb (pos x0) ℓ) σ)).card ≤ σ.card + 2 := by
            have := Finset.card_insert_le u (insert (emb (pos x0) ℓ) σ)
            have := Finset.card_insert_le (emb (pos x0) ℓ) σ
            omega
        _ ≤ d + 1 := by omega
  -- two hubs are adjacent
  have hub_hub : ∀ ℓ ℓ' : Vec a, ℓ ∉ σ.image lab → ℓ' ∉ σ.image lab → ℓ ≠ ℓ' →
      emb (pos x0) ℓ ≠ emb (pos x0) ℓ' ∧
        ∃ τ ∈ tops d k a, insert (emb (pos x0) ℓ) (insert (emb (pos x0) ℓ') σ) ⊆ τ := by
    intro ℓ ℓ' hℓ hℓ' hll
    have := to_hub (emb (pos x0) ℓ) (hub_mem ℓ hℓ) ℓ' hℓ' (by simpa using Ne.symm hll)
    exact this
  intro u hu v hv
  -- choose fresh labels
  obtain ⟨ℓu, hℓu⟩ := exists_fresh ha (insert (lab u) (σ.image lab))
    (by have := Finset.card_insert_le (lab u) (σ.image lab)
        have := Finset.card_image_le (s := σ) (f := lab); omega)
  obtain ⟨ℓv, hℓv⟩ := exists_fresh ha (insert (lab v) (σ.image lab))
    (by have := Finset.card_insert_le (lab v) (σ.image lab)
        have := Finset.card_image_le (s := σ) (f := lab); omega)
  rw [Finset.mem_insert, not_or] at hℓu hℓv
  have e1 := to_hub u hu ℓu hℓu.2 hℓu.1
  have e2 := to_hub v hv ℓv hℓv.2 hℓv.1
  have step : ∀ x y, x ∈ wLinkVerts (tops d k a) σ → y ∈ wLinkVerts (tops d k a) σ →
      x ≠ y → (∃ τ ∈ tops d k a, insert x (insert y σ) ⊆ τ) →
      Relation.ReflTransGen (fun p q => p ∈ wLinkVerts (tops d k a) σ ∧
        q ∈ wLinkVerts (tops d k a) σ ∧ p ≠ q ∧ ∃ τ ∈ tops d k a, insert p (insert q σ) ⊆ τ) x y :=
    fun x y hx hy hxy h => Relation.ReflTransGen.single ⟨hx, hy, hxy, h⟩
  have symm_step : ∀ x y, (∃ τ ∈ tops d k a, insert x (insert y σ) ⊆ τ) →
      ∃ τ ∈ tops d k a, insert y (insert x σ) ⊆ τ := by
    rintro x y ⟨τ, hτ, hs⟩; exact ⟨τ, hτ, by rw [Finset.insert_comm]; exact hs⟩
  have hu' := hub_mem ℓu hℓu.2
  have hv' := hub_mem ℓv hℓv.2
  refine (step _ _ hu hu' e1.1 e1.2).trans ?_
  refine Relation.ReflTransGen.trans ?_ (step _ _ hv' hv (Ne.symm e2.1) (symm_step _ _ e2.2))
  by_cases hl : ℓu = ℓv
  · rw [hl]
  · have := hub_hub ℓu ℓv hℓu.2 hℓv.2 hl
    exact step _ _ hu' hv' this.1 this.2

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset AbelianCayleyHDX.Tensor AbelianCayleyHDX.Pos

/-- Transfer of two-sided expansion along an injective parametrization of the vertex set. -/
lemma tse_of_embedding {X α : Type*} [Fintype X] [DecidableEq α] (E : X → α)
    (hE : Function.Injective E) (U : Finset α) (hU : U = Finset.univ.image E)
    (w : α → α → ℝ) (A : X → X → ℝ) (hwA : ∀ p q, w (E p) (E q) = A p q) (hne : Nonempty X)
    (hsym : ∀ p q, A p q = A q p) (hnn : ∀ p q, 0 ≤ A p q) (hdiag : ∀ p, A p p = 0)
    (hdeg : ∀ p, 0 < ∑ q, A p q)
    (hconn : ∀ p q, Relation.ReflTransGen (fun x y => 0 < A x y) p q) (lam : ℝ) (hlam : 0 ≤ lam)
    (hspec : ∀ f : X → ℝ, ∑ p, (∑ q, A p q) * f p = 0 →
      ∑ p, (∑ q, A p q) * ((∑ q, A p q * f q) / (∑ q, A p q)) ^ 2 ≤
        lam ^ 2 * ∑ p, (∑ q, A p q) * f p ^ 2) :
    AbelianCayleyHDX.IsTwoSidedSpectralExpander U w lam := by
  subst hU
  have hinj : ∀ x ∈ (Finset.univ : Finset X), ∀ y ∈ (Finset.univ : Finset X), E x = E y → x = y :=
    fun x _ y _ h => hE h
  have hsum : ∀ F : α → ℝ, ∑ x ∈ Finset.univ.image E, F x = ∑ p, F (E p) := fun F =>
    Finset.sum_image hinj
  refine ⟨Finset.univ_nonempty.image _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩; rw [hwA, hwA]; exact hsym p q
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩; rw [hwA]; exact hnn p q
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨p, rfl⟩; rw [hwA]; exact hdiag p
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨p, rfl⟩; rw [hsum]; simp only [hwA]; exact hdeg p
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    refine Relation.ReflTransGen.lift E ?_ p q (hconn p q)
    intro x y hxy
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩, by rw [hwA]; exact hxy⟩
  · intro f hf
    rw [hsum] at hf
    simp only [hsum, hwA] at hf ⊢
    have key := hspec (f ∘ E) (by simpa [Function.comp] using hf)
    simp only [Function.comp] at key
    calc Real.sqrt (∑ p, (∑ q, A p q) * ((∑ q, A p q * f (E q)) / (∑ q, A p q)) ^ 2)
        ≤ Real.sqrt (lam ^ 2 * ∑ p, (∑ q, A p q) * f (E p) ^ 2) := Real.sqrt_le_sqrt key
      _ = lam * Real.sqrt (∑ p, (∑ q, A p q) * f (E p) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam]

/-- The binomial identity behind the split links: the second eigenvalue is exactly `1/d`. -/
lemma binom_identity (d j : ℕ) (hj1 : 1 ≤ j) (hj2 : j + 2 ≤ d) :
    ((1 / (Nat.choose (d - 1) (j + 1) : ℝ)) * (1 / (Nat.choose (d - 1) (j - 1) : ℝ)) -
        (1 / (Nat.choose (d - 1) j : ℝ)) ^ 2) /
      ((1 / (Nat.choose (d - 1) (j + 1) : ℝ) + 1 / (Nat.choose (d - 1) j : ℝ)) *
        (1 / (Nat.choose (d - 1) j : ℝ) + 1 / (Nat.choose (d - 1) (j - 1) : ℝ))) =
      1 / (d : ℝ) := by
  -- the two ratio identities
  have e1 : (Nat.choose (d - 1) (j + 1) : ℝ) * (j + 1) = (Nat.choose (d - 1) j : ℝ) * ((d : ℝ) - 1 - j) := by
    have := Nat.choose_succ_right_eq (d - 1) j
    have h' : ((Nat.choose (d - 1) (j + 1) * (j + 1) : ℕ) : ℝ) =
        ((Nat.choose (d - 1) j * (d - 1 - j) : ℕ) : ℝ) := by rw [this]
    push_cast at h'
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at h'
    push_cast at h'; linarith
  have e2 : (Nat.choose (d - 1) j : ℝ) * j = (Nat.choose (d - 1) (j - 1) : ℝ) * ((d : ℝ) - j) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have := Nat.choose_succ_right_eq (d - 1) i
    have h' : ((Nat.choose (d - 1) (i + 1) * (i + 1) : ℕ) : ℝ) =
        ((Nat.choose (d - 1) i * (d - 1 - i) : ℕ) : ℝ) := by rw [this]
    push_cast at h'
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at h'
    push_cast at h'
    simp only [Nat.add_sub_cancel]
    push_cast; linarith
  have hB : (0 : ℝ) < Nat.choose (d - 1) j := by exact_mod_cast Nat.choose_pos (by omega)
  have hA : (0 : ℝ) < Nat.choose (d - 1) (j + 1) := by exact_mod_cast Nat.choose_pos (by omega)
  have hC : (0 : ℝ) < Nat.choose (d - 1) (j - 1) := by exact_mod_cast Nat.choose_pos (by omega)
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hdj : (j : ℝ) + 2 ≤ d := by exact_mod_cast hj2
  set A := (Nat.choose (d - 1) (j + 1) : ℝ)
  set B := (Nat.choose (d - 1) j : ℝ)
  set C := (Nat.choose (d - 1) (j - 1) : ℝ)
  have hA' : A = B * ((d : ℝ) - 1 - j) / (j + 1) := by
    field_simp; linarith
  have hC' : C = B * j / ((d : ℝ) - j) := by
    have : (d : ℝ) - j ≠ 0 := by linarith
    field_simp; linarith
  rw [hA', hC']
  have h1 : (d : ℝ) - 1 - j ≠ 0 := by linarith
  have h2 : (d : ℝ) - j ≠ 0 := by linarith
  have h3 : (j : ℝ) + 1 ≠ 0 := by linarith
  have h4 : (j : ℝ) ≠ 0 := by linarith
  have h5 : (d : ℝ) ≠ 0 := by linarith
  field_simp
  ring_nf
  field_simp

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset AbelianCayleyHDX.Tensor AbelianCayleyHDX.Pos

variable {d k a : ℕ}

open Classical in
/-- For a codimension-two face, the link weight of two new vertices is the mass of the single
top face they span, if any. -/
lemma wLinkWeight_eq (hd : 1 ≤ d) {σ : Finset (Vec (k + a))} (hσc : σ.card = d - 1)
    {u v : Vec (k + a)} (hu : u ∉ σ) (hv : v ∉ σ) (huv : u ≠ v) :
    wLinkWeight (tops d k a) (mu d k a) σ u v =
      if IsClique (insert u (insert v σ)) then ((mu d k a (insert u (insert v σ)) : ℚ) : ℝ)
      else 0 := by
  classical
  unfold wLinkWeight
  rw [if_neg huv]
  have hcard : (insert u (insert v σ)).card = d + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [huv, hu]), Finset.card_insert_of_notMem hv]
    omega
  by_cases hcl : IsClique (insert u (insert v σ))
  · rw [if_pos hcl]
    have hT0 : insert u (insert v σ) ∈ tops d k a := mem_tops.2 ⟨hcard, hcl⟩
    have : (tops d k a).filter (fun τ => insert u (insert v σ) ⊆ τ) = {insert u (insert v σ)} := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hτ, hsub⟩
        symm
        apply Finset.eq_of_subset_of_card_le hsub
        rw [(mem_tops.1 hτ).1, hcard]
      · rintro rfl; exact ⟨hT0, subset_refl _⟩
    rw [this, Finset.sum_singleton]
  · rw [if_neg hcl]
    apply Finset.sum_eq_zero
    intro τ hτ
    exfalso
    simp only [Finset.mem_filter] at hτ
    exact hcl ((mem_tops.1 hτ.1).2.subset hτ.2)

lemma cnt_insert2 {σ : Finset (Vec (k + a))} {u v x : Vec (k + a)} (hu : u ∉ σ) (hv : v ∉ σ)
    (huv : u ≠ v) :
    cnt (insert u (insert v σ)) x = cnt σ x + (if pos u = pos x then 1 else 0) +
      (if pos v = pos x then 1 else 0) := by
  unfold cnt
  rw [Finset.filter_insert, Finset.filter_insert]
  have hv' : v ∉ σ.filter (fun y => pos y = pos x) := fun h => hv (Finset.mem_filter.1 h).1
  have hu' : ∀ s : Finset (Vec (k + a)), s ⊆ insert v σ → u ∉ s := fun s hs h => by
    have := hs h; rw [Finset.mem_insert] at this
    rcases this with h1 | h1
    · exact huv h1
    · exact hu h1
  split_ifs with h1 h2 h2
  · rw [Finset.card_insert_of_notMem (hu' _ (by
        intro y hy; rw [Finset.mem_insert] at hy ⊢
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (Finset.mem_filter.1 hy).1)),
      Finset.card_insert_of_notMem hv']
  · rw [Finset.card_insert_of_notMem (hu' _ (fun y hy => Finset.mem_insert_of_mem
      (Finset.mem_filter.1 hy).1))]
  · rw [Finset.card_insert_of_notMem hv']
  · simp

/-- The labels of a clique are distinct. -/
lemma card_image_lab {σ : Finset (Vec (k + a))} (hσ : IsClique σ) :
    (σ.image lab).card = σ.card :=
  Finset.card_image_of_injOn (fun x hx y hy h => hσ.lab_inj hx hy h)

/-- The fresh labels. -/
abbrev Fresh (σ : Finset (Vec (k + a))) := {ℓ : Vec a // ℓ ∉ σ.image lab}

lemma card_fresh {σ : Finset (Vec (k + a))} (hσ : IsClique σ) :
    Fintype.card (Fresh σ) = 2 ^ a - σ.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe, card_image_lab hσ]
  simp

/-- Connectivity of `positions × labels` through a hub position. -/
lemma prod_conn {W L : Type*} [Fintype L] [DecidableEq L] (aW : W → W → ℝ) (w0 : W)
    (hhub : ∀ w, 0 < aW w w0 ∧ 0 < aW w0 w) (hL : 3 ≤ Fintype.card L) (p q : W × L) :
    Relation.ReflTransGen (fun x y => 0 < prodW aW x y) p q := by
  have hpos : ∀ x y : W × L, x.2 ≠ y.2 → 0 < aW x.1 y.1 → 0 < prodW aW x y := by
    intro x y hxy h; simp [prodW, hxy, h]
  -- choose labels different from `p.2`, `q.2`
  obtain ⟨l1, hl1⟩ : ∃ l, l ≠ p.2 ∧ l ≠ q.2 := by
    by_contra h; push Not at h
    have : (Finset.univ : Finset L) ⊆ {p.2, q.2} := by
      intro l _; by_cases hl : l = p.2
      · simp [hl]
      · simp [h l hl]
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    have := Finset.card_le_two (a := p.2) (b := q.2)
    omega
  have s1 : Relation.ReflTransGen (fun x y => 0 < prodW aW x y) p (w0, l1) :=
    Relation.ReflTransGen.single (hpos p (w0, l1) (Ne.symm hl1.1) (hhub p.1).1)
  have s2 : Relation.ReflTransGen (fun x y => 0 < prodW aW x y) (w0, l1) q :=
    Relation.ReflTransGen.single (hpos (w0, l1) q hl1.2 (hhub q.1).2)
  exact s1.trans s2

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset AbelianCayleyHDX.Tensor AbelianCayleyHDX.Pos

variable {d k a : ℕ}

/-- Positions around a fibre `c`: `none ↦ c`, `some i ↦ c + eᵢ`. -/
def posA (c : Vec k) : Option (Fin k) → Vec k
  | none => c
  | some i => c + Pi.single i 1

lemma posA_inj (c : Vec k) : Function.Injective (posA c) := by
  have hc : ∀ i : Fin k, c ≠ c + Pi.single i 1 := by
    intro i h
    apply single_ne_zero' i
    have := congrArg (c + ·) h
    simpa [← add_assoc, vadd_self'] using this.symm
  intro w w' h
  cases w <;> cases w' <;> simp only [posA] at h
  · rfl
  · exact absurd h (hc _)
  · exact absurd h.symm (hc _)
  · rw [single_inj' (add_left_cancel h)]

lemma posAdj_posA_c (c : Vec k) (w : Option (Fin k)) : PosAdj (posA c w) c := by
  cases w with
  | none => left; exact vadd_self' c
  | some i =>
    right; refine ⟨i, ?_⟩
    simp only [posA]
    rw [add_comm (c + _) c, ← add_assoc, vadd_self', zero_add]

lemma posAdj_posA_iff (c : Vec k) (w w' : Option (Fin k)) :
    PosAdj (posA c w) (posA c w') ↔ ¬ ∃ i j : Fin k, i ≠ j ∧ w = some i ∧ w' = some j := by
  constructor
  · rintro h ⟨i, j, hij, rfl, rfl⟩
    simp only [posA] at h
    have e : c + Pi.single i 1 + (c + Pi.single j 1) = (Pi.single i 1 + Pi.single j 1 : Vec k) := by
      rw [add_add_add_comm, vadd_self', zero_add]
    rcases h with h | ⟨l, hl⟩
    · rw [e] at h; exact (single_add_single_ne hij).1 h
    · rw [e] at hl; exact (single_add_single_ne hij).2 l hl
  · intro h
    cases w with
    | none => exact posAdj_symm (posAdj_posA_c c w')
    | some i =>
      cases w' with
      | none => exact posAdj_posA_c c (some i)
      | some j =>
        by_cases hij : i = j
        · subst hij; left; exact vadd_self' _
        · exact absurd ⟨i, j, hij, rfl, rfl⟩ h

lemma choose_pred_self (n : ℕ) (hn : 1 ≤ n) : Nat.choose n (n - 1) = n := by
  rw [Nat.choose_symm (by omega)]; simp [show n - (n - 1) = 1 by omega]

/-- **Codimension-two links inside one fibre.** -/
theorem codim2_single (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : 2 * d + 3 ≤ 2 ^ a)
    {σ : Finset (Vec (k + a))} (hσf : IsFace (tops d k a) σ) (hσc : σ.card = d - 1)
    {x0 : Vec (k + a)} (hx0 : x0 ∈ σ) (hc : ∀ x ∈ σ, pos x = pos x0) :
    AbelianCayleyHDX.IsTwoSidedSpectralExpander (wLinkVerts (tops d k a) σ)
      (wLinkWeight (tops d k a) (mu d k a) σ) (1 / (d : ℝ)) := by
  classical
  set c := pos x0 with hcdef
  have hcl := isClique_of_face hσf
  have ha' : d + 1 ≤ 2 ^ a := by omega
  let E : Option (Fin k) × Fresh σ → Vec (k + a) := fun p => emb (posA c p.1) p.2.1
  have hEpos : ∀ p, pos (E p) = posA c p.1 := fun p => pos_emb _ _
  have hElab : ∀ p, lab (E p) = p.2.1 := fun p => lab_emb _ _
  have hE : Function.Injective E := by
    intro p q h
    have h1 := congrArg pos h; have h2 := congrArg lab h
    rw [hEpos, hEpos] at h1; rw [hElab, hElab] at h2
    exact Prod.ext (posA_inj c h1) (Subtype.ext h2)
  have hnot : ∀ p, E p ∉ σ := by
    intro p hp; exact p.2.2 (Finset.mem_image.2 ⟨_, hp, hElab p⟩)
  have hcompat : ∀ p, ∀ y ∈ σ, E p + y ∈ gens k a := by
    intro p y hy
    rw [add_mem_gens, hElab, hEpos, hc y hy]
    exact ⟨fun h => p.2.2 (Finset.mem_image.2 ⟨y, hy, h.symm⟩), posAdj_posA_c c p.1⟩
  have hU : wLinkVerts (tops d k a) σ = Finset.univ.image E := by
    ext x
    rw [mem_linkVerts ha' (by omega : σ.card ≤ d)]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxσ, hcl'⟩
      have h1 := (isClique_insert hcl).1 hcl' x0 hx0 (fun h => hxσ (h ▸ hx0))
      rw [add_mem_gens] at h1
      have hfresh : lab x ∉ σ.image lab := by
        intro hmem
        obtain ⟨y, hy, hyl⟩ := Finset.mem_image.1 hmem
        have := (isClique_insert hcl).1 hcl' y hy (fun h => hxσ (h ▸ hy))
        exact (add_mem_gens.1 this).1 hyl.symm
      obtain ⟨w, hw⟩ : ∃ w, posA c w = pos x := by
        rcases h1.2 with h | ⟨i, hi⟩
        · exact ⟨none, ((vec_eq_iff_add_eq_zero _ _).2 h).symm⟩
        · refine ⟨some i, ?_⟩
          simp only [posA]
          rw [← hi, add_comm (pos x) c, ← add_assoc, vadd_self', zero_add]
      exact ⟨(w, ⟨lab x, hfresh⟩), ext_pl (by rw [hEpos, hw]) (by rw [hElab])⟩
    · rintro ⟨p, rfl⟩
      exact ⟨hnot p, (isClique_insert hcl).2 (fun y hy _ => hcompat p y hy)⟩
  -- the normalization
  set Z : ℚ := ∑ τ ∈ tops d k a, weight d k a τ with hZdef
  have hZ : 0 < Z := total_pos hd hk ha'
  set β : ℝ := 1 / (Z : ℝ) with hβdef
  have hβ : 0 < β := by rw [hβdef]; exact div_pos one_pos (by exact_mod_cast hZ)
  have hmu : ∀ T, ((mu d k a T : ℚ) : ℝ) = (weight d k a T : ℝ) * β := by
    intro T; unfold mu; rw [← hZdef, hβdef]; push_cast; ring
  have hcntσ : cnt σ x0 = d - 1 := by
    rw [← hσc]; unfold cnt; congr 1
    exact Finset.filter_true_of_mem (fun y hy => hc y hy)
  have hd1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hci : ∀ i : Fin k, posA c (some i) ≠ c := by
    intro i h
    apply single_ne_zero' i
    have := congrArg (c + ·) h
    simpa [posA, ← add_assoc, vadd_self'] using this
  have hc0 : posA c none = pos x0 := rfl
  have hcs : ∀ i : Fin k, posA c (some i) ≠ pos x0 := hci
  -- the link weights
  have hwA : ∀ p q, wLinkWeight (tops d k a) (mu d k a) σ (E p) (E q) =
      prodW (starW d k β) p q := by
    intro p q
    by_cases hpq : p = q
    · subst hpq; unfold wLinkWeight; rw [if_pos rfl]; simp [prodW]
    have hne : E p ≠ E q := fun h => hpq (hE h)
    rw [wLinkWeight_eq (by omega) hσc (hnot p) (hnot q) hne]
    have hclq := (isClique_insert hcl).2 (fun y hy _ => hcompat q y hy)
    have hcliq : IsClique (insert (E p) (insert (E q) σ)) ↔
        (p.2 ≠ q.2 ∧ PosAdj (posA c p.1) (posA c q.1)) := by
      rw [isClique_insert hclq]
      constructor
      · intro h
        have := h (E q) (Finset.mem_insert_self _ _) (Ne.symm hne)
        rw [add_mem_gens, hElab, hElab, hEpos, hEpos] at this
        exact ⟨fun h' => this.1 (by rw [h']), this.2⟩
      · rintro ⟨hl, hpa⟩ y hy hyp
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · rw [add_mem_gens, hElab, hElab, hEpos, hEpos]
          exact ⟨fun h' => hl (Subtype.ext h'), hpa⟩
        · exact hcompat p y hy
    have hcard : (insert (E p) (insert (E q) σ)).card = d + 1 := by
      rw [Finset.card_insert_of_notMem (by simp [hne, hnot p]),
        Finset.card_insert_of_notMem (hnot q)]
      omega
    have hx0T : x0 ∈ insert (E p) (insert (E q) σ) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx0)
    have hcnt := cnt_insert2 (x := x0) (hnot p) (hnot q) hne
    rw [hcntσ, hEpos, hEpos] at hcnt
    by_cases hl : p.2 = q.2
    · rw [if_neg (fun h => (hcliq.1 h).1 hl)]
      simp [prodW, hl]
    have hlab : (if p.2 = q.2 then (0 : ℝ) else 1) = 1 := if_neg hl
    simp only [prodW, hlab, mul_one]
    obtain ⟨w1, l1⟩ := p
    obtain ⟨w2, l2⟩ := q
    simp only at hl hcliq hcnt hlab ⊢
    cases w1 with
    | none =>
      cases w2 with
      | none =>
        have hcl0 : IsClique (insert (E (none, l1)) (insert (E (none, l2)) σ)) :=
          hcliq.2 ⟨hl, (posAdj_posA_iff c _ _).2 (by rintro ⟨i, j, -, h, -⟩; cases h)⟩
        rw [if_pos hcl0, hmu]
        have hall : ∀ x ∈ insert (E (none, l1)) (insert (E (none, l2)) σ),
            ∀ y ∈ insert (E (none, l1)) (insert (E (none, l2)) σ), pos x = pos y := by
          have : ∀ x ∈ insert (E (none, l1)) (insert (E (none, l2)) σ), pos x = c := by
            intro x hx
            simp only [Finset.mem_insert] at hx
            rcases hx with rfl | rfl | hx
            · rw [hEpos]; rfl
            · rw [hEpos]; rfl
            · exact hc x hx
          intro x hx y hy; rw [this x hx, this y hy]
        rw [weight_single hall]
        simp only [starW]; push_cast; ring
      | some i =>
        have hcl0 : IsClique (insert (E (none, l1)) (insert (E (some i, l2)) σ)) :=
          hcliq.2 ⟨hl, (posAdj_posA_iff c _ _).2 (by rintro ⟨i, j, -, h, -⟩; cases h)⟩
        rw [if_pos hcl0, hmu]
        have hT : insert (E (none, l1)) (insert (E (some i, l2)) σ) ∈ tops d k a :=
          mem_tops.2 ⟨hcard, hcl0⟩
        have hnall : ¬ ∀ x ∈ insert (E (none, l1)) (insert (E (some i, l2)) σ),
            ∀ y ∈ insert (E (none, l1)) (insert (E (some i, l2)) σ), pos x = pos y := by
          intro h
          have := h _ (Finset.mem_insert_self _ _) _
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          rw [hEpos, hEpos] at this
          exact absurd (posA_inj c this) (by simp)
        rw [weight_split (by omega) hT hnall hx0T]
        rw [if_pos hc0, if_neg (hcs i)] at hcnt
        rw [hcnt, show d - 1 + 1 + 0 - 1 = d - 1 by omega, Nat.choose_self]
        simp only [starW]; push_cast; ring
    | some i =>
      cases w2 with
      | none =>
        have hcl0 : IsClique (insert (E (some i, l1)) (insert (E (none, l2)) σ)) :=
          hcliq.2 ⟨hl, (posAdj_posA_iff c _ _).2 (by rintro ⟨i, j, -, -, h⟩; cases h)⟩
        rw [if_pos hcl0, hmu]
        have hT : insert (E (some i, l1)) (insert (E (none, l2)) σ) ∈ tops d k a :=
          mem_tops.2 ⟨hcard, hcl0⟩
        have hnall : ¬ ∀ x ∈ insert (E (some i, l1)) (insert (E (none, l2)) σ),
            ∀ y ∈ insert (E (some i, l1)) (insert (E (none, l2)) σ), pos x = pos y := by
          intro h
          have := h _ (Finset.mem_insert_self _ _) _
            (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          rw [hEpos, hEpos] at this
          exact absurd (posA_inj c this) (by simp)
        rw [weight_split (by omega) hT hnall hx0T]
        rw [if_neg (hcs i), if_pos hc0] at hcnt
        rw [hcnt, show d - 1 + 0 + 1 - 1 = d - 1 by omega, Nat.choose_self]
        simp only [starW]; push_cast; ring
      | some j =>
        by_cases hij : i = j
        · subst hij
          have hcl0 : IsClique (insert (E (some i, l1)) (insert (E (some i, l2)) σ)) :=
            hcliq.2 ⟨hl, (posAdj_posA_iff c _ _).2 (by
              rintro ⟨i', j', hij', h1, h2⟩; cases h1; cases h2; exact hij' rfl)⟩
          rw [if_pos hcl0, hmu]
          have hT : insert (E (some i, l1)) (insert (E (some i, l2)) σ) ∈ tops d k a :=
            mem_tops.2 ⟨hcard, hcl0⟩
          have hnall : ¬ ∀ x ∈ insert (E (some i, l1)) (insert (E (some i, l2)) σ),
              ∀ y ∈ insert (E (some i, l1)) (insert (E (some i, l2)) σ), pos x = pos y := by
            intro h
            have := h _ (Finset.mem_insert_self _ _) _ hx0T
            rw [hEpos] at this
            exact hcs i this
          rw [weight_split (by omega) hT hnall hx0T]
          rw [if_neg (hcs i)] at hcnt
          rw [hcnt, show d - 1 + 0 + 0 - 1 = d - 1 - 1 by omega,
            show d - 1 - 1 = (d - 1) - 1 from rfl, choose_pred_self (d - 1) (by omega)]
          simp only [starW, if_true]
          have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
          push_cast [this]
          field_simp
        · rw [if_neg (fun h => (posAdj_posA_iff c _ _).1 (hcliq.1 h).2 ⟨i, j, hij, rfl, rfl⟩)]
          simp [starW, hij]
  -- assemble
  have hcardL : Fintype.card (Fresh σ) = 2 ^ a - (d - 1) := by rw [card_fresh hcl, hσc]
  have hL3 : 3 ≤ Fintype.card (Fresh σ) := by rw [hcardL]; omega
  have hLd : 1 / ((Fintype.card (Fresh σ) : ℝ) - 1) ≤ 1 / (d : ℝ) := by
    have : (d : ℝ) + 1 ≤ (Fintype.card (Fresh σ) : ℝ) := by
      rw [hcardL]
      have : d + 1 ≤ 2 ^ a - (d - 1) := by omega
      exact_mod_cast this
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hneX : Nonempty (Option (Fin k) × Fresh σ) := by
    have : 0 < Fintype.card (Fresh σ) := by omega
    obtain ⟨l⟩ := Fintype.card_pos_iff.1 this
    exact ⟨(none, l)⟩
  apply tse_of_embedding E hE _ hU _ (prodW (starW d k β)) hwA hneX
  · intro p q; simp only [prodW]; rw [starW_symm]; congr 1; simp [eq_comm]
  · intro p q; simp only [prodW]
    exact mul_nonneg (starW_nn d k hd β hβ.le _ _) (by split_ifs <;> norm_num)
  · intro p; simp [prodW]
  · intro p; rw [deg_prodW]
    have := starW_deg_pos d k hd hk β hβ p.1
    have : (2 : ℝ) ≤ Fintype.card (Fresh σ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card (Fresh σ))
    nlinarith
  · intro p q
    apply prod_conn _ none _ hL3
    intro w
    cases w with
    | none =>
      simp only [starW]
      have h1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) < k := by exact_mod_cast hk
      constructor <;> positivity
    | some i => simp only [starW]; exact ⟨hβ, hβ⟩
  · positivity
  · intro f hf
    exact tensor_bound (starW d k β) (starW_symm d k β) (starW_nn d k hd β hβ.le)
      (starW_deg_pos d k hd hk β hβ) _ (by positivity) (by omega) hLd
      (star_bound d k hd hk β hβ) f hf

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset AbelianCayleyHDX.Tensor AbelianCayleyHDX.Pos

variable {d k a : ℕ}

/-- **Codimension-two links split across a cube edge.** -/
theorem codim2_split (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : 2 * d + 3 ≤ 2 ^ a)
    {σ : Finset (Vec (k + a))} (hσf : IsFace (tops d k a) σ) (hσc : σ.card = d - 1)
    {x0 y0 : Vec (k + a)} (hx0 : x0 ∈ σ) (hy0 : y0 ∈ σ) (hxy : pos x0 ≠ pos y0) :
    AbelianCayleyHDX.IsTwoSidedSpectralExpander (wLinkVerts (tops d k a) σ)
      (wLinkWeight (tops d k a) (mu d k a) σ) (1 / (d : ℝ)) := by
  classical
  have hcl := isClique_of_face hσf
  have ha' : d + 1 ≤ 2 ^ a := by omega
  set c := pos x0 with hcdef
  set c' := pos y0 with hc'def
  let posB : Bool → Vec k := fun b => if b then c else c'
  have hposB_inj : Function.Injective posB := by
    intro b b' h; cases b <;> cases b' <;> simp_all [posB, eq_comm]
  have hadj : PosAdj c c' := hcl.posAdj hx0 hy0
  have hposσ : ∀ y ∈ σ, pos y = c ∨ pos y = c' := fun y hy => hcl.pos_two hx0 hy0 hy hxy
  have hposB_adj : ∀ (b : Bool) (y : Vec (k + a)), (pos y = c ∨ pos y = c') →
      PosAdj (posB b) (pos y) := by
    intro b y hy
    have hcc : PosAdj c c := Or.inl (vadd_self' c)
    have hc'c' : PosAdj c' c' := Or.inl (vadd_self' c')
    cases b <;> rcases hy with hy | hy <;> simp only [posB, hy, if_true] <;>
      first | exact hcc | exact hc'c' | exact hadj | exact posAdj_symm hadj | skip
    all_goals simp_all
  let E : Bool × Fresh σ → Vec (k + a) := fun p => emb (posB p.1) p.2.1
  have hEpos : ∀ p, pos (E p) = posB p.1 := fun p => pos_emb _ _
  have hElab : ∀ p, lab (E p) = p.2.1 := fun p => lab_emb _ _
  have hE : Function.Injective E := by
    intro p q h
    have h1 := congrArg pos h; have h2 := congrArg lab h
    rw [hEpos, hEpos] at h1; rw [hElab, hElab] at h2
    exact Prod.ext (hposB_inj h1) (Subtype.ext h2)
  have hnot : ∀ p, E p ∉ σ := by
    intro p hp; exact p.2.2 (Finset.mem_image.2 ⟨_, hp, hElab p⟩)
  have hcompat : ∀ p, ∀ y ∈ σ, E p + y ∈ gens k a := by
    intro p y hy
    rw [add_mem_gens, hElab, hEpos]
    exact ⟨fun h => p.2.2 (Finset.mem_image.2 ⟨y, hy, h.symm⟩), hposB_adj p.1 y (hposσ y hy)⟩
  have hU : wLinkVerts (tops d k a) σ = Finset.univ.image E := by
    ext x
    rw [mem_linkVerts ha' (by omega : σ.card ≤ d)]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxσ, hcl'⟩
      have hfresh : lab x ∉ σ.image lab := by
        intro hmem
        obtain ⟨y, hy, hyl⟩ := Finset.mem_image.1 hmem
        have := (isClique_insert hcl).1 hcl' y hy (fun h => hxσ (h ▸ hy))
        exact (add_mem_gens.1 this).1 hyl.symm
      have hp := hcl'.pos_two (Finset.mem_insert_of_mem hx0) (Finset.mem_insert_of_mem hy0)
        (Finset.mem_insert_self x σ) hxy
      obtain ⟨b, hb⟩ : ∃ b, posB b = pos x := by
        rcases hp with h | h
        · exact ⟨true, by simp only [posB, if_true]; rw [h]⟩
        · exact ⟨false, by simp only [posB, Bool.false_eq_true, if_false]; rw [h]⟩
      exact ⟨(b, ⟨lab x, hfresh⟩), ext_pl (by rw [hEpos, hb]) (by rw [hElab])⟩
    · rintro ⟨p, rfl⟩
      exact ⟨hnot p, (isClique_insert hcl).2 (fun y hy _ => hcompat p y hy)⟩
  -- counts
  set j := cnt σ x0 with hjdef
  have hj1 : 1 ≤ j := cnt_pos hx0
  have hj2 : 1 ≤ cnt σ y0 := cnt_pos hy0
  have hjsum := cnt_add_cnt hcl hx0 hy0 hxy
  rw [hσc] at hjsum
  have hjd : j + 2 ≤ d := by omega
  -- normalization
  set Z : ℚ := ∑ τ ∈ tops d k a, weight d k a τ with hZdef
  have hZ : 0 < Z := total_pos hd hk ha'
  set β : ℝ := 1 / (Z : ℝ) with hβdef
  have hβ : 0 < β := by rw [hβdef]; exact div_pos one_pos (by exact_mod_cast hZ)
  have hmu : ∀ T, ((mu d k a T : ℚ) : ℝ) = (weight d k a T : ℝ) * β := by
    intro T; unfold mu; rw [← hZdef, hβdef]; push_cast; ring
  set pp : ℝ := 1 / (Nat.choose (d - 1) (j + 1) : ℝ)
  set rr : ℝ := 1 / (Nat.choose (d - 1) j : ℝ)
  set ss : ℝ := 1 / (Nat.choose (d - 1) (j - 1) : ℝ)
  have hpp : 0 < pp := by
    have : (0 : ℝ) < Nat.choose (d - 1) (j + 1) := by exact_mod_cast Nat.choose_pos (by omega)
    positivity
  have hrr : 0 < rr := by
    have : (0 : ℝ) < Nat.choose (d - 1) j := by exact_mod_cast Nat.choose_pos (by omega)
    positivity
  have hss : 0 < ss := by
    have : (0 : ℝ) < Nat.choose (d - 1) (j - 1) := by exact_mod_cast Nat.choose_pos (by omega)
    positivity
  have hc'ne : posB false ≠ c := fun h => hxy (by simp [posB] at h; exact h.symm)
  have hcc : posB true = c := by simp [posB]
  -- link weights
  have hwA : ∀ p q, wLinkWeight (tops d k a) (mu d k a) σ (E p) (E q) =
      prodW (pairW (β * pp) (β * rr) (β * ss)) p q := by
    intro p q
    by_cases hpq : p = q
    · subst hpq; unfold wLinkWeight; rw [if_pos rfl]; simp [prodW]
    have hne : E p ≠ E q := fun h => hpq (hE h)
    rw [wLinkWeight_eq (by omega) hσc (hnot p) (hnot q) hne]
    have hclq := (isClique_insert hcl).2 (fun y hy _ => hcompat q y hy)
    by_cases hl : p.2 = q.2
    · rw [if_neg]
      · simp [prodW, hl]
      · intro h
        have := h (E p) (Finset.mem_insert_self _ _) (E q)
          (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hne
        rw [add_mem_gens, hElab, hElab] at this
        exact this.1 (by rw [hl])
    have hcl0 : IsClique (insert (E p) (insert (E q) σ)) := by
      rw [isClique_insert hclq]
      intro y hy hyp
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rw [add_mem_gens, hElab, hElab, hEpos]
        refine ⟨fun h' => hl (Subtype.ext h'), hposB_adj p.1 (E q) ?_⟩
        rw [hEpos]; cases q.1 <;> simp [posB]
      · exact hcompat p y hy
    rw [if_pos hcl0, hmu]
    have hcard : (insert (E p) (insert (E q) σ)).card = d + 1 := by
      rw [Finset.card_insert_of_notMem (by simp [hne, hnot p]),
        Finset.card_insert_of_notMem (hnot q)]
      omega
    have hT : insert (E p) (insert (E q) σ) ∈ tops d k a := mem_tops.2 ⟨hcard, hcl0⟩
    have hx0T : x0 ∈ insert (E p) (insert (E q) σ) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx0)
    have hy0T : y0 ∈ insert (E p) (insert (E q) σ) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy0)
    have hnall : ¬ ∀ x ∈ insert (E p) (insert (E q) σ), ∀ y ∈ insert (E p) (insert (E q) σ),
        pos x = pos y := fun h => hxy (h x0 hx0T y0 hy0T)
    rw [weight_split (by omega) hT hnall hx0T]
    have hcnt := cnt_insert2 (x := x0) (hnot p) (hnot q) hne
    rw [hEpos, hEpos, ← hjdef] at hcnt
    have hlab : (if p.2 = q.2 then (0 : ℝ) else 1) = 1 := if_neg hl
    simp only [prodW, hlab, mul_one]
    obtain ⟨b1, l1⟩ := p
    obtain ⟨b2, l2⟩ := q
    simp only at hcnt ⊢
    cases b1 <;> cases b2
    · rw [if_neg hc'ne] at hcnt
      rw [hcnt, show j + 0 + 0 - 1 = j - 1 by omega]
      simp only [pairW, ss]; push_cast; ring
    · rw [if_neg hc'ne, if_pos hcc] at hcnt
      rw [hcnt, show j + 0 + 1 - 1 = j by omega]
      simp only [pairW, rr]; push_cast; ring
    · rw [if_pos hcc, if_neg hc'ne] at hcnt
      rw [hcnt, show j + 1 + 0 - 1 = j by omega]
      simp only [pairW, rr]; push_cast; ring
    · rw [if_pos hcc] at hcnt
      rw [hcnt, show j + 1 + 1 - 1 = j + 1 by omega]
      simp only [pairW, pp]; push_cast; ring
  -- assemble
  have hcardL : Fintype.card (Fresh σ) = 2 ^ a - (d - 1) := by rw [card_fresh hcl, hσc]
  have hL3 : 3 ≤ Fintype.card (Fresh σ) := by rw [hcardL]; omega
  have hLd : 1 / ((Fintype.card (Fresh σ) : ℝ) - 1) ≤ 1 / (d : ℝ) := by
    have : (d : ℝ) + 1 ≤ (Fintype.card (Fresh σ) : ℝ) := by
      rw [hcardL]
      have : d + 1 ≤ 2 ^ a - (d - 1) := by omega
      exact_mod_cast this
    have hd1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    apply one_div_le_one_div_of_le (by positivity); linarith
  have hneX : Nonempty (Bool × Fresh σ) := by
    have : 0 < Fintype.card (Fresh σ) := by omega
    obtain ⟨l⟩ := Fintype.card_pos_iff.1 this
    exact ⟨(true, l)⟩
  have hP : ∀ b b', 0 < pairW (β * pp) (β * rr) (β * ss) b b' := by
    intro b b'; cases b <;> cases b' <;> simp only [pairW] <;> positivity
  have hdegW : ∀ b, 0 < ∑ b', pairW (β * pp) (β * rr) (β * ss) b b' := by
    intro b; exact Finset.sum_pos (fun b' _ => hP b b') Finset.univ_nonempty
  have hμ : ((β * pp) * (β * ss) - (β * rr) ^ 2) / ((β * pp + β * rr) * (β * rr + β * ss)) =
      1 / (d : ℝ) := by
    rw [← binom_identity d j hj1 hjd]
    have hβ' : β ^ 2 ≠ 0 := by positivity
    rw [show (β * pp) * (β * ss) - (β * rr) ^ 2 = β ^ 2 * (pp * ss - rr ^ 2) by ring,
      show (β * pp + β * rr) * (β * rr + β * ss) = β ^ 2 * ((pp + rr) * (rr + ss)) by ring,
      mul_div_mul_left _ _ hβ']
  apply tse_of_embedding E hE _ hU _ (prodW (pairW (β * pp) (β * rr) (β * ss))) hwA hneX
  · intro p q; simp only [prodW]; rw [pairW_symm]; congr 1; simp [eq_comm]
  · intro p q; simp only [prodW]
    exact mul_nonneg (hP _ _).le (by split_ifs <;> norm_num)
  · intro p; simp [prodW]
  · intro p; rw [deg_prodW]
    have := hdegW p.1
    have : (2 : ℝ) ≤ Fintype.card (Fresh σ) := by
      exact_mod_cast (by omega : 2 ≤ Fintype.card (Fresh σ))
    nlinarith
  · intro p q
    exact prod_conn _ true (fun w => ⟨hP w true, hP true w⟩) hL3 p q
  · positivity
  · intro f hf
    refine tensor_bound (pairW (β * pp) (β * rr) (β * ss)) (pairW_symm _ _ _) (fun w w' => (hP w w').le)
      hdegW _ (by positivity) (by omega) hLd ?_ f hf
    intro g hg
    rw [pair_bound _ _ _ _ (by positivity) (by positivity) (by positivity) hμ g hg]

end AbelianCayleyHDX.Supplement.CubeLabel

open ReplParity (Vec)
open Filter
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.Supplement.CubeLabel

open Finset

variable {d k a : ℕ}

lemma exists_label_ne_zero (ha : 1 ≤ a) : ∃ b : Vec a, b ≠ 0 :=
  ⟨Pi.single ⟨0, ha⟩ 1, fun h => by have := congrFun h ⟨0, ha⟩; simp at this⟩

lemma emb_zero_zero : (emb 0 0 : Vec (k + a)) = 0 := ext_pl (by simp; rfl) (by simp; rfl)

lemma span_gens (ha : 1 ≤ a) :
    Submodule.span (ZMod 2) ((gens k a : Finset (Vec (k + a))) : Set (Vec (k + a))) = ⊤ := by
  obtain ⟨b0, hb0⟩ := exists_label_ne_zero (a := a) ha
  set V := Submodule.span (ZMod 2) ((gens k a : Finset (Vec (k + a))) : Set (Vec (k + a)))
  have hlab : ∀ b : Vec a, emb (0 : Vec k) b ∈ V := by
    intro b
    by_cases hb : b = 0
    · rw [hb, emb_zero_zero]; exact V.zero_mem
    · apply Submodule.subset_span
      rw [Finset.mem_coe, mem_gens]
      simp only [lab_emb, pos_emb]
      exact ⟨hb, Or.inl (by simp)⟩
  have hpos : ∀ u : Vec k, emb u (0 : Vec a) ∈ V := by
    intro u
    have hu : u ∈ Submodule.span (ZMod 2) (Set.range fun i : Fin k => (Pi.single i 1 : Vec k)) := by
      have := (Pi.basisFun (ZMod 2) (Fin k)).span_eq
      rw [show ⇑(Pi.basisFun (ZMod 2) (Fin k)) = fun i => Pi.single i 1 from
        funext (Pi.basisFun_apply _ _)] at this
      rw [this]; trivial
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have h1 : emb (Pi.single i 1 : Vec k) b0 ∈ V := by
        apply Submodule.subset_span
        rw [Finset.mem_coe, mem_gens]
        simp only [lab_emb, pos_emb]
        exact ⟨hb0, Or.inr ⟨i, by simp⟩⟩
      have := V.add_mem h1 (hlab b0)
      rwa [emb_add, add_zero, vadd_self'] at this
    | zero => rw [emb_zero_zero]; exact V.zero_mem
    | add x y _ _ hx hy =>
      have := V.add_mem hx hy
      rwa [emb_add, add_zero] at this
    | smul c x _ hx =>
      rcases (show c = 0 ∨ c = 1 by fin_cases c; exacts [Or.inl rfl, Or.inr rfl]) with rfl | rfl
      · rw [zero_smul, emb_zero_zero]; exact V.zero_mem
      · rwa [one_smul]
  rw [eq_top_iff]
  intro x _
  have := V.add_mem (hpos (pos x)) (hlab (lab x))
  rwa [emb_add, add_zero, zero_add, emb_pos_lab] at this

lemma card_gens : (gens k a).card = (k + 1) * (2 ^ a - 1) := by
  classical
  set P : Finset (Vec k) := insert 0 (Finset.univ.image fun i : Fin k => (Pi.single i 1 : Vec k))
  set B : Finset (Vec a) := Finset.univ.filter fun b => b ≠ 0
  have hP : P.card = k + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (fun i j h => single_inj' h)]
    · simp
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro i h; exact single_ne_zero' i h
  have hB : B.card = 2 ^ a - 1 := by
    have : B = Finset.univ.erase 0 := by ext b; simp [B]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp
  have heq : gens k a = (P ×ˢ B).image fun p => emb p.1 p.2 := by
    ext s
    simp only [mem_gens, Finset.mem_image, Finset.mem_product, Prod.exists, P, B,
      Finset.mem_insert, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨hl, hp⟩
      refine ⟨pos s, lab s, ⟨?_, hl⟩, emb_pos_lab s⟩
      rcases hp with h | ⟨i, hi⟩
      · left; simpa using h
      · right; exact ⟨i, by simpa using hi.symm⟩
    · rintro ⟨u, b, ⟨hu, hb⟩, rfl⟩
      simp only [lab_emb, pos_emb]
      refine ⟨hb, ?_⟩
      rcases hu with rfl | ⟨i, rfl⟩
      · left; simp
      · right; exact ⟨i, by simp⟩
  rw [heq, Finset.card_image_of_injective, Finset.card_product, hP, hB]
  intro p q h
  have h1 := congrArg pos h; have h2 := congrArg lab h
  simp only [pos_emb, lab_emb] at h1 h2
  exact Prod.ext h1 h2

end AbelianCayleyHDX.Supplement.CubeLabel

open AbelianCayleyHDX.Supplement.CubeLabel in
theorem solution :
    ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∃ (n : ℕ → ℕ) (S : ∀ j, Finset (Vec (n j))) (tops : ∀ j, Finset (Finset (Vec (n j))))
        (μ : ∀ j, Finset (Vec (n j)) → ℚ),
        Tendsto n atTop atTop ∧
        (∀ j, AbelianCayleyHDX.Supplement.IsWeightedCayleyComplex d (S j) (tops j) (μ j) ∧
          AbelianCayleyHDX.Supplement.IsWeightedTranslationInvariant (tops j) (μ j) ∧
          (AbelianCayleyHDX.cayleyGraph (S j)).Connected ∧
          (∀ σ : Finset (Vec (n j)), AbelianCayleyHDX.Supplement.IsFace (tops j) σ →
            σ.card ≤ d - 1 → AbelianCayleyHDX.Supplement.LinkConnected (tops j) σ) ∧
          AbelianCayleyHDX.Supplement.HasCodimTwoLocalSpectralNorm d (tops j) (μ j) (1 / (d : ℝ)) ∧
          c * (n j : ℝ) ≤ ((S j).card : ℝ) ∧ ((S j).card : ℝ) ≤ C * (n j : ℝ)) ∧
        AbelianCayleyHDX.Supplement.IsExplicitWeightedFamily n S tops μ := by
  intro d hd
  set a := d + 2 with hadef
  have h2a : 2 * d + 3 ≤ 2 ^ a := by
    have : d + 1 ≤ 2 ^ d := by
      have := Nat.lt_two_pow_self (n := d)
      omega
    rw [hadef, pow_add]; omega
  have ha1 : 1 ≤ a := by omega
  have ha' : d + 1 ≤ 2 ^ a := by omega
  refine ⟨1 / (a : ℝ), by positivity, 2 ^ a, by positivity, fun j => (encNat j).length + a,
    fun j => gens (encNat j).length a, fun j => AbelianCayleyHDX.Supplement.CubeLabel.tops d (encNat j).length a,
    fun j => mu d (encNat j).length a, ?_, fun j => ?_,
    AbelianCayleyHDX.Supplement.explicit_cube_label_family_log d hd⟩
  · rw [tendsto_atTop_atTop]
    intro b
    refine ⟨2 ^ b, fun j hj => ?_⟩
    have h1 : j < 2 ^ (Nat.digits 2 j).length := Nat.lt_base_pow_length_digits (by norm_num)
    have h2 : (encNat j).length = 2 * (Nat.digits 2 j).length + 2 := by
      simp [encNat, encBits, List.length_flatMap, Function.comp_def]
      ring
    have h3 : b < (Nat.digits 2 j).length := by
      by_contra hc; push Not at hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
      omega
    omega
  have hk : 1 ≤ (encNat j).length := by
    simp [encNat, encBits]
  -- the Cayley graph is connected
  have hS0 : (0 : Vec ((encNat j).length + a)) ∉ gens (encNat j).length a := by
    intro h; exact (mem_gens.1 h).1 lab_zero
  have hSne : (gens (encNat j).length a).Nonempty := by
    obtain ⟨b0, hb0⟩ := exists_label_ne_zero (a := a) ha1
    refine ⟨emb 0 b0, ?_⟩
    rw [mem_gens]; simp only [lab_emb, pos_emb]; exact ⟨hb0, Or.inl (by simp)⟩
  have hconn : (AbelianCayleyHDX.cayleyGraph (gens (encNat j).length a)).Connected :=
    ((AbelianCayleyHDX.lemma_2_1 (gens (encNat j).length a) hSne hS0).2.2.2.2).2 (span_gens ha1)
  refine ⟨⟨fun τ hτ => (mem_tops.1 hτ).1, hSne, hS0, edges_eq (by omega) ha',
      fun τ hτ => mu_pos hd hk ha' hτ, mu_sum hd hk ha', fun s _ x y => faceMass_edge s x y⟩,
    fun g τ hτ => ⟨tops_image_add hτ g, mu_image_add τ g⟩, hconn, ?_, ?_, ?_, ?_⟩
  · -- links are connected
    intro σ hσf hσc
    by_cases hne : σ.Nonempty
    · exact linkConnected_nonempty (by omega) hσf hne hσc
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      intro u _ v _
      have hr := (SimpleGraph.reachable_iff_reflTransGen u v).1 (hconn.preconnected u v)
      refine Relation.ReflTransGen.mono ?_ u v hr
      intro x y hxy
      obtain ⟨hne', hs⟩ := hxy
      have hcl : IsClique ({x, y} : Finset (Vec ((encNat j).length + a))) := by
        intro p hp q hq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        · exact absurd rfl hpq
        · exact hs
        · rw [add_comm p q]; exact hs
        · exact absurd rfl hpq
      obtain ⟨τ, hτ, hsub⟩ := exists_top_of_clique ha' hcl (by simp)
        (by have := Finset.card_le_two (a := x) (b := y); omega)
      have hmem : ∀ z, z ∈ AbelianCayleyHDX.Supplement.wLinkVerts (AbelianCayleyHDX.Supplement.CubeLabel.tops d (encNat j).length a) ∅ := by
        intro z
        rw [mem_linkVerts ha' (by simp)]
        refine ⟨Finset.notMem_empty z, ?_⟩
        intro p hp q hq hpq
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hp hq
        rw [hp, hq] at hpq; exact absurd rfl hpq
      exact ⟨hmem x, hmem y, hne', τ, hτ, by simpa using hsub⟩
  · -- codimension-two links
    intro σ hσf hσc
    have hne : σ.Nonempty := by rw [← Finset.card_pos, hσc]; omega
    obtain ⟨x0, hx0⟩ := hne
    by_cases hall : ∀ x ∈ σ, pos x = pos x0
    · exact codim2_single hd hk h2a hσf hσc hx0 hall
    · push Not at hall
      obtain ⟨y0, hy0, hne'⟩ := hall
      exact codim2_split hd hk h2a hσf hσc hx0 hy0 (Ne.symm hne')
  · -- lower degree bound
    rw [card_gens]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ a - 1 := by
      have : (2 : ℝ) ≤ 2 ^ a := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha1
      linarith
    have hA : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hj0 : (0 : ℝ) ≤ ((encNat j).length : ℝ) := by positivity
    have h3 : 1 / (a : ℝ) * (((encNat j).length : ℝ) + a) ≤ ((encNat j).length : ℝ) + 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; nlinarith
    push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
    nlinarith
  · -- upper degree bound
    rw [card_gens]
    push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have h2 : (0 : ℝ) ≤ 2 ^ a := by positivity
    nlinarith
