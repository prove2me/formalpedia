-- Prove2me | Definitions.Def_FracTruthSched_PaddingLimitRounding
-- name    : FracTruthSched_PaddingLimitRounding
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:59:18.703129+00:00
-- url     : https://prove2.me/theorems/52fdd03d-5c09-4536-9a99-be40e427bb7a
-- title:
--   Ceiling rounding of real graph inputs to rational graph inputs
-- statement:
--   The exact real-to-rational rounding device of Appendix A.3. Define $R_h(a)=\lceil h!a\rceil/h!$ and apply it componentwise. The module proves $0\le R_h(a)-a<1/h!$ for $a\ge0$, preservation of zeros, nonnegativity and strict positivity, and $R_h(a)\to a$ for every fixed real $a$. Every rational value is eventually fixed once the denominator divides $h!$. Rounded graph inputs are rational graph inputs, and rounding commutes with one-machine row updates, zero rows, and arbitrary task relabelling. These identities give exactly the admissibility and equilibrium expressions needed to pass coordinatewise limits from rational to real graph inputs.
-- source:
--   Anastasiadis et al., arXiv:2611.06642v1, Appendix A.3, pp.26–27, Claim 9. The uniform error bound also yields the paper's rounding error at most $n(n-1)\ell/2+n$ on any machine load.

import Mathlib
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_PaddingSequence
set_option autoImplicit false
open Filter Topology Set
namespace FracTruthSched.PaddingLimitAux
private theorem tendsto_factorial_real : Tendsto (fun h : ℕ => (h.factorial : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  exact tendsto_atTop_mono Nat.self_le_factorial tendsto_id
private theorem tendsto_inv_factorial : Tendsto (fun h : ℕ => (h.factorial : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_factorial_real
noncomputable def roundVal (h : ℕ) (a : ℝ) : ℝ := ((⌈(h.factorial : ℝ) * a⌉ : ℤ) : ℝ) / (h.factorial : ℝ)
lemma factorial_real_pos (h : ℕ) : 0 < (h.factorial : ℝ) := by positivity
lemma roundVal_zero (h : ℕ) : roundVal h 0 = 0 := by simp [roundVal]
lemma le_roundVal (h : ℕ) (a : ℝ) : a ≤ roundVal h a := by
  rw [roundVal, le_div_iff₀ (factorial_real_pos h)]
  nlinarith [Int.le_ceil ((h.factorial : ℝ) * a)]
lemma roundVal_sub_lt (h : ℕ) (a : ℝ) : roundVal h a - a < (h.factorial : ℝ)⁻¹ := by
  rw [roundVal, sub_lt_iff_lt_add, div_lt_iff₀ (factorial_real_pos h)]
  calc
    ((⌈(h.factorial : ℝ) * a⌉ : ℤ) : ℝ) < (h.factorial : ℝ) * a + 1 := Int.ceil_lt_add_one _
    _ = ((h.factorial : ℝ)⁻¹ + a) * (h.factorial : ℝ) := by
      rw [add_mul, inv_mul_cancel₀ (ne_of_gt (factorial_real_pos h))]
      ring
lemma roundVal_le_add_one (h : ℕ) (a : ℝ) : roundVal h a ≤ a + 1 := by
  have h1 : (1 : ℝ) ≤ h.factorial := by exact_mod_cast Nat.factorial_pos h
  have hi : (h.factorial : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ (factorial_real_pos h)]; exact h1
  linarith [roundVal_sub_lt h a]
lemma roundVal_nonneg (h : ℕ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ roundVal h a := ha.trans (le_roundVal h a)
lemma roundVal_pos (h : ℕ) {a : ℝ} (ha : 0 < a) : 0 < roundVal h a := ha.trans_le (le_roundVal h a)
lemma roundVal_rational (h : ℕ) (a : ℝ) : ∃ q : ℚ, roundVal h a = q := by
  refine ⟨((⌈(h.factorial : ℝ) * a⌉ : ℤ) : ℚ) / (h.factorial : ℚ), ?_⟩
  simp [roundVal, Rat.cast_div]
lemma tendsto_roundVal (a : ℝ) : Tendsto (fun h => roundVal h a) atTop (𝓝 a) := by
  have hd : Tendsto (fun h => roundVal h a - a) atTop (𝓝 0) := by
    apply squeeze_zero (fun h => sub_nonneg.mpr (le_roundVal h a)) (fun h => (roundVal_sub_lt h a).le)
    exact tendsto_inv_factorial
  have ht : Tendsto (fun h => a + (roundVal h a - a)) atTop (𝓝 (a + 0)) := (tendsto_const_nhds (x := a)).add hd
  simpa [add_sub_assoc] using ht
lemma roundVal_eventually_rat (q : ℚ) : ∀ᶠ h : ℕ in atTop, roundVal h (q : ℝ) = (q : ℝ) := by
  filter_upwards [eventually_ge_atTop q.den] with h hh
  obtain ⟨z, hz⟩ := Nat.dvd_factorial q.den_pos hh
  have hval : (h.factorial : ℝ) * (q : ℝ) = ((q.num * (z : ℤ) : ℤ) : ℝ) := by
    rw [hz]
    push_cast
    rw [Rat.cast_def]
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    field_simp
  rw [roundVal, hval, Int.ceil_intCast, ← hval]
  exact mul_div_cancel_left₀ _ (ne_of_gt (factorial_real_pos h))

noncomputable def roundInput {n ℓ : ℕ} (h : ℕ) (t : Fin n → CoreTask n ℓ → ℝ) :
    Fin n → CoreTask n ℓ → ℝ := fun i e => roundVal h (t i e)

lemma roundInput_graph {n ℓ : ℕ} (h : ℕ) {t : Fin n → CoreTask n ℓ → ℝ}
    (ht : IsGraphInput t) : IsGraphInput (roundInput h t) := by
  intro i e
  obtain ⟨hnonneg, hzero⟩ := ht i e
  exact ⟨roundVal_nonneg h hnonneg, fun hi => by simp [roundInput, hzero hi, roundVal_zero]⟩

lemma roundInput_rat {n ℓ : ℕ} (h : ℕ) {t : Fin n → CoreTask n ℓ → ℝ}
    (ht : IsGraphInput t) : IsRatGraphInput (roundInput h t) := by
  refine ⟨roundInput_graph h ht, ?_⟩
  intro i e
  exact roundVal_rational h (t i e)

lemma roundInput_relabel {n ℓ : ℕ} (h : ℕ) (γ : Equiv.Perm (CoreTask n ℓ))
    (t : Fin n → CoreTask n ℓ → ℝ) :
    roundInput h (relabel γ t) = relabel γ (roundInput h t) := rfl

lemma roundInput_update_zero {n ℓ : ℕ} (h : ℕ) (t : Fin n → CoreTask n ℓ → ℝ)
    (i : Fin n) : Function.update (roundInput h t) i 0 =
      roundInput h (Function.update t i 0) := by
  funext u e
  by_cases hu : u = i
  · subst u
    simp [roundInput, roundVal_zero]
  · simp [Function.update_of_ne hu, roundInput]

lemma roundInput_update {n ℓ : ℕ} (h : ℕ) (t : Fin n → CoreTask n ℓ → ℝ)
    (i : Fin n) (b : CoreTask n ℓ → ℝ) : Function.update (roundInput h t) i (fun e => roundVal h (b e)) =
      roundInput h (Function.update t i b) := by
  funext u e
  by_cases hu : u = i
  · subst u; simp [roundInput]
  · simp [Function.update_of_ne hu, roundInput]

lemma roundInput_tendsto {n ℓ : ℕ} (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n)
    (e : CoreTask n ℓ) : Tendsto (fun h => roundInput h t i e) atTop (𝓝 (t i e)) :=
  tendsto_roundVal (t i e)

lemma roundInput_eventually_rat {n ℓ : ℕ} {t : Fin n → CoreTask n ℓ → ℝ}
    (ht : IsRatGraphInput t) : ∀ᶠ h : ℕ in atTop, roundInput h t = t := by
  have he : ∀ i e, ∀ᶠ h : ℕ in atTop, roundInput h t i e = t i e := by
    intro i e
    obtain ⟨q, hq⟩ := ht.2 i e
    simpa [roundInput, hq] using roundVal_eventually_rat q
  have hall : ∀ᶠ h : ℕ in atTop, ∀ p : Fin n × CoreTask n ℓ,
      roundInput h t p.1 p.2 = t p.1 p.2 := Filter.eventually_all.2 (fun p => he p.1 p.2)
  filter_upwards [hall] with h hh
  funext i e
  exact hh (i, e)
end FracTruthSched.PaddingLimitAux


