-- Prove2me | Definitions.Def_RPLib_S3_ConjClassesC
-- name    : RPLib_S3_ConjClassesC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:54:47.5436+00:00
-- url     : https://prove2.me/theorems/32f7027b-e613-490c-973d-4b60cf2d6b9f
-- title:
--   The Eichler-Selberg trace formula, conjugacy classes part C: trace classification
-- statement:
--   Classification of integer $2 \times 2$ matrices by trace and determinant: scalar matrices, elliptic matrices ($t^2 < 4n$, no conjugate is upper triangular), split hyperbolic and parabolic matrices with explicit upper triangular representatives and centralisers, and non-split hyperbolic matrices.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_ConjClassesA

/-!
# Conjugacy classes (unit S3-ConjClasses, part C): trace classification, hyperbolic and parabolic classes

For `γ ∈ M₂(ℤ)` with `t = tr γ`, `n = det γ`:
* scalar: `formOf γ = 0` iff `γ = a I` (then `t = 2a`, `n = a²`);
* elliptic (`t² < 4n`): no `SL(2, ℤ)`-conjugate has lower-left entry `0`;
* `t² - 4n = u²`: some conjugate is upper triangular; split hyperbolic (`u ≠ 0`) representatives
  `[[a, b], [0, d]]` with `0 ≤ b < |a - d|`, centraliser `{±1}`; parabolic non-scalar (`u = 0`) representatives
  `[[a, b], [0, a]]`, `b ≠ 0`, centraliser `{±T^x}`;
* non-split hyperbolic (`t² - 4n > 0` not a square): no conjugate is upper triangular.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Conj

open Matrix MatrixGroups RamanujanPetersson.Hurwitz

/-! ## Commutation and the conjugates by `T^x` -/

theorem conj_eq_iff_commute (z : SL(2, ℤ)) (γ : Mat) : conj z γ = γ ↔ (z : Mat) * γ = γ * z := by
  constructor
  · intro h
    calc (z : Mat) * γ = conj z γ * z := by
          rw [conj, Matrix.mul_assoc _ _ (z : Mat), coe_inv_mul_coe, Matrix.mul_one]
      _ = γ * z := by rw [h]
  · intro h
    rw [conj, h, Matrix.mul_assoc, coe_mul_coe_inv, Matrix.mul_one]

theorem conj_neg_one (γ : Mat) : conj (-1) γ = γ := by
  rw [conj_eq_iff_commute]; simp

theorem conj_T_zpow (x : ℤ) (γ : Mat) :
    conj (ModularGroup.T ^ x) γ = !![γ 0 0 + x * γ 1 0, γ 0 1 + x * γ 1 1 - x * (γ 0 0 + x * γ 1 0);
      γ 1 0, γ 1 1 - x * γ 1 0] := by
  rw [conj, ← _root_.zpow_neg, ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

theorem conj_inv_lower_eq_eval (k : SL(2, ℤ)) (γ : Mat) :
    (conj k⁻¹ γ) 1 0 = (formOf γ).eval (k 0 0) (k 1 0) := by
  have h1 : (conj k⁻¹ γ) 1 0 = (formOf (conj k⁻¹ γ)).a := rfl
  rw [h1, formOf_conj, smul_def, inv_inv, act_a]

theorem disc_of_upper {γ : Mat} (h : γ 1 0 = 0) : γ.trace ^ 2 - 4 * γ.det = (γ 0 0 - γ 1 1) ^ 2 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, h]; ring

/-! ## Isotropic vectors -/

theorem eval_isotropic_root (f : BQF) {u : ℤ} (hu : f.disc = u ^ 2) :
    ∃ p r : ℤ, (p ≠ 0 ∨ r ≠ 0) ∧ f.eval p r = 0 := by
  by_cases hA : f.a = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [BQF.eval, hA]⟩
  · refine ⟨u - f.b, 2 * f.a, Or.inr (by omega), ?_⟩
    have h : f.a * f.eval (u - f.b) (2 * f.a) = 0 := by
      simp only [BQF.eval, BQF.disc] at hu ⊢
      linear_combination (-(f.a ^ 2)) * hu
    exact (mul_eq_zero.1 h).resolve_left hA

/-- A form with square discriminant has a primitive zero, the first column of some `k ∈ SL(2, ℤ)`. -/
theorem exists_isotropic (f : BQF) {u : ℤ} (hu : f.disc = u ^ 2) :
    ∃ k : SL(2, ℤ), f.eval (k 0 0) (k 1 0) = 0 := by
  obtain ⟨p0, r0, hne, h0⟩ := eval_isotropic_root f hu
  have hg : 0 < Int.gcd p0 r0 := Int.gcd_pos_iff.2 hne
  obtain ⟨g, p, r, hg0, hcop, hp, hr⟩ := Int.exists_gcd_one' hg
  rw [hp, hr] at h0
  have hev : f.eval p r = 0 := by
    have : (g : ℤ) ^ 2 * f.eval p r = 0 := by
      rw [← h0]; simp only [BQF.eval]; ring
    exact (mul_eq_zero.1 this).resolve_left (by positivity)
  have hb := Int.gcd_eq_gcd_ab p r
  rw [hcop] at hb; push_cast at hb
  have hdet : (p, -Int.gcdB p r, r, Int.gcdA p r).1 * (p, -Int.gcdB p r, r, Int.gcdA p r).2.2.2 -
      (p, -Int.gcdB p r, r, Int.gcdA p r).2.1 * (p, -Int.gcdB p r, r, Int.gcdA p r).2.2.1 = 1 := by
    show p * Int.gcdA p r - -Int.gcdB p r * r = 1
    linear_combination hb.symm
  refine ⟨mkSL _ hdet, ?_⟩
  have he := ent_mkSL _ hdet
  simp only [ent, Prod.mk.injEq] at he
  rw [he.1, he.2.2.1]; exact hev

/-- `t² - 4n` a square: `γ` is `SL(2, ℤ)`-conjugate to an upper triangular matrix. -/
theorem exists_conj_upper {γ : Mat} {u : ℤ} (hu : γ.trace ^ 2 - 4 * γ.det = u ^ 2) :
    ∃ g : SL(2, ℤ), (conj g γ) 1 0 = 0 := by
  obtain ⟨k, hk⟩ := exists_isotropic (formOf γ) (by rw [disc_formOf]; exact hu)
  exact ⟨k⁻¹, by rw [conj_inv_lower_eq_eval]; exact hk⟩

/-! ## Trace classification -/

/-- Scalar classes: the fixed-point form vanishes iff `γ = a I`. -/
theorem formOf_eq_zero_iff {γ : Mat} : formOf γ = ⟨0, 0, 0⟩ ↔ γ = !![γ 0 0, 0; 0, γ 0 0] := by
  constructor
  · intro h
    simp only [formOf, BQF.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> omega
  · intro h; rw [h]; simp [formOf]

theorem trace_det_of_scalar {γ : Mat} (h : formOf γ = ⟨0, 0, 0⟩) :
    γ.trace = 2 * γ 0 0 ∧ γ.det = γ 0 0 ^ 2 := by
  rw [formOf_eq_zero_iff.1 h]
  constructor <;> simp [Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- Elliptic (`t² < 4n`): no conjugate has lower-left entry `0`. -/
theorem lower_ne_zero_of_elliptic {γ : Mat} (h : γ.trace ^ 2 < 4 * γ.det) (g : SL(2, ℤ)) :
    (conj g γ) 1 0 ≠ 0 := by
  intro h0
  have := disc_of_upper h0
  rw [trace_conj, det_conj] at this
  nlinarith [sq_nonneg ((conj g γ) 0 0 - (conj g γ) 1 1)]

/-- Non-split hyperbolic (`t² - 4n` not a square): no conjugate is upper triangular. -/
theorem lower_ne_zero_of_nonsquare {γ : Mat} (h : ¬ ∃ u : ℤ, γ.trace ^ 2 - 4 * γ.det = u ^ 2)
    (g : SL(2, ℤ)) : (conj g γ) 1 0 ≠ 0 := by
  intro h0; apply h
  refine ⟨(conj g γ) 0 0 - (conj g γ) 1 1, ?_⟩
  rw [← disc_of_upper h0, trace_conj, det_conj]

/-- Split hyperbolic representatives `[[a, b], [0, d]]`, `a ≠ d`, `0 ≤ b < |a - d|`. -/
theorem exists_hyp_rep {γ : Mat} {u : ℤ} (hu : γ.trace ^ 2 - 4 * γ.det = u ^ 2) (hu0 : u ≠ 0) :
    ∃ g : SL(2, ℤ), (conj g γ) 1 0 = 0 ∧ (conj g γ) 0 0 ≠ (conj g γ) 1 1 ∧
      0 ≤ (conj g γ) 0 1 ∧ (conj g γ) 0 1 < |(conj g γ) 0 0 - (conj g γ) 1 1| := by
  obtain ⟨g, hg⟩ := exists_conj_upper hu
  have hne : (conj g γ) 0 0 - (conj g γ) 1 1 ≠ 0 := by
    intro h
    have := disc_of_upper hg
    rw [trace_conj, det_conj, hu, h] at this
    exact hu0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by rw [this]; ring))
  have key : conj (ModularGroup.T ^ ((conj g γ) 0 1 / ((conj g γ) 0 0 - (conj g γ) 1 1)) * g) γ =
      !![(conj g γ) 0 0, (conj g γ) 0 1 % ((conj g γ) 0 0 - (conj g γ) 1 1); 0, (conj g γ) 1 1] := by
    rw [conj_mul, conj_T_zpow, hg, Int.emod_def]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  refine ⟨ModularGroup.T ^ ((conj g γ) 0 1 / ((conj g γ) 0 0 - (conj g γ) 1 1)) * g, ?_⟩
  rw [key]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  refine ⟨trivial, fun h => hne (by rw [h, sub_self]), Int.emod_nonneg _ hne, ?_⟩
  have := Int.emod_lt ((conj g γ) 0 1) hne
  rwa [Int.natCast_natAbs] at this

/-- Parabolic non-scalar representatives `[[a, b], [0, a]]`, `b ≠ 0`. -/
theorem exists_par_rep {γ : Mat} (ht : γ.trace ^ 2 = 4 * γ.det) (hns : formOf γ ≠ ⟨0, 0, 0⟩) :
    ∃ g : SL(2, ℤ), (conj g γ) 1 0 = 0 ∧ (conj g γ) 0 0 = (conj g γ) 1 1 ∧ (conj g γ) 0 1 ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_conj_upper (u := 0) (by rw [ht]; ring)
  have hd := disc_of_upper hg
  rw [trace_conj, det_conj, ht, sub_self] at hd
  have heq : (conj g γ) 0 0 = (conj g γ) 1 1 := by
    have : ((conj g γ) 0 0 - (conj g γ) 1 1) ^ 2 = 0 := hd.symm
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    omega
  refine ⟨g, hg, heq, fun hb => hns ?_⟩
  have h0 : formOf (conj g γ) = ⟨0, 0, 0⟩ := by
    simp only [formOf, BQF.mk.injEq]; exact ⟨hg, by rw [heq, sub_self], by rw [hb, neg_zero]⟩
  have h1 : formOf γ = g⁻¹ • formOf (conj g γ) := by rw [← formOf_conj, conj_inv_conj]
  rw [h1, h0, smul_def, inv_inv]
  simp [act, BQF.subst]

/-! ## Centralisers -/

/-- Split hyperbolic: the centraliser of `[[a, b], [0, d]]`, `a ≠ d`, in `SL(2, ℤ)` is `{±1}`. -/
theorem centralizer_hyp {γ : Mat} (h10 : γ 1 0 = 0) (hne : γ 0 0 ≠ γ 1 1) (z : SL(2, ℤ)) :
    conj z γ = γ ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    rw [conj_eq_iff_commute] at hz
    have e10 := congrFun (congrFun hz 1) 0
    have e01 := congrFun (congrFun hz 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h10] at e10 e01
    have hdet := det_eq z
    have hz10 : z 1 0 = 0 := by
      have : z 1 0 * (γ 0 0 - γ 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
    rw [hz10, mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have hz01 : z 0 1 = 0 := by
        have : z 0 1 * (γ 0 0 - γ 1 1) = 0 := by
          linear_combination (-1 : ℤ) * e01 + γ 0 1 * h0 - γ 0 1 * h1
        exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
      left; ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, hz10, hz01]
    · have hz01 : z 0 1 = 0 := by
        have : z 0 1 * (γ 0 0 - γ 1 1) = 0 := by
          linear_combination (-1 : ℤ) * e01 + γ 0 1 * h0 - γ 0 1 * h1
        exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
      right; ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, hz10, hz01]
  · rintro (rfl | rfl)
    · exact conj_one γ
    · exact conj_neg_one γ

/-- Parabolic non-scalar: the centraliser of `[[a, b], [0, a]]`, `b ≠ 0`, in `SL(2, ℤ)` is `{±T^x}`. -/
theorem centralizer_par {γ : Mat} (h10 : γ 1 0 = 0) (heq : γ 0 0 = γ 1 1) (hb : γ 0 1 ≠ 0)
    (z : SL(2, ℤ)) : conj z γ = γ ↔ ∃ x : ℤ, z = ModularGroup.T ^ x ∨ z = -ModularGroup.T ^ x := by
  constructor
  · intro hz
    rw [conj_eq_iff_commute] at hz
    have e00 := congrFun (congrFun hz 0) 0
    have e01 := congrFun (congrFun hz 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h10] at e00 e01
    have hdet := det_eq z
    have hz10 : z 1 0 = 0 := by
      have : γ 0 1 * z 1 0 = 0 := by linear_combination -e00
      exact (mul_eq_zero.1 this).resolve_left hb
    have hzd : z 0 0 = z 1 1 := by
      have : γ 0 1 * (z 0 0 - z 1 1) = 0 := by linear_combination e01 + z 0 1 * heq
      have := (mul_eq_zero.1 this).resolve_left hb
      omega
    rw [hz10, mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine ⟨z 0 1, Or.inl ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h0, h1, hz10]
    · refine ⟨-z 0 1, Or.inr ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h0, h1, hz10]
  · rintro ⟨x, rfl | rfl⟩
    · rw [conj_T_zpow]
      ext i j; fin_cases i <;> fin_cases j <;> simp [h10, heq]
    · rw [← neg_one_mul, conj_mul, conj_neg_one, conj_T_zpow]
      ext i j; fin_cases i <;> fin_cases j <;> simp [h10, heq]

/-- `-1 ∉ Γ₁(M)` for `M ≥ 3`. -/
theorem neg_one_not_mem_Gamma1 {M : ℕ} (hM : 3 ≤ M) : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 M := by
  have : NeZero M := ⟨by omega⟩
  rw [CongruenceSubgroup.Gamma1_mem]
  rintro ⟨h, -, -⟩
  have h2 : ((2 : ℤ) : ZMod M) = 0 := by
    have e : ((-1 : SL(2, ℤ)) 0 0 : ℤ) = -1 := by simp
    rw [e] at h; push_cast at h ⊢; linear_combination -h
  have := Int.le_of_dvd (by norm_num) ((ZMod.intCast_zmod_eq_zero_iff_dvd 2 M).1 h2)
  omega

end RamanujanPetersson.S3.Conj


