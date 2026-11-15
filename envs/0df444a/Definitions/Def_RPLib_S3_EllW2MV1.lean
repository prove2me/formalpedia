-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV1
-- name    : RPLib_S3_EllW2MV1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:51:29.005023+00:00
-- url     : https://prove2.me/theorems/62439dc5-1f67-4660-80c2-367fff323cb0
-- title:
--   The Eichler-Selberg trace formula in weight two: the mean `μ_c` as a sum over `(ZMod q)²`
-- statement:
--   The mean `μ_c` as a sum over `(ZMod q)²`.
--
--   For `c ≠ 0` and `q = |c| M`:
--   * `Lbar M δ' G`: `levelCount` for matrices over `ZMod M`; `levelCount_eq_Lbar` (by `rfl`).
--   * `piM M n c hMq (x, d) = [[x̄, ((x̃ d̃ - n)/c)‾], [c̄, d̄]]` and `Xc n c (x, d) :↔ c ∣ x̃ d̃ - n`.
--   * `divc_congr`: `(A - n)/c ≡ (B - n)/c (mod M)` when `c ∣ A - n`, `c ∣ B - n` and `|c| M ∣ A - B`.
--   * **`two_mul_muc_eq_sum`**: `2 M (q μ_c) = Σ_{z ∈ (ZMod q)²} [Xc z] Lbar(piM z)`
--     (the `j = 0` case of `dft_WcF_eq`, then `y = x + d`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2K2b
import Definitions.Def_RPLib_S3_EllW2W

/-!
# S3-ES-Wt2 (O6, file MV1): the mean `μ_c` as a sum over `(ZMod q)²`

For `c ≠ 0` and `q = |c| M`:
* `Lbar M δ' G`: `levelCount` for matrices over `ZMod M`; `levelCount_eq_Lbar` (by `rfl`).
* `piM M n c hMq (x, d) = [[x̄, ((x̃ d̃ - n)/c)‾], [c̄, d̄]]` and `Xc n c (x, d) :↔ c ∣ x̃ d̃ - n`.
* `divc_congr`: `(A - n)/c ≡ (B - n)/c (mod M)` when `c ∣ A - n`, `c ∣ B - n` and `|c| M ∣ A - B`.
* **`two_mul_muc_eq_sum`**: `2 M (q μ_c) = Σ_{z ∈ (ZMod q)²} [Xc z] Lbar(piM z)`
  (the `j = 0` case of `dft_WcF_eq`, then `y = x + d`).
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-- `levelCount` on matrices over `ZMod M`. -/
def Lbar (M : ℕ) [NeZero M] (δ' : ZMod M) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) : ℕ :=
  (Finset.univ.filter fun v : Fin 2 → ZMod M =>
    (∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0) ∧ G.mulVec v = δ' • v).card

variable {M : ℕ} [NeZero M]

lemma levelCount_eq_Lbar (δ' : ZMod M) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    S3.levelCount M δ' g = Lbar M δ' (g.map (Int.castRingHom (ZMod M))) := rfl

/-- The reduction mod `M` of `mkT` in the coordinates `(x, d) = (a, t - a)`. -/
def piM (M : ℕ) [NeZero M] (n c : ℤ) {q : ℕ} (hMq : M ∣ q) (z : ZMod q × ZMod q) :
    Matrix (Fin 2) (Fin 2) (ZMod M) :=
  !![ZMod.castHom hMq (ZMod M) z.1, ((((z.1.val : ℤ) * z.2.val - n) / c : ℤ) : ZMod M);
     (c : ZMod M), ZMod.castHom hMq (ZMod M) z.2]

/-- The condition `c ∣ x̃ d̃ - n`. -/
def Xc (n c : ℤ) {q : ℕ} (z : ZMod q × ZMod q) : Prop := c ∣ (z.1.val : ℤ) * z.2.val - n

instance (n c : ℤ) {q : ℕ} (z : ZMod q × ZMod q) : Decidable (Xc n c z) := by
  unfold Xc; infer_instance

lemma natAbs_mul_dvd_iff (c : ℤ) (m : ℕ) (X : ℤ) :
    ((c.natAbs * m : ℕ) : ℤ) ∣ X ↔ c * m ∣ X := by
  have h : ((c.natAbs * m : ℕ) : ℤ) = |c * m| := by
    rw [abs_mul, Nat.abs_cast, Nat.cast_mul, Int.natCast_natAbs]
  rw [h, abs_dvd]

lemma dvd_q (c : ℤ) (m : ℕ) : c ∣ ((c.natAbs * m : ℕ) : ℤ) := by
  rw [Nat.cast_mul, Int.natCast_natAbs]
  exact Dvd.dvd.mul_right ((dvd_abs c c).mpr dvd_rfl) _

lemma divc_congr {n c A B : ℤ} (hc : c ≠ 0) (hA : c ∣ A - n) (hB : c ∣ B - n)
    (hAB : ((c.natAbs * M : ℕ) : ℤ) ∣ A - B) :
    (((A - n) / c : ℤ) : ZMod M) = (((B - n) / c : ℤ) : ZMod M) := by
  obtain ⟨α, hα⟩ := hA
  obtain ⟨β, hβ⟩ := hB
  rw [hα, hβ, Int.mul_ediv_cancel_left _ hc, Int.mul_ediv_cancel_left _ hc,
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  rw [natAbs_mul_dvd_iff] at hAB
  have h1 : A - B = c * (α - β) := by linear_combination hα - hβ
  rw [h1] at hAB
  have h2 : (M : ℤ) ∣ α - β := (mul_dvd_mul_iff_left hc).mp hAB
  have h3 : β - α = -(α - β) := by ring
  rw [h3]
  exact dvd_neg.mpr h2

lemma intCast_val_zmod {q : ℕ} [NeZero q] (x : ZMod q) : (((x.val : ℤ)) : ZMod q) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

lemma intCast_val_castHom {q : ℕ} [NeZero q] (hMq : M ∣ q) (x : ZMod q) :
    (((x.val : ℤ)) : ZMod M) = ZMod.castHom hMq (ZMod M) x := by
  rw [Int.cast_natCast, ZMod.natCast_val, ZMod.castHom_apply]

/-- The summand of `dft_WcF_eq` at `j = 0`, `y = x + d`, in the `(x, d)` coordinates. -/
lemma term_eq (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q]
    (hq : q = c.natAbs * M) (hMq : M ∣ q) (x d : ZMod q) :
    (if c ∣ (x.val : ℤ) * (((x + d).val : ℤ) - x.val) - n then
        (S3.levelCount M δ' (mkT n (c, ((x + d).val : ℤ)) (x.val : ℤ)) : ℂ) else 0) =
      if Xc n c (x, d) then (Lbar M δ' (piM M n c hMq (x, d)) : ℂ) else 0 := by
  have hAB : ((c.natAbs * M : ℕ) : ℤ) ∣
      (x.val : ℤ) * (((x + d).val : ℤ) - x.val) - (x.val : ℤ) * d.val := by
    rw [← hq]
    have h : ((((x.val : ℤ) * d.val : ℤ)) : ZMod q) =
        ((((x.val : ℤ) * (((x + d).val : ℤ) - x.val) : ℤ)) : ZMod q) := by
      simp only [Int.cast_mul, Int.cast_sub, intCast_val_zmod]
      ring
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp h
  have hiff : c ∣ (x.val : ℤ) * (((x + d).val : ℤ) - x.val) - n ↔
      c ∣ (x.val : ℤ) * d.val - n := by
    have e : (x.val : ℤ) * (((x + d).val : ℤ) - x.val) - n =
        ((x.val : ℤ) * (((x + d).val : ℤ) - x.val) - (x.val : ℤ) * d.val) +
          ((x.val : ℤ) * d.val - n) := by ring
    rw [e]
    exact dvd_add_right ((dvd_q c M).trans hAB)
  by_cases hB : c ∣ (x.val : ℤ) * d.val - n
  · have hA := hiff.mpr hB
    rw [if_pos hA, if_pos (show Xc n c (x, d) from hB), levelCount_eq_Lbar]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j
    · show (((x.val : ℤ)) : ZMod M) = ZMod.castHom hMq (ZMod M) x
      exact intCast_val_castHom hMq x
    · show ((((x.val : ℤ) * (((x + d).val : ℤ) - x.val) - n) / c : ℤ) : ZMod M) =
        ((((x.val : ℤ) * d.val - n) / c : ℤ) : ZMod M)
      exact divc_congr hc hA hB hAB
    · rfl
    · show (((((x + d).val : ℤ) - x.val : ℤ)) : ZMod M) = ZMod.castHom hMq (ZMod M) d
      rw [Int.cast_sub, intCast_val_castHom hMq, intCast_val_castHom hMq, map_add]
      ring
  · rw [if_neg (mt hiff.mp hB), if_neg (show ¬ Xc n c (x, d) from hB)]

/-- **`μ_c` as a sum over `(ZMod q)²`** (`q = |c| M`). -/
theorem two_mul_muc_eq_sum (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q]
    (hq : q = c.natAbs * M) (hMq : M ∣ q) :
    2 * (M : ℂ) * ((q : ℂ) * muc M n δ' c) =
      ∑ z : ZMod q × ZMod q, if Xc n c z then (Lbar M δ' (piM M n c hMq z) : ℂ) else 0 := by
  have h := dft_WcF_eq n δ' hc hq 0
  rw [dft_val_apply (WcF M n δ' c)] at h
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul, mul_one] at h
  have hs : ∑ u ∈ range q, WcF M n δ' c (u : ℤ) = (q : ℂ) * muc M n δ' c := by
    subst hq
    exact sum_WcF_eq n δ' hc
  rw [← hs, h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft x)]
  exact Finset.sum_congr rfl fun d _ => term_eq n δ' hc hq hMq x d

end RamanujanPetersson.EllW2


