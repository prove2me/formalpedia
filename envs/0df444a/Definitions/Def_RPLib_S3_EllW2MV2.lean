-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV2
-- name    : RPLib_S3_EllW2MV2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:53:20.626211+00:00
-- url     : https://prove2.me/theorems/6560995c-0dc4-4134-a72b-aeb8a8c6347f
-- title:
--   The Eichler-Selberg trace formula in weight two: the moves of `(ZMod q)²` and their action on `piM`
-- statement:
--   The moves of `(ZMod q)²` and their action on `piM`.
--
--   * `fibC n c hMq G = #{z : Xc z ∧ piM z = G}`; `fibC_eq_of_equiv`: an equivalence `σ` of `(ZMod q)²` with
--     `Xc ∘ σ ↔ Xc` and `piM ∘ σ = ψ ∘ piM` (`ψ` injective) gives `fibC (ψ G) = fibC G`.
--   * `xc_piM_of_cast`: if `x̃'d̃' ≡ x̃d̃ + c t (mod q)` then `Xc z' ↔ Xc z` and `b' ≡ b + t (mod M)`.
--   * the moves: torus `σU u (x, d) = (u x, u⁻¹ d)` (`psiU`), left `σL k (x, d) = (x + k c, d)` (`psiL`),
--     right `σR k (x, d) = (x, d + k c)` (`psiR`), with `fibC_psiU`, `fibC_psiL`, `fibC_psiR`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV1

/-!
# S3-ES-Wt2 (O6, file MV2): the moves of `(ZMod q)²` and their action on `piM`

* `fibC n c hMq G = #{z : Xc z ∧ piM z = G}`; `fibC_eq_of_equiv`: an equivalence `σ` of `(ZMod q)²` with
  `Xc ∘ σ ↔ Xc` and `piM ∘ σ = ψ ∘ piM` (`ψ` injective) gives `fibC (ψ G) = fibC G`.
* `xc_piM_of_cast`: if `x̃'d̃' ≡ x̃d̃ + c t (mod q)` then `Xc z' ↔ Xc z` and `b' ≡ b + t (mod M)`.
* the moves: torus `σU u (x, d) = (u x, u⁻¹ d)` (`psiU`), left `σL k (x, d) = (x + k c, d)` (`psiL`),
  right `σR k (x, d) = (x, d + k c)` (`psiR`), with `fibC_psiU`, `fibC_psiL`, `fibC_psiR`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

variable {M : ℕ} [NeZero M]

lemma mat2_ext {R : Type*} {A B : Matrix (Fin 2) (Fin 2) R} (h00 : A 0 0 = B 0 0)
    (h01 : A 0 1 = B 0 1) (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

/-- The fibre count `#{z : Xc z ∧ piM z = G}`. -/
def fibC (M : ℕ) [NeZero M] (n c : ℤ) {q : ℕ} [NeZero q] (hMq : M ∣ q)
    (G : Matrix (Fin 2) (Fin 2) (ZMod M)) : ℕ :=
  (univ.filter fun z : ZMod q × ZMod q => Xc n c z ∧ piM M n c hMq z = G).card

lemma fibC_eq_of_equiv (n c : ℤ) {q : ℕ} [NeZero q] (hMq : M ∣ q)
    (σ : ZMod q × ZMod q ≃ ZMod q × ZMod q)
    (ψ : Matrix (Fin 2) (Fin 2) (ZMod M) → Matrix (Fin 2) (Fin 2) (ZMod M))
    (hψ : Function.Injective ψ) (hX : ∀ z, Xc n c (σ z) ↔ Xc n c z)
    (hπ : ∀ z, Xc n c z → piM M n c hMq (σ z) = ψ (piM M n c hMq z))
    (G : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    fibC M n c hMq (ψ G) = fibC M n c hMq G := by
  unfold fibC
  refine Finset.card_nbij' σ.symm σ ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    have h1 : Xc n c (σ (σ.symm w)) := by rw [Equiv.apply_symm_apply]; exact hw.2.1
    have hX' : Xc n c (σ.symm w) := (hX _).mp h1
    refine ⟨mem_univ _, hX', hψ ?_⟩
    rw [← hπ _ hX', Equiv.apply_symm_apply, hw.2.2]
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_filter] at hz ⊢
    exact ⟨mem_univ _, (hX z).mpr hz.2.1, by rw [hπ z hz.2.1, hz.2.2]⟩
  · intro w _
    exact σ.apply_symm_apply w
  · intro z _
    exact σ.symm_apply_apply z

lemma xc_piM_of_cast (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (z z' : ZMod q × ZMod q) (t : ℤ)
    (h : ((((z'.1.val : ℤ) * z'.2.val : ℤ)) : ZMod q) =
      ((((z.1.val : ℤ) * z.2.val + c * t : ℤ)) : ZMod q)) :
    (Xc n c z' ↔ Xc n c z) ∧ (Xc n c z →
      (((((z'.1.val : ℤ) * z'.2.val - n) / c : ℤ)) : ZMod M) =
        (((((z.1.val : ℤ) * z.2.val - n) / c : ℤ)) : ZMod M) + (t : ZMod M)) := by
  have hAB : ((c.natAbs * M : ℕ) : ℤ) ∣
      (z'.1.val : ℤ) * z'.2.val - ((z.1.val : ℤ) * z.2.val + c * t) := by
    rw [← hq]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp h.symm
  have hcq := (dvd_q c M).trans hAB
  have e1 : (z'.1.val : ℤ) * z'.2.val - n =
      ((z'.1.val : ℤ) * z'.2.val - ((z.1.val : ℤ) * z.2.val + c * t)) +
        (((z.1.val : ℤ) * z.2.val - n) + c * t) := by ring
  have hiff : c ∣ (z'.1.val : ℤ) * z'.2.val - n ↔ c ∣ (z.1.val : ℤ) * z.2.val - n := by
    rw [e1, dvd_add_right hcq, dvd_add_left (dvd_mul_right c t)]
  refine ⟨hiff, fun hz => ?_⟩
  have hz0 : c ∣ (z.1.val : ℤ) * z.2.val - n := hz
  have hz' : c ∣ (z'.1.val : ℤ) * z'.2.val - n := hiff.mpr hz0
  have e2 : ((z.1.val : ℤ) * z.2.val + c * t) - n = ((z.1.val : ℤ) * z.2.val - n) + t * c := by ring
  have hB : c ∣ ((z.1.val : ℤ) * z.2.val + c * t) - n := by
    rw [e2]; exact dvd_add hz0 (dvd_mul_left c t)
  rw [divc_congr hc hz' hB hAB, e2, Int.add_mul_ediv_right _ _ hc, Int.cast_add]

/-! ## The three moves -/

/-- Torus action on matrices. -/
def psiU (w : (ZMod M)ˣ) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  !![(w : ZMod M) * G 0 0, G 0 1; G 1 0, ((w⁻¹ : (ZMod M)ˣ) : ZMod M) * G 1 1]

/-- Left unipotent action `T^k · G`. -/
def psiL (k : ZMod M) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  !![G 0 0 + k * G 1 0, G 0 1 + k * G 1 1; G 1 0, G 1 1]

/-- Right unipotent action `G · T^k`. -/
def psiR (k : ZMod M) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  !![G 0 0, G 0 1 + k * G 0 0; G 1 0, G 1 1 + k * G 1 0]

lemma psiU_inj (w : (ZMod M)ˣ) : Function.Injective (psiU w) := by
  intro G G' h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [psiU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Units.mul_right_inj] at h00 h01 h10 h11
  exact mat2_ext h00 h01 h10 h11

lemma psiL_inj (k : ZMod M) : Function.Injective (psiL k) := by
  intro G G' h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [psiL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
  refine mat2_ext ?_ ?_ h10 h11
  · rw [h10] at h00; exact add_right_cancel h00
  · rw [h11] at h01; exact add_right_cancel h01

lemma psiR_inj (k : ZMod M) : Function.Injective (psiR k) := by
  intro G G' h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [psiR, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
  refine mat2_ext h00 ?_ h10 ?_
  · rw [h00] at h01; exact add_right_cancel h01
  · rw [h10] at h11; exact add_right_cancel h11

/-- The torus move `(x, d) ↦ (u x, u⁻¹ d)`. -/
def σU {q : ℕ} (u : (ZMod q)ˣ) : ZMod q × ZMod q ≃ ZMod q × ZMod q where
  toFun z := ((u : ZMod q) * z.1, ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * z.2)
  invFun z := (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * z.1, (u : ZMod q) * z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The left move `(x, d) ↦ (x + k c, d)`. -/
def σL {q : ℕ} (c k : ℤ) : ZMod q × ZMod q ≃ ZMod q × ZMod q where
  toFun z := (z.1 + ((k * c : ℤ) : ZMod q), z.2)
  invFun z := (z.1 - ((k * c : ℤ) : ZMod q), z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The right move `(x, d) ↦ (x, d + k c)`. -/
def σR {q : ℕ} (c k : ℤ) : ZMod q × ZMod q ≃ ZMod q × ZMod q where
  toFun z := (z.1, z.2 + ((k * c : ℤ) : ZMod q))
  invFun z := (z.1, z.2 - ((k * c : ℤ) : ZMod q))
  left_inv z := by simp
  right_inv z := by simp

lemma fibC_psiU (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (hMq : M ∣ q) (u : (ZMod q)ˣ) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    fibC M n c hMq (psiU (ZMod.unitsMap hMq u) G) = fibC M n c hMq G := by
  have key : ∀ z : ZMod q × ZMod q,
      (Xc n c (σU u z) ↔ Xc n c z) ∧ (Xc n c z →
        (((((σU u z).1.val : ℤ) * (σU u z).2.val - n) / c : ℤ) : ZMod M) =
          ((((z.1.val : ℤ) * z.2.val - n) / c : ℤ) : ZMod M) + ((0 : ℤ) : ZMod M)) := by
    intro z
    refine xc_piM_of_cast n hc hq z (σU u z) 0 ?_
    simp only [Int.cast_mul, Int.cast_add, mul_zero, Int.cast_zero, add_zero, intCast_val_zmod]
    show ((u : ZMod q) * z.1) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * z.2) = z.1 * z.2
    calc ((u : ZMod q) * z.1) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * z.2)
        = ((u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) * (z.1 * z.2) := by ring
      _ = z.1 * z.2 := by rw [Units.mul_inv, one_mul]
  refine fibC_eq_of_equiv n c hMq (σU u) _ (psiU_inj _) (fun z => (key z).1) (fun z hz => ?_) G
  refine mat2_ext ?_ ?_ rfl ?_
  · show ZMod.castHom hMq (ZMod M) ((u : ZMod q) * z.1) =
      ((ZMod.unitsMap hMq u : (ZMod M)ˣ) : ZMod M) * ZMod.castHom hMq (ZMod M) z.1
    rw [map_mul]; rfl
  · show (((((σU u z).1.val : ℤ) * (σU u z).2.val - n) / c : ℤ) : ZMod M) =
      ((((z.1.val : ℤ) * z.2.val - n) / c : ℤ) : ZMod M)
    rw [(key z).2 hz, Int.cast_zero, add_zero]
  · show ZMod.castHom hMq (ZMod M) (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * z.2) =
      (((ZMod.unitsMap hMq u)⁻¹ : (ZMod M)ˣ) : ZMod M) * ZMod.castHom hMq (ZMod M) z.2
    rw [map_mul, ← map_inv]; rfl

lemma fibC_psiL (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (hMq : M ∣ q) (k : ℤ) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    fibC M n c hMq (psiL (k : ZMod M) G) = fibC M n c hMq G := by
  have key : ∀ z : ZMod q × ZMod q,
      (Xc n c (σL c k z) ↔ Xc n c z) ∧ (Xc n c z →
        (((((σL c k z).1.val : ℤ) * (σL c k z).2.val - n) / c : ℤ) : ZMod M) =
          ((((z.1.val : ℤ) * z.2.val - n) / c : ℤ) : ZMod M) + ((k * z.2.val : ℤ) : ZMod M)) := by
    intro z
    refine xc_piM_of_cast n hc hq z (σL c k z) (k * z.2.val) ?_
    simp only [Int.cast_mul, Int.cast_add, intCast_val_zmod]
    show (z.1 + ((k * c : ℤ) : ZMod q)) * z.2 = z.1 * z.2 + (c : ZMod q) * ((k : ZMod q) * z.2)
    push_cast
    ring
  refine fibC_eq_of_equiv n c hMq (σL c k) _ (psiL_inj _) (fun z => (key z).1) (fun z hz => ?_) G
  refine mat2_ext ?_ ?_ rfl rfl
  · show ZMod.castHom hMq (ZMod M) (z.1 + ((k * c : ℤ) : ZMod q)) =
      ZMod.castHom hMq (ZMod M) z.1 + (k : ZMod M) * (c : ZMod M)
    rw [map_add, map_intCast, Int.cast_mul]
  · show (((((σL c k z).1.val : ℤ) * (σL c k z).2.val - n) / c : ℤ) : ZMod M) =
      ((((z.1.val : ℤ) * z.2.val - n) / c : ℤ) : ZMod M) + (k : ZMod M) * ZMod.castHom hMq (ZMod M) z.2
    rw [(key z).2 hz, Int.cast_mul, intCast_val_castHom hMq]

lemma fibC_psiR (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (hMq : M ∣ q) (k : ℤ) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    fibC M n c hMq (psiR (k : ZMod M) G) = fibC M n c hMq G := by
  have key : ∀ z : ZMod q × ZMod q,
      (Xc n c (σR c k z) ↔ Xc n c z) ∧ (Xc n c z →
        (((((σR c k z).1.val : ℤ) * (σR c k z).2.val - n) / c : ℤ) : ZMod M) =
          ((((z.1.val : ℤ) * z.2.val - n) / c : ℤ) : ZMod M) + ((k * z.1.val : ℤ) : ZMod M)) := by
    intro z
    refine xc_piM_of_cast n hc hq z (σR c k z) (k * z.1.val) ?_
    simp only [Int.cast_mul, Int.cast_add, intCast_val_zmod]
    show z.1 * (z.2 + ((k * c : ℤ) : ZMod q)) = z.1 * z.2 + (c : ZMod q) * ((k : ZMod q) * z.1)
    push_cast
    ring
  refine fibC_eq_of_equiv n c hMq (σR c k) _ (psiR_inj _) (fun z => (key z).1) (fun z hz => ?_) G
  refine mat2_ext rfl ?_ rfl ?_
  · show (((((σR c k z).1.val : ℤ) * (σR c k z).2.val - n) / c : ℤ) : ZMod M) =
      ((((z.1.val : ℤ) * z.2.val - n) / c : ℤ) : ZMod M) + (k : ZMod M) * ZMod.castHom hMq (ZMod M) z.1
    rw [(key z).2 hz, Int.cast_mul, intCast_val_castHom hMq]
  · show ZMod.castHom hMq (ZMod M) (z.2 + ((k * c : ℤ) : ZMod q)) =
      ZMod.castHom hMq (ZMod M) z.2 + (k : ZMod M) * (c : ZMod M)
    rw [map_add, map_intCast, Int.cast_mul]

end RamanujanPetersson.EllW2


