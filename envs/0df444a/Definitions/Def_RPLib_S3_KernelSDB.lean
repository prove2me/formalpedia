-- Prove2me | Definitions.Def_RPLib_S3_KernelSDB
-- name    : RPLib_S3_KernelSDB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:31:07.69519+00:00
-- url     : https://prove2.me/theorems/ae778810-48a9-4044-b0d3-98c18485f8be
-- title:
--   The Eichler-Selberg trace formula in weight two: the `Γ(M)` kernel `KG`, its `c = 0` block and its ERROR part
-- statement:
--   The `Γ(M)` kernel `KG`, its `c = 0` block and its ERROR part.
--
--   * `GamSet M` (`Γ(M)` as integer matrices), `KG M s z w = Σ_{g ∈ Γ(M)} Q(g;z,w)^-2 ratQ^s`, `summable_norm_KG`.
--   * `phiG : ℤ ⊕ Tset M → GamSet M` is a bijection (`M ≥ 3`): `j ↦ [[1, M j], [0, 1]]`,
--     `(c, a, d) ↦ [[a, (ad-1)/c], [c, d]]`.
--   * `KG_eq`: `KG = KG0 + Σ_{Tset} Fterm`, `KG0 = (yv/M²)^s M^-2 G_s((z+w)/M)`; `Fterm = Eterm + Mterm`.
--   * ERROR: `norm_Eterm_le`, `summable_maj` (uniform in `Re z`, factor `(y²)^(-1/4)`), `summable_Eterm`,
--     `norm_tsum_Eterm_le`, `tendsto_tsum_Eterm` (`s → 0+`).
--   * `KG_split`: `KG = KG0 + Σ Eterm + Σ Mterm` with `Mterm` summable (`0 < s ≤ 1`); `tendsto_KG0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDA
import Definitions.Def_RPLib_S3_KernelSB
import Definitions.Def_RPLib_S3_GSA

/-!
# S3-ES-Wt2, part KS_D (B): the `Γ(M)` kernel `KG`, its `c = 0` block and its ERROR part

* `GamSet M` (`Γ(M)` as integer matrices), `KG M s z w = Σ_{g ∈ Γ(M)} Q(g;z,w)^-2 ratQ^s`, `summable_norm_KG`.
* `phiG : ℤ ⊕ Tset M → GamSet M` is a bijection (`M ≥ 3`): `j ↦ [[1, M j], [0, 1]]`,
  `(c, a, d) ↦ [[a, (ad-1)/c], [c, d]]`.
* `KG_eq`: `KG = KG0 + Σ_{Tset} Fterm`, `KG0 = (yv/M²)^s M^-2 G_s((z+w)/M)`; `Fterm = Eterm + Mterm`.
* ERROR: `norm_Eterm_le`, `summable_maj` (uniform in `Re z`, factor `(y²)^(-1/4)`), `summable_Eterm`,
  `norm_tsum_Eterm_le`, `tendsto_tsum_Eterm` (`s → 0+`).
* `KG_split`: `KG = KG0 + Σ Eterm + Σ Mterm` with `Mterm` summable (`0 < s ≤ 1`); `tendsto_KG0`.
-/

open Complex Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

/-! ### The kernel `KG` -/

/-- `Γ(M)` as a set of integer matrices. -/
def GamSet (M : ℕ) : Set (Matrix (Fin 2) (Fin 2) ℤ) :=
  {g | g.det = 1 ∧ (M : ℤ) ∣ g 0 0 - 1 ∧ (M : ℤ) ∣ g 0 1 ∧ (M : ℤ) ∣ g 1 0 ∧ (M : ℤ) ∣ g 1 1 - 1}

def termG (s : ℝ) (z w : ℂ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ :=
  (Q g z w ^ 2)⁻¹ * ((ratQ g z w ^ s : ℝ) : ℂ)

def KG (M : ℕ) (s : ℝ) (z w : ℂ) : ℂ := ∑' g : GamSet M, termG s z w g.1

theorem summable_norm_KG (M : ℕ) {s : ℝ} (hs : 0 < s) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Summable fun g : GamSet M => ‖termG s z w g.1‖ := by
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
  have hinj : Function.Injective (fun g : GamSet M => (⟨g.1, g.2.1⟩ : DetSet 1)) :=
    fun a b h => Subtype.ext (congrArg (fun x : DetSet 1 => x.1) h :)
  refine (((summable_N_rpow (n := 1) one_pos hσ).comp_injective hinj).mul_left
    ((((1 : ℤ) : ℝ) * z.im * w.im) ^ s * B z w ^ (-(((2 : ℕ) : ℝ) / 2 + s)))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun g => ?_)
  have hd : g.1.det = 1 := g.2.1
  have hpos : 0 < g.1.det := by rw [hd]; exact one_pos
  have := norm_termS_le hpos hy hv 2 (s := s) (by norm_num; linarith)
  rw [hd, Real.mul_rpow (B_pos hy hv).le (N_pos hpos).le] at this
  simp only [termG, Function.comp_apply]
  exact this.trans_eq (by ring)

/-! ### The bijection `ℤ ⊕ Tset M → Γ(M)` -/

/-- Lower-left, upper-left, lower-right entries `(c, a, d)` of the `c ≠ 0` part of `Γ(M)`. -/
def Tset (M : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | p.1 ≠ 0 ∧ (M : ℤ) ∣ p.1 ∧ (M : ℤ) ∣ p.2.1 - 1 ∧ (M : ℤ) * p.1 ∣ p.2.1 * p.2.2 - 1}

def matU (M : ℕ) (j : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (M : ℤ) * j; 0, 1]

def matT (p : ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![p.2.1, (p.2.1 * p.2.2 - 1) / p.1; p.1, p.2.2]

lemma matU_apply (M : ℕ) (j : ℤ) :
    matU M j 0 0 = 1 ∧ matU M j 0 1 = M * j ∧ matU M j 1 0 = 0 ∧ matU M j 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

lemma matT_apply (p : ℤ × ℤ × ℤ) :
    matT p 0 0 = p.2.1 ∧ matT p 0 1 = (p.2.1 * p.2.2 - 1) / p.1 ∧ matT p 1 0 = p.1 ∧
      matT p 1 1 = p.2.2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

lemma det_matU (M : ℕ) (j : ℤ) : (matU M j).det = 1 := by
  simp [matU, Matrix.det_fin_two_of]

lemma det_matT {p : ℤ × ℤ × ℤ} (hcd : p.1 ∣ p.2.1 * p.2.2 - 1) : (matT p).det = 1 := by
  rw [matT, Matrix.det_fin_two_of, Int.ediv_mul_cancel hcd]; ring

lemma matU_mem (M : ℕ) (j : ℤ) : matU M j ∈ GamSet M := by
  obtain ⟨h1, h2, h3, h4⟩ := matU_apply M j
  refine ⟨det_matU M j, ?_, ?_, ?_, ?_⟩
  · rw [h1]; simp
  · rw [h2]; exact dvd_mul_right _ _
  · rw [h3]; exact dvd_zero _
  · rw [h4]; simp

lemma matT_mem {M : ℕ} {p : ℤ × ℤ × ℤ} (hp : p ∈ Tset M) : matT p ∈ GamSet M := by
  obtain ⟨hc, hMc, ha, k, hk⟩ := hp
  obtain ⟨e1, e2, e3, e4⟩ := matT_apply p
  have hb : (p.2.1 * p.2.2 - 1) / p.1 = M * k := by
    rw [hk, show (M : ℤ) * p.1 * k = p.1 * (M * k) by ring, Int.mul_ediv_cancel_left _ hc]
  have hcd : p.1 ∣ p.2.1 * p.2.2 - 1 := ⟨M * k, by rw [hk]; ring⟩
  refine ⟨det_matT hcd, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact ha
  · rw [e2, hb]; exact dvd_mul_right _ _
  · rw [e3]; exact hMc
  · have h1 : (M : ℤ) ∣ p.2.1 * p.2.2 - 1 := ⟨p.1 * k, by rw [hk]; ring⟩
    have h2 : (M : ℤ) ∣ (p.2.1 - 1) * p.2.2 := dvd_mul_of_dvd_left ha _
    have h3 := dvd_sub h1 h2
    rw [e4, show p.2.2 - 1 = p.2.1 * p.2.2 - 1 - (p.2.1 - 1) * p.2.2 by ring]
    exact h3

def phiG (M : ℕ) : ℤ ⊕ Tset M → GamSet M
  | .inl j => ⟨matU M j, matU_mem M j⟩
  | .inr p => ⟨matT p.1, matT_mem p.2⟩

lemma phiG_inl (M : ℕ) (j : ℤ) : (phiG M (.inl j)).1 = matU M j := rfl

lemma phiG_inr (M : ℕ) (p : Tset M) : (phiG M (.inr p)).1 = matT p.1 := rfl

lemma phiG_injective {M : ℕ} (hM : M ≠ 0) : Function.Injective (phiG M) := by
  rintro (j | ⟨p, hp⟩) (j' | ⟨p', hp'⟩) h <;> have h' := congrArg Subtype.val h <;>
    simp only [phiG_inl, phiG_inr] at h'
  · have e := congrArg (fun g : Matrix (Fin 2) (Fin 2) ℤ => g 0 1) h'
    simp only [(matU_apply M j).2.1, (matU_apply M j').2.1] at e
    exact congrArg Sum.inl (mul_left_cancel₀ (by exact_mod_cast hM) e)
  · have e := congrArg (fun g : Matrix (Fin 2) (Fin 2) ℤ => g 1 0) h'
    simp only [(matU_apply M j).2.2.1, (matT_apply p').2.2.1] at e
    exact absurd e.symm hp'.1
  · have e := congrArg (fun g : Matrix (Fin 2) (Fin 2) ℤ => g 1 0) h'
    simp only [(matU_apply M j').2.2.1, (matT_apply p).2.2.1] at e
    exact absurd e hp.1
  · have e1 := congrArg (fun g : Matrix (Fin 2) (Fin 2) ℤ => g 1 0) h'
    have e2 := congrArg (fun g : Matrix (Fin 2) (Fin 2) ℤ => g 0 0) h'
    have e3 := congrArg (fun g : Matrix (Fin 2) (Fin 2) ℤ => g 1 1) h'
    simp only [(matT_apply p).1, (matT_apply p').1, (matT_apply p).2.2.1, (matT_apply p').2.2.1,
      (matT_apply p).2.2.2, (matT_apply p').2.2.2] at e1 e2 e3
    exact congrArg Sum.inr (Subtype.ext (Prod.ext e1 (Prod.ext e2 e3)))

lemma phiG_surjective {M : ℕ} (hM : 3 ≤ M) : Function.Surjective (phiG M) := by
  rintro ⟨g, hdet, ha, hb, hc, _hd⟩
  have hdet' : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  by_cases hc0 : g 1 0 = 0
  · rw [hc0, mul_zero, sub_zero] at hdet'
    have ha1 : g 0 0 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet' with h | h
      · exact h
      · exfalso
        rw [h, show (-1 : ℤ) - 1 = -2 by norm_num, dvd_neg] at ha
        have := Int.le_of_dvd (by norm_num) ha
        omega
    have hd1 : g 1 1 = 1 := by rw [ha1, one_mul] at hdet'; exact hdet'
    obtain ⟨j, hj⟩ := hb
    refine ⟨Sum.inl j, Subtype.ext ?_⟩
    show matU M j = g
    rw [Matrix.eta_fin_two g, ha1, hj, hc0, hd1]
    rfl
  · obtain ⟨k, hk⟩ := hb
    have hbc : g 0 0 * g 1 1 - 1 = g 0 1 * g 1 0 := by linarith
    refine ⟨Sum.inr ⟨(g 1 0, g 0 0, g 1 1), hc0, hc, ha, ⟨k, ?_⟩⟩, Subtype.ext ?_⟩
    · show g 0 0 * g 1 1 - 1 = M * g 1 0 * k
      rw [hbc, hk]; ring
    · rw [phiG_inr]
      show !![g 0 0, (g 0 0 * g 1 1 - 1) / g 1 0; g 1 0, g 1 1] = g
      rw [hbc, Int.mul_ediv_cancel _ hc0]
      exact (Matrix.eta_fin_two g).symm

/-! ### The terms -/

lemma Q_matU (M : ℕ) (j : ℤ) (z w : ℂ) : Q (matU M j) z w = z + w + (M : ℂ) * j := by
  simp only [Q, (matU_apply M j).1, (matU_apply M j).2.1, (matU_apply M j).2.2.1, (matU_apply M j).2.2.2]
  push_cast; ring

/-- The `c = 0` block: `(yv/M²)^s M^-2 G_s((z+w)/M)`. -/
def KG0 (M : ℕ) (s : ℝ) (z w : ℂ) : ℂ :=
  (((z.im * w.im / (M : ℝ) ^ 2) ^ s : ℝ) : ℂ) * ((M : ℂ) ^ 2)⁻¹ * Gs s ((z + w) / M)

lemma termG_matU {M : ℕ} (hM : M ≠ 0) (s : ℝ) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) (j : ℤ) :
    termG s z w (matU M j) = (((z.im * w.im / (M : ℝ) ^ 2) ^ s : ℝ) : ℂ) * ((M : ℂ) ^ 2)⁻¹ *
      fS s ((z + w) / M).im (((z + w) / M).re + j) := by
  rw [fS_shift]
  have hMc : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  have hQ : Q (matU M j) z w = M * ((z + w) / M + j) := by
    rw [Q_matU]; field_simp
  have h0 : (M : ℂ) * ((z + w) / M + j) ≠ 0 := by
    rw [← hQ, Q_matU]; intro h
    have := congrArg Complex.im h
    simp at this; linarith
  have hN : 0 < normSq ((z + w) / M + j) := normSq_pos.mpr (right_ne_zero_of_mul h0)
  have hnorm : ‖(M : ℂ) * ((z + w) / M + j)‖ ^ 2 = (M : ℝ) ^ 2 * normSq ((z + w) / M + j) := by
    rw [norm_mul, mul_pow, Complex.norm_natCast, Complex.sq_norm]
  have hr : (((1 : ℤ) : ℝ) * z.im * w.im / ‖(M : ℂ) * ((z + w) / M + j)‖ ^ 2) ^ s
      = (z.im * w.im / (M : ℝ) ^ 2) ^ s * normSq ((z + w) / M + j) ^ (-s) := by
    rw [hnorm, Int.cast_one, one_mul, ← div_div,
      Real.div_rpow (div_nonneg (mul_pos hy hv).le (by positivity)) hN.le, Real.rpow_neg hN.le]
    ring
  unfold termG ratQ
  rw [hQ, det_matU, hr, Complex.ofReal_mul, mul_pow, mul_inv]
  ring

/-- `A = (c z + d)(c w + a)` and `η = c² y v`. -/
def AC (z w : ℂ) (p : ℤ × ℤ × ℤ) : ℂ := ((p.1 : ℂ) * z + p.2.2) * ((p.1 : ℂ) * w + p.2.1)

def etaC (z w : ℂ) (c : ℤ) : ℝ := (c : ℝ) ^ 2 * z.im * w.im

/-- The `(c, a, d)` term: `c² (A-1)^-2 (η/|A-1|²)^s`. -/
def Fterm (s : ℝ) (z w : ℂ) (p : ℤ × ℤ × ℤ) : ℂ :=
  (p.1 : ℂ) ^ 2 * (((AC z w p - 1) ^ 2)⁻¹ * (((etaC z w p.1 / ‖AC z w p - 1‖ ^ 2) ^ s : ℝ) : ℂ))

/-- MAIN: `c² A^-2 (η/|A|²)^s`. -/
def Mterm (s : ℝ) (z w : ℂ) (p : ℤ × ℤ × ℤ) : ℂ :=
  (p.1 : ℂ) ^ 2 * ((AC z w p ^ 2)⁻¹ * (((etaC z w p.1 / ‖AC z w p‖ ^ 2) ^ s : ℝ) : ℂ))

/-- ERROR: `c² Ferr`. -/
def Eterm (s : ℝ) (z w : ℂ) (p : ℤ × ℤ × ℤ) : ℂ := (p.1 : ℂ) ^ 2 * Ferr s (etaC z w p.1) (AC z w p)

lemma Fterm_eq (s : ℝ) (z w : ℂ) (p : ℤ × ℤ × ℤ) : Fterm s z w p = Eterm s z w p + Mterm s z w p := by
  unfold Fterm Eterm Mterm Ferr; ring

lemma Q_matT {p : ℤ × ℤ × ℤ} (hcd : p.1 ∣ p.2.1 * p.2.2 - 1) (z w : ℂ) :
    (p.1 : ℂ) * Q (matT p) z w = AC z w p - 1 := by
  have hbc : (((p.2.1 * p.2.2 - 1) / p.1 : ℤ) : ℂ) * p.1 = p.2.1 * p.2.2 - 1 := by
    exact_mod_cast Int.ediv_mul_cancel hcd
  simp only [Q, (matT_apply p).1, (matT_apply p).2.1, (matT_apply p).2.2.1, (matT_apply p).2.2.2, AC]
  linear_combination hbc

lemma termG_matT {p : ℤ × ℤ × ℤ} (hc : p.1 ≠ 0) (hcd : p.1 ∣ p.2.1 * p.2.2 - 1) (s : ℝ) (z w : ℂ) :
    termG s z w (matT p) = Fterm s z w p := by
  have hc' : (p.1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hQ : Q (matT p) z w = (AC z w p - 1) / p.1 := by
    rw [← Q_matT hcd z w]; field_simp
  have hr : ratQ (matT p) z w = etaC z w p.1 / ‖AC z w p - 1‖ ^ 2 := by
    unfold ratQ etaC
    rw [det_matT hcd, hQ, norm_div, Complex.norm_intCast, div_pow, sq_abs, div_div_eq_mul_div]
    push_cast; ring
  unfold termG Fterm
  rw [hr, hQ, div_pow, inv_div]
  ring

theorem KG_eq {M : ℕ} (hM : 3 ≤ M) {s : ℝ} (hs : 0 < s) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    KG M s z w = KG0 M s z w + ∑' p : Tset M, Fterm s z w p.1 := by
  have hM0 : M ≠ 0 := by omega
  have hsum : Summable (fun g : GamSet M => termG s z w g.1) := (summable_norm_KG M hs hy hv).of_norm
  have hsum' : Summable (fun x => termG s z w (phiG M x).1) := hsum.comp_injective (phiG_injective hM0)
  have key : KG M s z w = ∑' x, termG s z w (phiG M x).1 :=
    ((phiG_injective hM0).tsum_eq (f := fun g : GamSet M => termG s z w g.1)
      (fun g _ => phiG_surjective hM g)).symm
  rw [key, Summable.tsum_sum (hsum'.comp_injective Sum.inl_injective)
    (hsum'.comp_injective Sum.inr_injective)]
  congr 1
  · simp only [phiG_inl]
    rw [tsum_congr (fun j => termG_matU hM0 s hy hv j), tsum_mul_left]
    rfl
  · exact tsum_congr fun p => termG_matT p.2.1 (dvd_trans (dvd_mul_left _ _) p.2.2.2.2) s z w

/-! ### ERROR: pointwise bound -/

lemma im_lin (c d : ℤ) (z : ℂ) : ((c : ℂ) * z + d).im = c * z.im := by
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]; ring

lemma AC_facts {c a d : ℤ} (hc : c ≠ 0) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    z.im * w.im ≤ etaC z w c ∧ etaC z w c ≤ ‖AC z w (c, a, d)‖ ∧
      2 * etaC z w c ≤ ‖AC z w (c, a, d) - 1‖ ^ 2 := by
  have hA : AC z w (c, a, d) = ((c : ℂ) * z + d) * ((c : ℂ) * w + a) := rfl
  have hc1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    nlinarith [sq_abs (c : ℝ), abs_nonneg (c : ℝ)]
  have hη : etaC z w c = |((c : ℂ) * z + d).im| * |((c : ℂ) * w + a).im| := by
    rw [im_lin, im_lin, abs_mul, abs_mul, abs_of_pos hy, abs_of_pos hv]
    unfold etaC; rw [← sq_abs (c : ℝ)]; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold etaC; nlinarith [mul_nonneg (sub_nonneg.2 hc1) (mul_pos hy hv).le]
  · rw [hη, hA, norm_mul]
    exact mul_le_mul (Complex.abs_im_le_norm _) (Complex.abs_im_le_norm _) (abs_nonneg _) (norm_nonneg _)
  · have h := normSq_mul_sub_one_ge ((c : ℂ) * z + d) ((c : ℂ) * w + a)
    rw [Complex.normSq_eq_norm_sq, im_lin, im_lin] at h
    rw [hA]; refine le_trans (le_of_eq ?_) h
    unfold etaC; ring

/-- The majorant `c² |cz+d|^-3 |cw+a|^-3`, indexed by `((c, d), a)`. -/
def maj (z w : ℂ) (q : (ℤ × ℤ) × ℤ) : ℝ :=
  (q.1.1 : ℝ) ^ 2 * (‖(q.1.1 : ℂ) * z + q.1.2‖ ^ 3)⁻¹ * (‖(q.1.1 : ℂ) * w + q.2‖ ^ 3)⁻¹

lemma maj_nonneg (z w : ℂ) (q : (ℤ × ℤ) × ℤ) : 0 ≤ maj z w q := by unfold maj; positivity

/-- `(c, a, d) ↦ ((c, d), a)`. -/
def iota (p : ℤ × ℤ × ℤ) : (ℤ × ℤ) × ℤ := ((p.1, p.2.2), p.2.1)

lemma iota_injective : Function.Injective iota := by
  rintro ⟨c, a, d⟩ ⟨c', a', d'⟩ h
  simp only [iota, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

lemma Kerr_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ Kerr t := by
  unfold Kerr
  have h1 : 0 ≤ max 1 t⁻¹ := le_trans zero_le_one (le_max_left _ _)
  have h2 : 0 ≤ (2 * t)⁻¹ := by positivity
  have h3 : 0 ≤ max 1 t⁻¹ / t ^ 2 := div_nonneg h1 (sq_nonneg _)
  linarith

theorem norm_Eterm_le {c a d : ℤ} (hc : c ≠ 0) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) (ht : 0 < t) (hty : t ≤ z.im * w.im) :
    ‖Eterm s z w (c, a, d)‖ ≤ Kerr t * maj z w ((c, d), a) := by
  obtain ⟨h1, h2, h3⟩ := AC_facts (a := a) (d := d) hc hy hv
  have hF := norm_Ferr_le ht (hty.trans h1) h2 h3 hs0 hs1
  have e1 : ‖Eterm s z w (c, a, d)‖ = (c : ℝ) ^ 2 * ‖Ferr s (etaC z w c) (AC z w (c, a, d))‖ := by
    simp only [Eterm]; rw [norm_mul, norm_pow, Complex.norm_intCast, sq_abs]
  have hA : AC z w (c, a, d) = ((c : ℂ) * z + d) * ((c : ℂ) * w + a) := rfl
  rw [e1]
  calc (c : ℝ) ^ 2 * ‖Ferr s (etaC z w c) (AC z w (c, a, d))‖
      ≤ (c : ℝ) ^ 2 * (Kerr t * (‖AC z w (c, a, d)‖ ^ 3)⁻¹) := mul_le_mul_of_nonneg_left hF (sq_nonneg _)
    _ = Kerr t * maj z w ((c, d), a) := by
        rw [hA, norm_mul, mul_pow, mul_inv]; simp only [maj]; ring

lemma norm_Eterm_le' {M : ℕ} (p : Tset M) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) (ht : 0 < t) (hty : t ≤ z.im * w.im) :
    ‖Eterm s z w p.1‖ ≤ Kerr t * maj z w (iota p.1) := by
  obtain ⟨⟨c, a, d⟩, hp⟩ := p
  exact norm_Eterm_le hp.1 hs0 hs1 hy hv ht hty

/-! ### ERROR: the lattice majorant -/

lemma S1_nonneg : 0 ≤ S1 := tsum_nonneg fun _ => Real.rpow_nonneg (sq_nonneg _) _

lemma S2_nonneg : 0 ≤ S2 := tsum_nonneg fun _ => Real.rpow_nonneg (sq_nonneg _) _

/-- `Kv v = (min v (1/2))^(-3/2) S1`. -/
def Kv (v : ℝ) : ℝ := ((min v (1 / 2)) ^ 2) ^ (-(3 / 4 : ℝ)) * S1

lemma Kv_nonneg (v : ℝ) : 0 ≤ Kv v := mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _) S1_nonneg

/-- `Kz z w = Kv v · v^(-3/2) · y^(-1/2)`. -/
def Kz (z w : ℂ) : ℝ := Kv w.im * (w.im ^ 2) ^ (-(3 / 4 : ℝ)) * (z.im ^ 2) ^ (-(1 / 4 : ℝ))

lemma Kz_nonneg (z w : ℂ) : 0 ≤ Kz z w :=
  mul_nonneg (mul_nonneg (Kv_nonneg _) (Real.rpow_nonneg (sq_nonneg _) _)) (Real.rpow_nonneg (sq_nonneg _) _)

lemma inv_pow_three_eq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 3)⁻¹ = (x ^ 2) ^ (-(3 / 4 : ℝ)) * (x ^ 2) ^ (-(3 / 4 : ℝ)) := by
  rw [← Real.rpow_add' (sq_nonneg x) (by norm_num), ← Real.rpow_natCast x 2, ← Real.rpow_mul hx,
    show ((2 : ℕ) : ℝ) * (-(3 / 4 : ℝ) + -(3 / 4)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx,
    Real.rpow_natCast]

lemma norm_sq_lin (c a : ℤ) (w : ℂ) :
    ‖(c : ℂ) * w + a‖ ^ 2 = ((c : ℝ) * w.re + a) ^ 2 + (|(c : ℝ)| * w.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, sq_abs]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im]
  ring

theorem sum_a {c : ℤ} (hc : c ≠ 0) {w : ℂ} (hv : 0 < w.im) :
    Summable (fun a : ℤ => (‖(c : ℂ) * w + a‖ ^ 3)⁻¹) ∧
      ∑' a : ℤ, (‖(c : ℂ) * w + a‖ ^ 3)⁻¹ ≤ ((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) * Kv w.im := by
  have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc
  have hh : 0 < |(c : ℝ)| * w.im := mul_pos (by linarith) hv
  obtain ⟨hS, hT⟩ := sum1D ((c : ℝ) * w.re) (|(c : ℝ)| * w.im) hh
  have hpt : ∀ a : ℤ, (‖(c : ℂ) * w + a‖ ^ 3)⁻¹ ≤ ((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) *
      (((c : ℝ) * w.re + a) ^ 2 + (|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) := by
    intro a
    rw [inv_pow_three_eq (norm_nonneg _), norm_sq_lin]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (pow_pos hh 2)
      (le_add_of_nonneg_left (sq_nonneg _)) (by norm_num)) (Real.rpow_nonneg (by positivity) _)
  have hS' := hS.mul_left (((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)))
  have hsum : Summable (fun a : ℤ => (‖(c : ℂ) * w + a‖ ^ 3)⁻¹) :=
    hS'.of_nonneg_of_le (fun a => by positivity) hpt
  refine ⟨hsum, ?_⟩
  have hmin : (min w.im (1 / 2)) ^ 2 ≤ (min (|(c : ℝ)| * w.im) (1 / 2)) ^ 2 := by
    have h0 : 0 ≤ min w.im (1 / 2) := le_min hv.le (by norm_num)
    have h1 : min w.im (1 / 2) ≤ min (|(c : ℝ)| * w.im) (1 / 2) :=
      min_le_min (le_mul_of_one_le_left hv.le hc1) le_rfl
    nlinarith
  have hK : ((min (|(c : ℝ)| * w.im) (1 / 2)) ^ 2) ^ (-(3 / 4 : ℝ)) * S1 ≤ Kv w.im :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos
      (pow_pos (lt_min hv (by norm_num)) 2) hmin (by norm_num)) S1_nonneg
  calc ∑' a : ℤ, (‖(c : ℂ) * w + a‖ ^ 3)⁻¹
      ≤ ∑' a : ℤ, ((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) *
          (((c : ℝ) * w.re + a) ^ 2 + (|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) :=
        Summable.tsum_le_tsum hpt hsum hS'
    _ = ((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) *
          ∑' a : ℤ, (((c : ℝ) * w.re + a) ^ 2 + (|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) := tsum_mul_left
    _ ≤ ((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) * Kv w.im :=
        mul_le_mul_of_nonneg_left (hT.trans hK) (Real.rpow_nonneg (sq_nonneg _) _)

lemma key_zfac {C P v y : ℝ} (hC : 0 < C) (hy : 0 < y) (hP : C ^ 2 * y ^ 2 ≤ P) :
    C ^ 2 * (P ^ (-(3 / 4 : ℝ)) * P ^ (-(3 / 4 : ℝ))) * ((C * v) ^ 2) ^ (-(3 / 4 : ℝ)) ≤
      (v ^ 2) ^ (-(3 / 4 : ℝ)) * (y ^ 2) ^ (-(1 / 4 : ℝ)) * P ^ (-(5 / 4 : ℝ)) := by
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have e1 : ((C * v) ^ 2) ^ (-(3 / 4 : ℝ)) = (C ^ 2) ^ (-(3 / 4 : ℝ)) * (v ^ 2) ^ (-(3 / 4 : ℝ)) := by
    rw [mul_pow, Real.mul_rpow (sq_nonneg _) (sq_nonneg _)]
  have e2 : (C ^ 2) ^ (1 / 4 : ℝ) = C ^ 2 * (C ^ 2) ^ (-(3 / 4 : ℝ)) := by
    rw [show (1 / 4 : ℝ) = 1 + (-(3 / 4)) by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
  have e3 : P ^ (-(3 / 4 : ℝ)) * P ^ (-(3 / 4 : ℝ)) = P ^ (-(1 / 4 : ℝ)) * P ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hP0, ← Real.rpow_add hP0]; norm_num
  have hCP : C ^ 2 ≤ P / y ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hP
  have h1 : (C ^ 2) ^ (1 / 4 : ℝ) * P ^ (-(1 / 4 : ℝ)) ≤ (y ^ 2) ^ (-(1 / 4 : ℝ)) := by
    calc (C ^ 2) ^ (1 / 4 : ℝ) * P ^ (-(1 / 4 : ℝ)) ≤ (P / y ^ 2) ^ (1 / 4 : ℝ) * P ^ (-(1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (sq_nonneg _) hCP (by norm_num))
            (Real.rpow_nonneg hP0.le _)
      _ = (y ^ 2) ^ (-(1 / 4 : ℝ)) * (P ^ (1 / 4 : ℝ) * P ^ (-(1 / 4 : ℝ))) := by
          rw [Real.div_rpow hP0.le (sq_nonneg _), Real.rpow_neg (sq_nonneg y)]; ring
      _ = (y ^ 2) ^ (-(1 / 4 : ℝ)) := by rw [← Real.rpow_add hP0]; norm_num
  calc C ^ 2 * (P ^ (-(3 / 4 : ℝ)) * P ^ (-(3 / 4 : ℝ))) * ((C * v) ^ 2) ^ (-(3 / 4 : ℝ))
      = (v ^ 2) ^ (-(3 / 4 : ℝ)) * P ^ (-(5 / 4 : ℝ)) *
          ((C ^ 2) ^ (1 / 4 : ℝ) * P ^ (-(1 / 4 : ℝ))) := by rw [e1, e3, e2]; ring
    _ ≤ (v ^ 2) ^ (-(3 / 4 : ℝ)) * P ^ (-(5 / 4 : ℝ)) * (y ^ 2) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1
          (mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _) (Real.rpow_nonneg hP0.le _))
    _ = _ := by ring

theorem sum_maj_inner {c d : ℤ} (hc : c ≠ 0) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Summable (fun a : ℤ => maj z w ((c, d), a)) ∧
      ∑' a : ℤ, maj z w ((c, d), a) ≤ Kz z w * (‖(c : ℂ) * z + d‖ ^ 2) ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨hS, hT⟩ := sum_a (w := w) hc hv
  have hC : 0 < |(c : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hc)
  have hmaj : (fun a : ℤ => maj z w ((c, d), a)) =
      fun a : ℤ => ((c : ℝ) ^ 2 * (‖(c : ℂ) * z + d‖ ^ 3)⁻¹) * (‖(c : ℂ) * w + a‖ ^ 3)⁻¹ := by
    funext a; rfl
  rw [hmaj, tsum_mul_left]
  refine ⟨hS.mul_left _, ?_⟩
  have hP : |(c : ℝ)| ^ 2 * z.im ^ 2 ≤ ‖(c : ℂ) * z + d‖ ^ 2 := by
    have := Complex.abs_im_le_norm ((c : ℂ) * z + d)
    rw [im_lin, abs_mul, abs_of_pos hy] at this
    nlinarith [mul_pos hC hy, norm_nonneg ((c : ℂ) * z + d)]
  have key := key_zfac (v := w.im) hC hy hP
  calc (c : ℝ) ^ 2 * (‖(c : ℂ) * z + d‖ ^ 3)⁻¹ * ∑' a : ℤ, (‖(c : ℂ) * w + a‖ ^ 3)⁻¹
      ≤ (c : ℝ) ^ 2 * (‖(c : ℂ) * z + d‖ ^ 3)⁻¹ * (((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ)) * Kv w.im) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (|(c : ℝ)| ^ 2 * ((‖(c : ℂ) * z + d‖ ^ 2) ^ (-(3 / 4 : ℝ)) * (‖(c : ℂ) * z + d‖ ^ 2) ^ (-(3 / 4 : ℝ))) *
          ((|(c : ℝ)| * w.im) ^ 2) ^ (-(3 / 4 : ℝ))) * Kv w.im := by
        rw [sq_abs, ← inv_pow_three_eq (norm_nonneg _)]; ring
    _ ≤ ((w.im ^ 2) ^ (-(3 / 4 : ℝ)) * (z.im ^ 2) ^ (-(1 / 4 : ℝ)) *
          (‖(c : ℂ) * z + d‖ ^ 2) ^ (-(5 / 4 : ℝ))) * Kv w.im :=
        mul_le_mul_of_nonneg_right key (Kv_nonneg _)
    _ = Kz z w * (‖(c : ℂ) * z + d‖ ^ 2) ^ (-(5 / 4 : ℝ)) := by unfold Kz; ring

/-- **The ERROR majorant** is summable, with a bound uniform in `Re z` (`y0 ≤ Im z`). -/
theorem summable_maj {z w : ℂ} {y0 : ℝ} (hy0 : 0 < y0) (hy : y0 ≤ z.im) (hv : 0 < w.im) :
    Summable (maj z w) ∧ ∑' q, maj z w q ≤ Kz z w * ((min (1 / 4) (y0 ^ 2)) ^ (-(5 / 4 : ℝ)) * S2) := by
  have hyz : 0 < z.im := hy0.trans_le hy
  obtain ⟨h2S, h2T⟩ := sum2D hy0 hy
  have hin : ∀ x : ℤ × ℤ, Summable (fun a : ℤ => maj z w (x, a)) ∧
      ∑' a : ℤ, maj z w (x, a) ≤ Kz z w * (‖(x.1 : ℂ) * z + x.2‖ ^ 2) ^ (-(5 / 4 : ℝ)) := by
    rintro ⟨c, d⟩
    by_cases hc : c = 0
    · subst hc
      have h0 : (fun a : ℤ => maj z w ((0, d), a)) = fun _ => 0 := by funext a; simp [maj]
      rw [h0, tsum_zero]
      exact ⟨summable_zero, mul_nonneg (Kz_nonneg _ _) (Real.rpow_nonneg (sq_nonneg _) _)⟩
    · exact sum_maj_inner hc hyz hv
  have hout : Summable (fun x : ℤ × ℤ => ∑' a : ℤ, maj z w (x, a)) :=
    (h2S.mul_left (Kz z w)).of_nonneg_of_le (fun x => tsum_nonneg fun a => maj_nonneg z w _)
      (fun x => (hin x).2)
  have hsum : Summable (maj z w) :=
    (summable_prod_of_nonneg (fun q => maj_nonneg z w q)).mpr ⟨fun x => (hin x).1, hout⟩
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_prod' (fun x => (hin x).1)]
  calc ∑' x : ℤ × ℤ, ∑' a : ℤ, maj z w (x, a)
      ≤ ∑' x : ℤ × ℤ, Kz z w * (‖(x.1 : ℂ) * z + x.2‖ ^ 2) ^ (-(5 / 4 : ℝ)) :=
        Summable.tsum_le_tsum (fun x => (hin x).2) hout (h2S.mul_left _)
    _ = Kz z w * ∑' x : ℤ × ℤ, (‖(x.1 : ℂ) * z + x.2‖ ^ 2) ^ (-(5 / 4 : ℝ)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left h2T (Kz_nonneg _ _)

theorem summable_Eterm (M : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (ht : 0 < t) (hty : t ≤ z.im * w.im) :
    Summable (fun p : Tset M => ‖Eterm s z w p.1‖) := by
  have hm := ((summable_maj hy le_rfl hv).1.comp_injective iota_injective).comp_injective
    (Subtype.val_injective (p := fun p => p ∈ Tset M))
  exact (hm.mul_left (Kerr t)).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_Eterm_le' p hs0 hs1 hy hv ht hty)

/-- **ERROR bound**, uniform in `Re z` for `Im z ≥ y0`. -/
theorem norm_tsum_Eterm_le (M : ℕ) {s t y0 : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy0 : 0 < y0)
    (hy : y0 ≤ z.im) (hv : 0 < w.im) (ht : 0 < t) (hty : t ≤ z.im * w.im) :
    ‖∑' p : Tset M, Eterm s z w p.1‖ ≤
      Kerr t * (Kz z w * ((min (1 / 4) (y0 ^ 2)) ^ (-(5 / 4 : ℝ)) * S2)) := by
  have hyz : 0 < z.im := hy0.trans_le hy
  obtain ⟨hS, hT⟩ := summable_maj hy0 hy hv
  have hm := (hS.comp_injective iota_injective).comp_injective
    (Subtype.val_injective (p := fun p => p ∈ Tset M))
  calc ‖∑' p : Tset M, Eterm s z w p.1‖ ≤ ∑' p : Tset M, ‖Eterm s z w p.1‖ :=
        norm_tsum_le_tsum_norm (summable_Eterm M hs0 hs1 hyz hv ht hty)
    _ ≤ ∑' p : Tset M, Kerr t * maj z w (iota p.1) :=
        Summable.tsum_le_tsum (fun p => norm_Eterm_le' p hs0 hs1 hyz hv ht hty)
          (summable_Eterm M hs0 hs1 hyz hv ht hty) (hm.mul_left _)
    _ = Kerr t * ∑' p : Tset M, maj z w (iota p.1) := tsum_mul_left
    _ ≤ Kerr t * ∑' q, maj z w q :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hS (maj_nonneg z w)
          (iota_injective.comp Subtype.val_injective)) (Kerr_nonneg ht)
    _ ≤ _ := mul_le_mul_of_nonneg_left hT (Kerr_nonneg ht)

lemma tendsto_Ferr {η : ℝ} {A : ℂ} (h1 : η / ‖A - 1‖ ^ 2 ≠ 0) (h2 : η / ‖A‖ ^ 2 ≠ 0) :
    Tendsto (fun s => Ferr s η A) (𝓝[>] 0) (𝓝 (Ferr 0 η A)) := by
  have k1 := ((Real.continuousAt_const_rpow (b := 0) h1).tendsto).ofReal
  have k2 := ((Real.continuousAt_const_rpow (b := 0) h2).tendsto).ofReal
  unfold Ferr
  exact ((k1.const_mul _).sub (k2.const_mul _)).mono_left nhdsWithin_le_nhds

/-- **ERROR limit** `s → 0+` (dominated convergence). -/
theorem tendsto_tsum_Eterm (M : ℕ) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Tendsto (fun s => ∑' p : Tset M, Eterm s z w p.1) (𝓝[>] 0)
      (𝓝 (∑' p : Tset M, Eterm 0 z w p.1)) := by
  have ht : 0 < z.im * w.im := mul_pos hy hv
  have hm := ((summable_maj hy le_rfl hv).1.comp_injective iota_injective).comp_injective
    (Subtype.val_injective (p := fun p => p ∈ Tset M))
  refine tendsto_tsum_of_dominated_convergence (hm.mul_left (Kerr (z.im * w.im))) (fun p => ?_) ?_
  · obtain ⟨⟨c, a, d⟩, hp⟩ := p
    obtain ⟨h1, h2, h3⟩ := AC_facts (a := a) (d := d) hp.1 hy hv
    have hη : 0 < etaC z w c := ht.trans_le h1
    exact (tendsto_Ferr (div_pos hη (by linarith)).ne'
      (div_pos hη (pow_pos (hη.trans_le h2) 2)).ne').const_mul _
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs p
    exact norm_Eterm_le' p hs.1.le hs.2.le hy hv ht le_rfl

/-! ### The split `KG = KG0 + ERROR + MAIN` -/

theorem KG_split {M : ℕ} (hM : 3 ≤ M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) :
    Summable (fun p : Tset M => Mterm s z w p.1) ∧
      KG M s z w = KG0 M s z w + ∑' p : Tset M, Eterm s z w p.1 + ∑' p : Tset M, Mterm s z w p.1 := by
  have hM0 : M ≠ 0 := by omega
  have hF : Summable (fun p : Tset M => Fterm s z w p.1) := by
    have hsum : Summable (fun g : GamSet M => termG s z w g.1) := (summable_norm_KG M hs hy hv).of_norm
    have h2 : Summable (fun p : Tset M => termG s z w (phiG M (Sum.inr p)).1) :=
      (hsum.comp_injective (phiG_injective hM0)).comp_injective Sum.inr_injective
    exact h2.congr fun p => termG_matT p.2.1 (dvd_trans (dvd_mul_left _ _) p.2.2.2.2) s z w
  have hE : Summable (fun p : Tset M => Eterm s z w p.1) :=
    (summable_Eterm M hs.le hs1 hy hv (mul_pos hy hv) le_rfl).of_norm
  have hMs : Summable (fun p : Tset M => Mterm s z w p.1) :=
    (hF.sub hE).congr fun p => by simp only [Fterm_eq]; ring
  refine ⟨hMs, ?_⟩
  rw [KG_eq hM hs hy hv, add_assoc, ← hE.tsum_add hMs]
  congr 1
  exact tsum_congr fun p => Fterm_eq s z w p.1

theorem tendsto_KG0 (M : ℕ) [NeZero M] {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Tendsto (fun s => KG0 M s z w) (𝓝[>] 0) (𝓝 (KG0 M 0 z w)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hb : z.im * w.im / (M : ℝ) ^ 2 ≠ 0 := (div_pos (mul_pos hy hv) (pow_pos hMr 2)).ne'
  have hζ : 0 < ((z + w) / (M : ℂ)).im := by
    rw [Complex.div_natCast_im, Complex.add_im]; exact div_pos (add_pos hy hv) hMr
  have k1 := (((Real.continuousAt_const_rpow (b := 0) hb).tendsto).ofReal).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi 0))
  unfold KG0
  exact (k1.mul_const _).mul (tendsto_Gs hζ)

end RamanujanPetersson.KernelSD


