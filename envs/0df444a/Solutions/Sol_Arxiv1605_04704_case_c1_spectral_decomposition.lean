-- Prove2me | solution 1 for Arxiv1605_04704.case_c1_spectral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:36:29.867505+00:00
-- url     : https://prove2.me/submissions/80192180-2040-4594-a713-2e427d8e72d9

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace S79MO
open Arxiv1605_04704

def mOf (H : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(H 0 0 + H 1 1 + H 2 2 + H 3 3).re, (H 0 0 - H 1 1 + H 2 2 - H 3 3).re,
      2 * (H 0 1 + H 2 3).re, 2 * (H 0 1 + H 2 3).im;
    (H 0 0 + H 1 1 - H 2 2 - H 3 3).re, (H 0 0 - H 1 1 - H 2 2 + H 3 3).re,
      2 * (H 0 1 - H 2 3).re, 2 * (H 0 1 - H 2 3).im;
    2 * (H 0 2 + H 1 3).re, 2 * (H 0 2 - H 1 3).re, 2 * (H 0 3 + H 1 2).re,
      2 * ((H 0 3).im - (H 1 2).im);
    -2 * (H 0 2 + H 1 3).im, -2 * (H 0 2 - H 1 3).im, -2 * ((H 0 3).im + (H 1 2).im),
      2 * (H 0 3 - H 1 2).re]

lemma mOf_coh (A : Matrix (Fin 4) (Fin 4) ℝ) : mOf (cohMat A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mOf, cohMat] <;> ring

lemma coh_mOf (H : Matrix (Fin 4) (Fin 4) ℂ) (hH : H.IsHermitian) : cohMat (mOf H) = H := by
  have hr : ∀ i j, (H i j).re = (H j i).re := fun i j => by
    rw [← hH.apply i j]; simp
  have hi : ∀ i j, (H i j).im = -(H j i).im := fun i j => by
    rw [← hH.apply i j]; simp
  have d0 := hi 0 0; have d1 := hi 1 1; have d2 := hi 2 2; have d3 := hi 3 3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mOf, cohMat, Complex.ext_iff] <;>
    constructor <;> linarith [hr 0 1, hr 0 2, hr 0 3, hr 1 2, hr 1 3, hr 2 3,
      hi 0 1, hi 0 2, hi 0 3, hi 1 2, hi 1 3, hi 2 3]

lemma coh_inj : Function.Injective cohMat := fun A B h => by
  rw [← mOf_coh A, h, mOf_coh]

lemma muellerOf_eq (H : Matrix (Fin 4) (Fin 4) ℂ) (hH : H.IsHermitian) : muellerOf H = mOf H := by
  conv_lhs => rw [← coh_mOf H hH]
  exact Function.leftInverse_invFun coh_inj (mOf H)

lemma mOf_add (H K : Matrix (Fin 4) (Fin 4) ℂ) : mOf (H + K) = mOf H + mOf K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mOf] <;> ring

lemma mOf_smul (r : ℝ) (H : Matrix (Fin 4) (Fin 4) ℂ) : mOf ((r : ℂ) • H) = r • mOf H := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mOf] <;> ring


variable (U : Matrix.unitaryGroup (Fin 4) ℂ)

def G (d : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (U : Matrix (Fin 4) (Fin 4) ℂ) * diagonal (fun i => ((d i : ℝ) : ℂ)) * star (U : Matrix (Fin 4) (Fin 4) ℂ)

def F (d : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := mOf (G U d)

lemma G_herm (d : Fin 4 → ℝ) : (G U d).IsHermitian := by
  unfold G
  rw [Matrix.star_eq_conjTranspose]
  apply isHermitian_mul_mul_conjTranspose
  apply isHermitian_diagonal_of_self_adjoint
  ext i; simp

lemma G_add (d e : Fin 4 → ℝ) : G U (d + e) = G U d + G U e := by
  unfold G
  have : diagonal (fun i => (((d + e) i : ℝ) : ℂ)) =
      diagonal (fun i => ((d i : ℝ) : ℂ)) + diagonal (fun i => ((e i : ℝ) : ℂ)) := by
    rw [diagonal_add]; congr 1; funext i; simp
  rw [this, Matrix.mul_add, Matrix.add_mul]

lemma G_smul (r : ℝ) (d : Fin 4 → ℝ) : G U (r • d) = (r : ℂ) • G U d := by
  unfold G
  have : diagonal (fun i => (((r • d) i : ℝ) : ℂ)) = (r : ℂ) • diagonal (fun i => ((d i : ℝ) : ℂ)) := by
    rw [← diagonal_smul]; congr 1; funext i; simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

lemma F_add (d e : Fin 4 → ℝ) : F U (d + e) = F U d + F U e := by
  simp [F, G_add, mOf_add]

lemma F_smul (r : ℝ) (d : Fin 4 → ℝ) : F U (r • d) = r • F U d := by
  rw [F, F, G_smul, mOf_smul]

lemma F_sub (d e : Fin 4 → ℝ) : F U (d - e) = F U d - F U e := by
  rw [sub_eq_add_neg, F_add, show -e = (-1 : ℝ) • e by simp, F_smul]; simp [sub_eq_add_neg]

lemma G_one (r : ℝ) : G U (fun _ => r) = (r : ℂ) • 1 := by
  unfold G
  have : diagonal (fun _ : Fin 4 => ((r : ℝ) : ℂ)) = (r : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    rw [← diagonal_one, ← diagonal_smul]; congr 1; funext; simp
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mem_unitaryGroup_iff.mp U.2]

lemma idealDepol_eq (c : ℝ) : idealDepol c = F U (fun _ => c / 4) := by
  rw [F, G_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mOf, idealDepol] <;> ring

lemma specComp_eq (c : ℝ) (i : Fin 4) : specComp U c i = F U (c • Pi.single i 1) := by
  have h : ((c : ℝ) : ℂ) • Matrix.vecMulVec (fun a => (U : Matrix (Fin 4) (Fin 4) ℂ) a i)
      (star (fun a => (U : Matrix (Fin 4) (Fin 4) ℂ) a i)) = G U (c • Pi.single i 1) := by
    ext a b
    fin_cases i <;> simp [G, Matrix.mul_apply, vecMulVec_apply, Fin.sum_univ_four, Pi.single_apply] <;> ring
  rw [specComp, h, muellerOf_eq _ (G_herm U _), F]

lemma depol3_eq (c : ℝ) : depol3 U c = F U ((c / 3) • ![1, 1, 1, 0]) := by
  have hD : ((c / 3 : ℝ) : ℂ) • ((U : Matrix (Fin 4) (Fin 4) ℂ) * diagonal ![(1 : ℂ), 1, 1, 0] *
      star (U : Matrix (Fin 4) (Fin 4) ℂ)) = G U ((c / 3) • ![1, 1, 1, 0]) := by
    rw [G_smul]; congr 1
  rw [depol3, hD, muellerOf_eq _ (G_herm U _), F]

lemma depol2_eq (c : ℝ) : depol2 U c = F U ((c / 2) • ![1, 1, 0, 0]) := by
  have hD : ((c / 2 : ℝ) : ℂ) • ((U : Matrix (Fin 4) (Fin 4) ℂ) * diagonal ![(1 : ℂ), 1, 0, 0] *
      star (U : Matrix (Fin 4) (Fin 4) ℂ)) = G U ((c / 2) • ![1, 1, 0, 0]) := by
    rw [G_smul]; congr 1
  rw [depol2, hD, muellerOf_eq _ (G_herm U _), F]

lemma F00 (d : Fin 4 → ℝ) : F U d 0 0 = ∑ i, d i := by
  have ht : (G U d).trace = ∑ i, ((d i : ℝ) : ℂ) := by
    rw [G, Matrix.trace_mul_cycle, Matrix.mem_unitaryGroup_iff'.mp U.2, Matrix.one_mul,
      trace_diagonal]
  have : F U d 0 0 = ((G U d).trace).re := by
    simp [F, mOf, Matrix.trace, Fin.sum_univ_four]
  rw [this, ht]; simp [Fin.sum_univ_four]


lemma sum_one (M : Matrix (Fin 4) (Fin 4) ℝ) (hm : 0 < M 0 0) (l : Fin 4 → ℝ)
    (hs : IsSpectralData M U l) : ∑ i, l i = 1 := by
  have h1 : M = M 0 0 • F U l := by
    conv_lhs => rw [← mOf_coh M]
    rw [hs.2, F, ← mOf_smul]; rfl
  have h2 := congrFun (congrFun h1 0) 0
  rw [Matrix.smul_apply, F00, smul_eq_mul] at h2
  have h3 : M 0 0 * (∑ i, l i - 1) = 0 := by rw [mul_sub]; linarith
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith


lemma covMueller_eq (lam : Fin 4 → ℝ) : covMueller U lam = F U (covEig lam) := by
  show muellerOf (G U (covEig lam)) = _
  rw [muellerOf_eq _ (G_herm U _)]; rfl

lemma covT_pos (lam : Fin 4 → ℝ) (h : 0 < lam 0) : 0 < covEig lam 0 + covEig lam 1 + covEig lam 2 + covEig lam 3 := by
  have := le_max_left (lam 0) 0
  have h1 := le_max_right (lam 1) 0
  have h2 := le_max_right (lam 2) 0
  have h3 := le_max_right (lam 3) 0
  simp only [covEig]; linarith

end S79MO

open Arxiv1605_04704 S79MO in
theorem solution (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : 2 < (covH U lam).rank) (hP2 : 0 < ipp2 (covLhat lam)) :
    let l := covLhat lam
    let c := covMueller U lam 0 0
    let p : Fin 4 → ℝ := ![(l 0 - l 2) / (l 0 + l 1 - 2 * l 2), (l 1 - l 2) / (l 0 + l 1 - 2 * l 2),
      0, 0]
    filt2 U lam = p 0 • specComp U c 0 + p 1 • specComp U c 1 ∧
    p 0 = (1 / 2) * (1 + ipp1 l / ipp2 l) ∧ p 1 = (1 / 2) * (1 - ipp1 l / ipp2 l) ∧
    (∀ i, 0 ≤ p i) ∧ p 0 + p 1 = 1 ∧
    filt2 U lam 0 0 = c ∧ IsSpectralData (filt2 U lam) U p := by
  intro l c p
  have hl : covLhat lam = l := rfl
  have hTpos := covT_pos lam hlam0
  set T := covEig lam 0 + covEig lam 1 + covEig lam 2 + covEig lam 3 with hT
  have hsumT : ∑ j, covEig lam j = T := by rw [Fin.sum_univ_four]
  have hE : covEig lam = T • l := by
    funext i; simp only [l, covLhat, hsumT, Pi.smul_apply, smul_eq_mul]; field_simp
  have hsum : l 0 + l 1 + l 2 + l 3 = 1 := by
    simp only [l, covLhat, hsumT]; field_simp; exact hT.symm
  have hc : c = T := by simp only [c, covMueller_eq, F00, Fin.sum_univ_four]; exact hT.symm
  have hcm : covMueller U lam = F U (T • l) := by rw [covMueller_eq, hE]
  have hanti : Antitone l := by
    intro i j hij
    simp only [l, covLhat, hsumT]
    apply div_le_div_of_nonneg_right _ hTpos.le
    exact max_le_max (hdat.1 hij) le_rfl
  have h01 : l 1 ≤ l 0 := hanti (by decide)
  have h12 : l 2 ≤ l 1 := hanti (by decide)
  have hq : l 0 + l 1 - 2 * l 2 = ipp2 l := by simp only [ipp2]
  set q := ipp2 l with hqdef
  have hl2 : l 2 = (l 0 + l 1 - q) / 2 := by linarith
  have hl3 : l 3 = 1 - l 0 - l 1 - (l 0 + l 1 - q) / 2 := by linarith
  have hqne : q ≠ 0 := hP2.ne'
  have hd : 0 < l 0 + l 1 - 2 * l 2 := by rw [hq]; exact hP2
  have hsTl : ∑ i, (T • l) i = T := by
    simp only [Fin.sum_univ_four, Pi.smul_apply, smul_eq_mul]
    rw [← mul_add, ← mul_add, ← mul_add, hsum, mul_one]
  have hfilt : filt2 U lam = F U ((T / q) • (l - ((1 - ipp3 l) / 4) • (fun _ : Fin 4 => (1 : ℝ)) -
      ((ipp3 l - q) / 3) • ![1, 1, 1, 0])) := by
    rw [filt2, hcm, F00, ← hqdef, idealDepol_eq U, depol3_eq U]
    simp only [hsTl]
    simp only [← F_add, ← F_smul, ← F_sub]
    congr 1; funext i
    fin_cases i <;> simp [hl, ipp3, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four] <;>
      field_simp <;> (try simp only [hl3, hl2]) <;> (first | ring1 | (right; trivial) | (right; ring1) | (left; right; ring1))
  have hpn : ∀ i, 0 ≤ p i := by
    intro i; fin_cases i <;> simp [p]
    · exact div_nonneg (by linarith) hd.le
    · exact div_nonneg (by linarith) hd.le
  have h00 : filt2 U lam 0 0 = T := by
    rw [hfilt, F00, Fin.sum_univ_four]
    simp [ipp3, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]
    field_simp; rw [hl3, hl2]; ring
  have fin1 : ∀ i : Fin 4, (((T / q) • (l - ((1 - ipp3 l) / 4) • (fun _ : Fin 4 => (1 : ℝ)) -
      ((ipp3 l - q) / 3) • ![1, 1, 1, 0])) : Fin 4 → ℝ) i = (T • p) i := by
    intro i
    fin_cases i <;> simp [p, ipp3, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;>
      (try simp only [hq]) <;> (try field_simp) <;> (try simp only [hl3, hl2]) <;>
        (first | ring1 | (right; trivial) | (right; ring1) | (left; right; ring1))
  refine ⟨?_, ?_, ?_, hpn, ?_, ?_, ?_⟩
  · rw [hfilt, hc, specComp_eq U, specComp_eq U]
    simp only [← F_add, ← F_smul]
    congr 1; funext i
    rw [fin1 i]
    fin_cases i <;> simp [Pi.single_apply, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul, p] <;> ring
  · simp only [p, ipp1, Matrix.cons_val_zero]; rw [hq]; field_simp; rw [hl2]; ring
  · simp only [p, ipp1, Matrix.cons_val_one, Matrix.cons_val_zero]; rw [hq]; field_simp; rw [hl2]; ring
  · simp only [p]; simp; rw [hq]; field_simp; rw [hl2]; ring
  · rw [h00, hc]
  · refine ⟨?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp [p] at hab ⊢ <;>
        (first | exact div_le_div_of_nonneg_right (by linarith) hd.le | exact div_nonneg (by linarith) hd.le | skip)
    · rw [h00, hfilt, F, coh_mOf _ (G_herm U _)]
      have : ((T : ℝ) : ℂ) • ((U : Matrix (Fin 4) (Fin 4) ℂ) * diagonal (fun i => ((p i : ℝ) : ℂ)) *
          star (U : Matrix (Fin 4) (Fin 4) ℂ)) = G U (T • p) := by rw [G_smul]; rfl
      rw [this]; congr 1; funext i; exact fin1 i
