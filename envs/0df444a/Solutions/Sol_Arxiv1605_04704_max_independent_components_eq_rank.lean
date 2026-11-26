-- Prove2me | solution 1 for Arxiv1605_04704.max_independent_components_eq_rank
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T05:40:05.616104+00:00
-- url     : https://prove2.me/submissions/15fa3194-c9fb-4c05-a2ae-5167f99a0973

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


lemma le_rank (A : Matrix (Fin 4) (Fin 4) ℂ) (n : ℕ) (w : Fin n → Fin 4 → ℂ)
    (hli : LinearIndependent ℂ w) (h : ∀ i, w i ∈ LinearMap.range A.mulVecLin) : n ≤ A.rank := by
  let w' : Fin n → LinearMap.range A.mulVecLin := fun i => ⟨w i, h i⟩
  have hw : LinearIndependent ℂ w' := by
    apply LinearIndependent.of_comp (LinearMap.range A.mulVecLin).subtype
    exact hli
  have := hw.fintype_card_le_finrank
  simpa [Matrix.rank] using this

lemma coh_cov (lam : Fin 4 → ℝ) : cohMat (covMueller U lam) = covH U lam := by
  rw [covMueller_eq, F, coh_mOf _ (G_herm U _)]; rfl

end S79MO

open Arxiv1605_04704 S79MO in
theorem solution (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0) :
    IsGreatest {n : ℕ | ∃ (p : Fin n → ℝ) (w : Fin n → Fin 4 → ℂ),
        IsPureDecomp (covMueller U lam) n p w ∧ ∀ i, 0 < p i} (covH U lam).rank := by
  refine ⟨?_, fun n ⟨p, w, hd, _⟩ => ?_⟩
  swap
  · have := le_rank _ n w hd.2.2.2.2.1 hd.2.2.2.1
    rwa [coh_cov] at this
  set E := covEig lam with hEdef
  have hE0 : ∀ i, 0 ≤ E i := fun i => le_max_right _ _
  have hTpos := covT_pos lam hlam0
  set T := E 0 + E 1 + E 2 + E 3 with hT
  set Um : Matrix (Fin 4) (Fin 4) ℂ := (U : Matrix (Fin 4) (Fin 4) ℂ) with hUm
  have hUU : star Um * Um = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hUU' : Um * star Um = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hdetU : IsUnit Um.det := Matrix.isUnit_det_of_left_inverse hUU
  have hdetU' : IsUnit (star Um).det := Matrix.isUnit_det_of_right_inverse hUU
  let S : Finset (Fin 4) := Finset.univ.filter (fun i => ((E i : ℝ) : ℂ) ≠ 0)
  have hrank : (covH U lam).rank = S.card := by
    show (Um * diagonal (fun i => ((E i : ℝ) : ℂ)) * star Um).rank = _
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetU', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdetU,
      Matrix.rank_diagonal, Fintype.card_subtype]
  rw [hrank]
  let f : Fin S.card → Fin 4 := fun k => (S.equivFin.symm k).1
  have hf : Function.Injective f := fun a b h => S.equivFin.symm.injective (Subtype.ext h)
  have hsumS : ∀ (β : Type) [AddCommMonoid β] (g : Fin 4 → β), (∀ i, E i = 0 → g i = 0) →
      ∑ k, g (f k) = ∑ i, g i := by
    intro β _ g hg
    rw [Equiv.sum_comp S.equivFin.symm (fun x : S => g x.1), Finset.sum_coe_sort S g]
    apply Finset.sum_filter_of_ne
    intro i _ hgi
    intro h0
    exact hgi (hg i (by exact_mod_cast h0))
  have hfpos : ∀ k, 0 < E (f k) := by
    intro k
    have hm := (S.equivFin.symm k).2
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact lt_of_le_of_ne (hE0 _) (fun h => hm (by rw [← h]; simp))
  let col : Fin 4 → Fin 4 → ℂ := fun i a => Um a i
  have hcol : ∀ i, col i = Um *ᵥ Pi.single i 1 := fun i => by
    rw [Matrix.mulVec_single_one]; rfl
  refine ⟨fun k => E (f k) / T, fun k => col (f k), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k; exact div_nonneg (hE0 _) hTpos.le
  · rw [← Finset.sum_div, hsumS ℝ E (fun i h => h), Fin.sum_univ_four]; exact div_self hTpos.ne'
  · intro k
    have h1 := congrFun (congrFun hUU (f k)) (f k)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h1
    have : ((∑ j, Complex.normSq (col (f k) j) : ℝ) : ℂ) = 1 := by
      rw [← h1]; push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    exact_mod_cast this
  · intro k
    rw [coh_cov]
    have hne : ((E (f k) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hfpos k).ne'
    refine ⟨Um *ᵥ ((((E (f k))⁻¹ : ℝ) : ℂ) • Pi.single (f k) 1), ?_⟩
    show (Um * diagonal (fun i => ((E i : ℝ) : ℂ)) * star Um) *ᵥ (Um *ᵥ _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
    show _ = col (f k)
    rw [hcol (f k)]
    congr 1
    ext j
    by_cases hj : j = f k
    · subst hj; simp [Matrix.mulVec, dotProduct, diagonal_apply, Pi.single_apply, hne]
    · simp [Matrix.mulVec, dotProduct, diagonal_apply, Pi.single_apply, hj]
  · have hli : LinearIndependent ℂ (fun k => (Pi.basisFun ℂ (Fin 4)) (f k)) :=
      (Pi.basisFun ℂ (Fin 4)).linearIndependent.comp f hf
    have hker : LinearMap.ker Um.mulVecLin = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      have := congrArg (fun x => star Um *ᵥ x) hv
      simpa [Matrix.mulVec_mulVec, hUU] using this
    have heq : (fun k => col (f k)) = Um.mulVecLin ∘ (fun k => (Pi.basisFun ℂ (Fin 4)) (f k)) := by
      funext k; simp [hcol, Pi.basisFun_apply]
    rw [heq]; exact hli.map' _ hker
  · have h00 : covMueller U lam 0 0 = T := by
      rw [covMueller_eq, F00, Fin.sum_univ_four]
    rw [coh_cov, h00]
    have : ∀ k, ((E (f k) / T * T : ℝ) : ℂ) = ((E (f k) : ℝ) : ℂ) := by
      intro k; rw [div_mul_cancel₀ _ hTpos.ne']
    simp only [this]
    rw [hsumS (Matrix (Fin 4) (Fin 4) ℂ) (fun i => ((E i : ℝ) : ℂ) • vecMulVec (col i) (star (col i)))
      (fun i h => by simp [h])]
    ext a b
    simp [covH, Matrix.mul_apply, vecMulVec_apply, Fin.sum_univ_four, col, Matrix.sum_apply, hEdef]
    ring
  · intro k; exact div_pos (hfpos k) hTpos
