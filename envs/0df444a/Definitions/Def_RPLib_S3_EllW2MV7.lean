-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV7
-- name    : RPLib_S3_EllW2MV7
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:01:42.045614+00:00
-- url     : https://prove2.me/theorems/743fe6c9-c506-4442-8f39-27c4e37c40f9
-- title:
--   The Eichler-Selberg trace formula in weight two: the level counts average to one over a determinant class
-- statement:
--   The level counts average to one over a determinant class.
--
--   For `n̄` and `δ'` units of `ZMod M`:
--   * `card_filter_mul_right`: right multiplication by a determinant-one unit permutes `{det = n̄}`.
--   * `card_eig_eq` (`v` exact): `#{G : det G = n̄, G v = δ' v} = #{G : det G = n̄, G e₁ = v}`
--     (`v = P e₁` with `P ∈ SL₂`; multiply by `diag(δ', δ'⁻¹) P⁻¹`).
--   * `exact_col`: the first column of a matrix with unit determinant is exact.
--   * **`sum_Lbar_det`**: `Σ_{det G = n̄} L̄(G) = #{G : det G = n̄}` (double counting).
--   * **`sum_TR_Lbar`**: `Σ_r Σ_{G ∈ T_r} L̄(G) = Σ_r #T_r`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV3b
import Definitions.Def_RPLib_S3_ConjClassesA

/-!
# S3-ES-Wt2 (O6, file MV7): the level counts average to one over a determinant class

For `n̄` and `δ'` units of `ZMod M`:
* `card_filter_mul_right`: right multiplication by a determinant-one unit permutes `{det = n̄}`.
* `card_eig_eq` (`v` exact): `#{G : det G = n̄, G v = δ' v} = #{G : det G = n̄, G e₁ = v}`
  (`v = P e₁` with `P ∈ SL₂`; multiply by `diag(δ', δ'⁻¹) P⁻¹`).
* `exact_col`: the first column of a matrix with unit determinant is exact.
* **`sum_Lbar_det`**: `Σ_{det G = n̄} L̄(G) = #{G : det G = n̄}` (double counting).
* **`sum_TR_Lbar`**: `Σ_r Σ_{G ∈ T_r} L̄(G) = Σ_r #T_r`.
-/

open Finset

open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.S3.Conj

variable {M : ℕ} [NeZero M]

/-- The matrices over `ZMod M` of determinant `n̄`. -/
def detSet (M : ℕ) [NeZero M] (n : ℤ) : Finset (Matrix (Fin 2) (Fin 2) (ZMod M)) :=
  univ.filter fun G => G.det = (n : ZMod M)

lemma mem_detSet {n : ℤ} {G : Matrix (Fin 2) (Fin 2) (ZMod M)} :
    G ∈ detSet M n ↔ G.det = (n : ZMod M) := by
  simp [detSet]

lemma card_filter_mul_right (n : ℤ) {A B : Matrix (Fin 2) (Fin 2) (ZMod M)} (hAB : A * B = 1)
    (hBA : B * A = 1) (hA : A.det = 1) (p q : Matrix (Fin 2) (Fin 2) (ZMod M) → Prop)
    [DecidablePred p] [DecidablePred q] (hpq : ∀ G, p G ↔ q (G * A)) :
    ((detSet M n).filter p).card = ((detSet M n).filter q).card := by
  have hB : B.det = 1 := by
    have h := congrArg Matrix.det hAB
    rwa [Matrix.det_mul, hA, one_mul, Matrix.det_one] at h
  refine Finset.card_bij' (fun G _ => G * A) (fun G _ => G * B) ?_ ?_ ?_ ?_
  · intro G hG
    rw [mem_filter, mem_detSet] at hG ⊢
    exact ⟨by rw [Matrix.det_mul, hA, mul_one, hG.1], (hpq G).1 hG.2⟩
  · intro G hG
    rw [mem_filter, mem_detSet] at hG ⊢
    refine ⟨by rw [Matrix.det_mul, hB, mul_one, hG.1], (hpq _).2 ?_⟩
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one]
    exact hG.2
  · intro G _
    rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  · intro G _
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one]

omit [NeZero M] in
lemma det_redMat_SL (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) : (redMat M (g : Mat)).det = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at h ⊢
  have h' := congrArg (Int.cast : ℤ → ZMod M) h
  push_cast at h'
  simpa [redMat] using h'

lemma card_eig_eq (n : ℤ) (u : (ZMod M)ˣ) {v : Fin 2 → ZMod M} (hv : IsExact M v) :
    ((detSet M n).filter fun G => G *ᵥ v = (u : ZMod M) • v).card =
      ((detSet M n).filter fun G => G *ᵥ ![1, 0] = v).card := by
  obtain ⟨g, hg⟩ := exists_smul_e1 hv
  rw [vsmul_def, e1] at hg
  set P := redMat M (g : Mat) with hP
  set Q := redMat M ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Mat) with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← redMat_mul, coe_mul_coe_inv, redMat_one]
  have hQP : Q * P = 1 := by rw [hP, hQ, ← redMat_mul, coe_inv_mul_coe, redMat_one]
  set D1 : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    !![(u : ZMod M), 0; 0, ((u⁻¹ : (ZMod M)ˣ) : ZMod M)] with hD1
  set D2 : Matrix (Fin 2) (Fin 2) (ZMod M) :=
    !![((u⁻¹ : (ZMod M)ˣ) : ZMod M), 0; 0, (u : ZMod M)] with hD2
  have h12 : D1 * D2 = 1 := by
    rw [hD1, hD2, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  have h21 : D2 * D1 = 1 := by
    rw [hD1, hD2, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  have hD1det : D1.det = 1 := by
    rw [hD1, Matrix.det_fin_two_of]
    simp
  have hAv : (D1 * Q) *ᵥ v = (u : ZMod M) • ![1, 0] := by
    rw [← hg, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQP, Matrix.mul_one, hD1]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  symm
  refine card_filter_mul_right n (A := D1 * Q) (B := P * D2) ?_ ?_ ?_ _ _ ?_
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul, h12]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc D2, h21, Matrix.one_mul, hPQ]
  · rw [Matrix.det_mul, hD1det, one_mul, hQ, det_redMat_SL]
  · intro G
    rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul]
    constructor
    · intro h
      rw [h]
    · intro h
      have h' := congrArg (fun w => ((u⁻¹ : (ZMod M)ˣ) : ZMod M) • w) h
      simpa [smul_smul] using h'

omit [NeZero M] in
lemma exact_col {n : ℤ} (hn : IsUnit (n : ZMod M)) {G : Matrix (Fin 2) (Fin 2) (ZMod M)}
    (hG : G.det = (n : ZMod M)) : IsExact M (G *ᵥ ![1, 0]) := by
  intro d hd hd0 h
  have h0 : (d : ZMod M) * G 0 0 = 0 := by
    have := congr_fun h 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, nsmul_eq_mul] using this
  have h1 : (d : ZMod M) * G 1 0 = 0 := by
    have := congr_fun h 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, nsmul_eq_mul] using this
  have hdet : (d : ZMod M) * (n : ZMod M) = 0 := by
    rw [← hG, Matrix.det_fin_two]
    linear_combination (G 1 1) * h0 - (G 0 1) * h1
  have hd' : (d : ZMod M) = 0 := hn.mul_left_eq_zero.1 hdet
  rw [ZMod.natCast_eq_zero_iff] at hd'
  exact absurd (Nat.le_of_dvd hd0 hd') (not_le.2 (mem_range.1 hd))

theorem sum_Lbar_det {n : ℤ} (hn : IsUnit (n : ZMod M)) {δ' : ZMod M} (hδ : IsUnit δ') :
    ∑ G ∈ detSet M n, Lbar M δ' G = (detSet M n).card := by
  obtain ⟨u, rfl⟩ := hδ
  have hL : ∀ G : Matrix (Fin 2) (Fin 2) (ZMod M), Lbar M (u : ZMod M) G =
      ((univ.filter fun v : Fin 2 → ZMod M => ∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0).bipartiteAbove
        (fun G v => G *ᵥ v = (u : ZMod M) • v) G).card := by
    intro G
    simp only [Lbar, Finset.bipartiteAbove, Finset.filter_filter]
  calc ∑ G ∈ detSet M n, Lbar M (u : ZMod M) G
      = ∑ G ∈ detSet M n, ((univ.filter fun v : Fin 2 → ZMod M =>
          ∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0).bipartiteAbove
            (fun G v => G *ᵥ v = (u : ZMod M) • v) G).card := sum_congr rfl fun G _ => hL G
    _ = ∑ v ∈ univ.filter (fun v : Fin 2 → ZMod M => ∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0),
          ((detSet M n).bipartiteBelow (fun G v => G *ᵥ v = (u : ZMod M) • v) v).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = ∑ v ∈ univ.filter (fun v : Fin 2 → ZMod M => ∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0),
          ((detSet M n).filter fun G => G *ᵥ ![1, 0] = v).card := by
        refine sum_congr rfl fun v hv => ?_
        rw [Finset.bipartiteBelow]
        exact card_eig_eq n u (mem_filter.1 hv).2
    _ = (detSet M n).card := by
        refine (card_eq_sum_card_fiberwise (f := fun G => G *ᵥ ![1, 0]) ?_).symm
        intro G hG
        rw [Finset.mem_coe, mem_filter]
        exact ⟨mem_univ _, exact_col hn (mem_detSet.1 (Finset.mem_coe.1 hG))⟩

lemma TR_eq_filter (n : ℤ) (r : ZMod M) :
    TR M n r = (detSet M n).filter fun G => G 1 0 = r := by
  ext G
  simp [TR, detSet, and_comm]

theorem sum_TR_card (n : ℤ) : ∑ r : ZMod M, (TR M n r).card = (detSet M n).card := by
  simp_rw [TR_eq_filter]
  exact (card_eq_sum_card_fiberwise (f := fun G : Matrix (Fin 2) (Fin 2) (ZMod M) => G 1 0) (t := univ)
    (fun G _ => Finset.mem_coe.2 (mem_univ _))).symm

theorem sum_TR_Lbar {n : ℤ} (hn : IsUnit (n : ZMod M)) {δ' : ZMod M} (hδ : IsUnit δ') :
    ∑ r : ZMod M, ∑ G ∈ TR M n r, (Lbar M δ' G : ℝ) = ∑ r : ZMod M, ((TR M n r).card : ℝ) := by
  have h1 : ∑ r : ZMod M, ∑ G ∈ TR M n r, (Lbar M δ' G : ℝ) =
      ∑ G ∈ detSet M n, (Lbar M δ' G : ℝ) := by
    simp_rw [TR_eq_filter]
    exact Finset.sum_fiberwise (detSet M n) (fun G : Matrix (Fin 2) (Fin 2) (ZMod M) => G 1 0) _
  rw [h1, ← Nat.cast_sum, ← Nat.cast_sum, sum_Lbar_det hn hδ, sum_TR_card]

end RamanujanPetersson.EllW2


