-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV2b
-- name    : RPLib_S3_EllW2MV2b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:55:20.275193+00:00
-- url     : https://prove2.me/theorems/7db42b97-6aa2-42e9-9e73-484a22588df8
-- title:
--   The Eichler-Selberg trace formula in weight two: normal form and the fibre identity
-- statement:
--   Normal form and the fibre identity.
--
--   * `Tc M n c = {G : G₁₀ = c̄, det G = n̄}` and `G0c M n c = [[1, 0], [c̄, n̄]]`.
--   * `det_psiU`, `det_psiL`, `det_psiR`: the three moves preserve the determinant.
--   * `piM_mem_Tc`: `Xc z → piM z ∈ Tc`.
--   * `ker_castHom_gcd`: the kernel of `ZMod M → ZMod (gcd(|c|, M))` is `c̄ · ZMod M`.
--   * **`fibC_normal`** (`n̄` a unit): `fibC G = fibC G0c` for every `G ∈ Tc`.
--   * **`sum_Xc_eq`**: `Σ_z [Xc z] F(piM z) = fibC G0c • Σ_{G ∈ Tc} F G`; **`card_Xc_eq`**: `#Xc = fibC G0c · #Tc`.
--   * **`two_mul_muc_eq_fib`**: `2 M (q μ_c) = fibC G0c · Σ_{G ∈ Tc} Lbar G`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV2

/-!
# S3-ES-Wt2 (O6, file MV2b): normal form and the fibre identity

* `Tc M n c = {G : G₁₀ = c̄, det G = n̄}` and `G0c M n c = [[1, 0], [c̄, n̄]]`.
* `det_psiU`, `det_psiL`, `det_psiR`: the three moves preserve the determinant.
* `piM_mem_Tc`: `Xc z → piM z ∈ Tc`.
* `ker_castHom_gcd`: the kernel of `ZMod M → ZMod (gcd(|c|, M))` is `c̄ · ZMod M`.
* **`fibC_normal`** (`n̄` a unit): `fibC G = fibC G0c` for every `G ∈ Tc`.
* **`sum_Xc_eq`**: `Σ_z [Xc z] F(piM z) = fibC G0c • Σ_{G ∈ Tc} F G`; **`card_Xc_eq`**: `#Xc = fibC G0c · #Tc`.
* **`two_mul_muc_eq_fib`**: `2 M (q μ_c) = fibC G0c · Σ_{G ∈ Tc} Lbar G`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- Matrices over `ZMod M` with lower-left entry `c̄` and determinant `n̄`. -/
def Tc (M : ℕ) [NeZero M] (n c : ℤ) : Finset (Matrix (Fin 2) (Fin 2) (ZMod M)) :=
  univ.filter fun G => G 1 0 = (c : ZMod M) ∧ G.det = (n : ZMod M)

/-- The normal form `[[1, 0], [c̄, n̄]]`. -/
def G0c (M : ℕ) [NeZero M] (n c : ℤ) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  !![1, 0; (c : ZMod M), (n : ZMod M)]

omit [NeZero M] in
lemma det_psiU (w : (ZMod M)ˣ) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    (psiU w G).det = G.det := by
  rw [psiU, Matrix.det_fin_two_of, Matrix.det_fin_two]
  have h : (w : ZMod M) * ((w⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := Units.mul_inv w
  linear_combination (G 0 0 * G 1 1) * h

omit [NeZero M] in
lemma det_psiL (k : ZMod M) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    (psiL k G).det = G.det := by
  rw [psiL, Matrix.det_fin_two_of, Matrix.det_fin_two]
  ring

omit [NeZero M] in
lemma det_psiR (k : ZMod M) (G : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    (psiR k G).det = G.det := by
  rw [psiR, Matrix.det_fin_two_of, Matrix.det_fin_two]
  ring

lemma piM_mem_Tc (n : ℤ) {c : ℤ} {q : ℕ} [NeZero q] (hMq : M ∣ q) (z : ZMod q × ZMod q)
    (hz : Xc n c z) : piM M n c hMq z ∈ Tc M n c := by
  rw [Tc, mem_filter]
  refine ⟨mem_univ _, rfl, ?_⟩
  have hz' : c ∣ (z.1.val : ℤ) * z.2.val - n := hz
  have h1 : (((((z.1.val : ℤ) * z.2.val - n) / c : ℤ)) : ZMod M) * (c : ZMod M) =
      ((((z.1.val : ℤ) * z.2.val - n : ℤ)) : ZMod M) := by
    rw [← Int.cast_mul, Int.ediv_mul_cancel hz']
  rw [piM, Matrix.det_fin_two_of, h1, ← intCast_val_castHom hMq z.1,
    ← intCast_val_castHom hMq z.2]
  push_cast
  ring

lemma ker_castHom_gcd (c : ℤ) (w : ZMod M)
    (hw : ZMod.castHom (Nat.gcd_dvd_right c.natAbs M) (ZMod (Nat.gcd c.natAbs M)) w = 0) :
    ∃ k : ℤ, w = (k : ZMod M) * (c : ZMod M) := by
  have he : ((Nat.gcd c.natAbs M : ℕ) : ℤ) = c * Int.gcdA c M + (M : ℤ) * Int.gcdB c M := by
    rw [← Int.gcd_eq_gcd_ab]
    rfl
  have h1 := hw
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨t, ht⟩ := h1
  refine ⟨Int.gcdA c M * t, ?_⟩
  rw [← intCast_val_zmod w, ht, Nat.cast_mul, he]
  push_cast
  rw [ZMod.natCast_self]
  ring

theorem fibC_normal (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (hMq : M ∣ q) (hn : IsUnit (n : ZMod M)) (G : Matrix (Fin 2) (Fin 2) (ZMod M))
    (hG : G ∈ Tc M n c) : fibC M n c hMq G = fibC M n c hMq (G0c M n c) := by
  rw [Tc, mem_filter] at hG
  obtain ⟨-, hG10, hGdet⟩ := hG
  have heM : Nat.gcd c.natAbs M ∣ M := Nat.gcd_dvd_right _ _
  have heq : Nat.gcd c.natAbs M ∣ q := dvd_trans heM hMq
  have : NeZero (Nat.gcd c.natAbs M) :=
    ⟨(Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne M))).ne'⟩
  set φ := ZMod.castHom heM (ZMod (Nat.gcd c.natAbs M)) with hφ
  have hc0 : φ (c : ZMod M) = 0 := by
    rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _)
  have hunit : IsUnit (φ (G 0 0)) := by
    have h1 : φ G.det = φ (G 0 0) * φ (G 1 1) := by
      rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, hG10, hc0, mul_zero, sub_zero]
    have h2 : IsUnit (φ G.det) := by rw [hGdet]; exact hn.map φ
    rw [h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective heq (hunit.unit⁻¹)
  have hu' : φ ((ZMod.unitsMap hMq u : (ZMod M)ˣ) : ZMod M) * φ (G 0 0) = 1 := by
    have h3 : φ ((ZMod.unitsMap hMq u : (ZMod M)ˣ) : ZMod M) =
        ((hunit.unit⁻¹ : (ZMod (Nat.gcd c.natAbs M))ˣ) : ZMod (Nat.gcd c.natAbs M)) := by
      rw [← hu, ← ZMod.unitsMap_comp heM hMq]
      rfl
    rw [h3]
    exact hunit.val_inv_mul
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = psiU (ZMod.unitsMap hMq u) G := ⟨_, rfl⟩
  have h1_00 : G1 0 0 = ((ZMod.unitsMap hMq u : (ZMod M)ˣ) : ZMod M) * G 0 0 := by
    rw [hG1]; rfl
  have h1_10 : G1 1 0 = (c : ZMod M) := by rw [hG1]; exact hG10
  have h1_det : G1.det = (n : ZMod M) := by rw [hG1, det_psiU, hGdet]
  have hk0 : φ (G1 0 0 - 1) = 0 := by rw [map_sub, map_one, h1_00, map_mul, hu', sub_self]
  obtain ⟨k0, hk0'⟩ := ker_castHom_gcd c (G1 0 0 - 1) hk0
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = psiL (((-k0 : ℤ)) : ZMod M) G1 := ⟨_, rfl⟩
  have h2_00 : G2 0 0 = 1 := by
    rw [hG2]
    show G1 0 0 + (((-k0 : ℤ)) : ZMod M) * G1 1 0 = 1
    rw [h1_10, Int.cast_neg]
    linear_combination hk0'
  have h2_10 : G2 1 0 = (c : ZMod M) := by rw [hG2]; exact h1_10
  have h2_det : G2.det = (n : ZMod M) := by rw [hG2, det_psiL, h1_det]
  obtain ⟨G3, hG3⟩ : ∃ G3, G3 = psiR (((-((G2 0 1).val : ℤ) : ℤ)) : ZMod M) G2 := ⟨_, rfl⟩
  have h3_00 : G3 0 0 = 1 := by rw [hG3]; exact h2_00
  have h3_01 : G3 0 1 = 0 := by
    rw [hG3]
    show G2 0 1 + (((-((G2 0 1).val : ℤ) : ℤ)) : ZMod M) * G2 0 0 = 0
    rw [h2_00, mul_one, Int.cast_neg, intCast_val_zmod, add_neg_cancel]
  have h3_10 : G3 1 0 = (c : ZMod M) := by rw [hG3]; exact h2_10
  have h3_det : G3.det = (n : ZMod M) := by rw [hG3, det_psiR, h2_det]
  have h3 : G3 = G0c M n c := by
    refine mat2_ext h3_00 h3_01 h3_10 ?_
    rw [Matrix.det_fin_two, h3_00, h3_01, one_mul, zero_mul, sub_zero] at h3_det
    exact h3_det
  rw [← h3, hG3, fibC_psiR n hc hq hMq, hG2, fibC_psiL n hc hq hMq, hG1, fibC_psiU n hc hq hMq]

/-- The fibre identity. -/
theorem sum_Xc_eq (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (hMq : M ∣ q) (hn : IsUnit (n : ZMod M)) {β : Type*} [AddCommMonoid β]
    (F : Matrix (Fin 2) (Fin 2) (ZMod M) → β) :
    (∑ z : ZMod q × ZMod q, if Xc n c z then F (piM M n c hMq z) else 0) =
      fibC M n c hMq (G0c M n c) • ∑ G ∈ Tc M n c, F G := by
  rw [← Finset.sum_filter,
    ← Finset.sum_fiberwise_of_maps_to' (s := univ.filter fun z => Xc n c z) (t := Tc M n c)
      (g := piM M n c hMq) (fun z hz => piM_mem_Tc n hMq z (mem_filter.mp hz).2) F,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun G hG => ?_
  rw [Finset.sum_const, filter_filter, ← fibC_normal n hc hq hMq hn G hG]
  rfl

theorem card_Xc_eq (n : ℤ) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q] (hq : q = c.natAbs * M)
    (hMq : M ∣ q) (hn : IsUnit (n : ZMod M)) :
    (univ.filter fun z : ZMod q × ZMod q => Xc n c z).card =
      fibC M n c hMq (G0c M n c) * (Tc M n c).card := by
  have h := sum_Xc_eq n hc hq hMq hn (β := ℕ) (fun _ => 1)
  simp only [smul_eq_mul, Finset.sum_const, mul_one] at h
  rw [Finset.card_filter, h]

theorem two_mul_muc_eq_fib (n : ℤ) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) {q : ℕ} [NeZero q]
    (hq : q = c.natAbs * M) (hMq : M ∣ q) (hn : IsUnit (n : ZMod M)) :
    2 * (M : ℂ) * ((q : ℂ) * muc M n δ' c) =
      (fibC M n c hMq (G0c M n c) : ℂ) * ∑ G ∈ Tc M n c, (Lbar M δ' G : ℂ) := by
  have h := sum_Xc_eq n hc hq hMq hn (fun G => (Lbar M δ' G : ℂ))
  rw [two_mul_muc_eq_sum n δ' hc hq hMq, h, nsmul_eq_mul]

end RamanujanPetersson.EllW2


