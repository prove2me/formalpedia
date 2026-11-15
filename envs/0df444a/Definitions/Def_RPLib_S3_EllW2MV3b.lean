-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV3b
-- name    : RPLib_S3_EllW2MV3b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:00:21.541501+00:00
-- url     : https://prove2.me/theorems/c835aa6b-f1b9-4909-922f-eea6bca0c0e6
-- title:
--   The Eichler-Selberg trace formula in weight two: `#T_r = M (M/e) φ(e)`, `e = gcd(M, r̃)`
-- statement:
--   `#T_r = M (M/e) φ(e)`, `e = gcd(M, r̃)`.
--
--   * `TR M n r = {G : G₁₀ = r, det G = n̄}`; `Tc_eq_TR : Tc M n c = TR M n c̄` (by `rfl`).
--   * `card_TR_eq_triple`: `T_r ≃ {(a, d, b) : b r = a d - n̄}`.
--   * `card_dvd_val`: `#{d mod M : K ∣ a d̃ - n} = (M/K) · gf n (gcd(K, a))` for `K ∣ M`.
--   * `gf_gcd_eq` (`n ⊥ M`, `g ∣ M`): `gf n (gcd(g, a)) = [a ⊥ g]`.
--   * **`card_TR`** (`n ⊥ M`): `#T_r = M · (M / e) · φ(e)`, `e = gcd(M, r.val)`; `card_TR_pos`;
--     `gcd_val_neg`, **`card_TR_neg`**: `#T_{-r} = #T_r`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV3a

/-!
# S3-ES-Wt2 (O6, file MV3b): `#T_r = M (M/e) φ(e)`, `e = gcd(M, r̃)`

* `TR M n r = {G : G₁₀ = r, det G = n̄}`; `Tc_eq_TR : Tc M n c = TR M n c̄` (by `rfl`).
* `card_TR_eq_triple`: `T_r ≃ {(a, d, b) : b r = a d - n̄}`.
* `card_dvd_val`: `#{d mod M : K ∣ a d̃ - n} = (M/K) · gf n (gcd(K, a))` for `K ∣ M`.
* `gf_gcd_eq` (`n ⊥ M`, `g ∣ M`): `gf n (gcd(g, a)) = [a ⊥ g]`.
* **`card_TR`** (`n ⊥ M`): `#T_r = M · (M / e) · φ(e)`, `e = gcd(M, r.val)`; `card_TR_pos`;
  `gcd_val_neg`, **`card_TR_neg`**: `#T_{-r} = #T_r`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

variable {M : ℕ} [NeZero M]

/-- Matrices over `ZMod M` with lower-left entry `r` and determinant `n̄`. -/
def TR (M : ℕ) [NeZero M] (n : ℤ) (r : ZMod M) : Finset (Matrix (Fin 2) (Fin 2) (ZMod M)) :=
  univ.filter fun G => G 1 0 = r ∧ G.det = (n : ZMod M)

lemma Tc_eq_TR (n c : ℤ) : Tc M n c = TR M n (c : ZMod M) := rfl

lemma card_TR_eq_triple (n : ℤ) (r : ZMod M) :
    (TR M n r).card = (univ.filter fun p : ZMod M × ZMod M × ZMod M =>
      p.2.2 * r = p.1 * p.2.1 - (n : ZMod M)).card := by
  refine Finset.card_nbij' (fun G => (G 0 0, G 1 1, G 0 1))
    (fun p => !![p.1, p.2.2; r, p.2.1]) ?_ ?_ ?_ ?_
  · intro G hG
    rw [Finset.mem_coe, TR, Finset.mem_filter] at hG
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨-, h10, hdet⟩ := hG
    rw [Matrix.det_fin_two, h10] at hdet
    exact ⟨mem_univ _, by linear_combination -hdet⟩
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    rw [Finset.mem_coe, TR, Finset.mem_filter]
    refine ⟨mem_univ _, rfl, ?_⟩
    rw [Matrix.det_fin_two_of]
    linear_combination -hp.2
  · intro G hG
    rw [Finset.mem_coe, TR, Finset.mem_filter] at hG
    exact mat2_ext rfl rfl hG.2.1.symm rfl
  · intro p _
    rfl

lemma card_dvd_val (n : ℤ) {K : ℕ} [NeZero K] (hK : K ∣ M) (a : ℕ) :
    (univ.filter fun d : ZMod M => (K : ℤ) ∣ (a : ℤ) * d.val - n).card =
      M / K * gf n (Nat.gcd K a) := by
  have hr : range M = range (M / K * K) := by rw [Nat.div_mul_cancel hK]
  have hP : ∀ m : ℕ, ((K : ℤ) ∣ (a : ℤ) * ((m + K : ℕ) : ℤ) - n) ↔
      ((K : ℤ) ∣ (a : ℤ) * (m : ℤ) - n) := by
    intro m
    have e2 : (a : ℤ) * ((m + K : ℕ) : ℤ) - n = ((a : ℤ) * m - n) + K * a := by push_cast; ring
    rw [e2]
    exact dvd_add_left (dvd_mul_right _ _)
  rw [HypPar.card_filter_val (M := M) (fun m : ℕ => ((K : ℤ) ∣ (a : ℤ) * m - n)), hr,
    HypPar.card_filter_range_periodic _ K hP (M / K),
    ← HypPar.card_filter_val (M := K) (fun m : ℕ => ((K : ℤ) ∣ (a : ℤ) * m - n)),
    card_dvd_mul_sub n a]

omit [NeZero M] in
lemma gf_gcd_eq (n : ℤ) (hn : Nat.Coprime n.natAbs M) {g : ℕ} (hg : g ∣ M) (a : ℕ) :
    gf n (Nat.gcd g a) = if Nat.Coprime a g then 1 else 0 := by
  unfold gf
  by_cases h : Nat.Coprime a g
  · rw [if_pos h, Nat.gcd_comm g a, Nat.Coprime.gcd_eq_one h]
    simp
  · rw [if_neg h, if_neg]
    intro hd
    apply h
    have h1 : Nat.gcd g a ∣ n.natAbs := Int.ofNat_dvd_left.mp hd
    have h2 : Nat.gcd g a ∣ M := (Nat.gcd_dvd_left g a).trans hg
    have h3 : Nat.gcd g a = 1 :=
      Nat.dvd_one.mp (by rw [← Nat.Coprime.gcd_eq_one hn]; exact Nat.dvd_gcd h1 h2)
    rw [Nat.Coprime, Nat.gcd_comm]
    exact h3

lemma card_b (n : ℤ) (r a d : ZMod M) :
    (univ.filter fun b : ZMod M => b * r = a * d - (n : ZMod M)).card =
      if ((Nat.gcd M r.val : ℕ) : ℤ) ∣ (a.val : ℤ) * d.val - n then Nat.gcd M r.val else 0 := by
  have e : a * d - (n : ZMod M) = ((((a.val : ℤ) * d.val - n : ℤ)) : ZMod M) * 1 := by
    rw [mul_one, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [e, HypPar.card_mul_eq r 1 _ (coprime_one_val _ (Nat.gcd_dvd_left _ _))]

lemma card_db (n : ℤ) (hn : Nat.Coprime n.natAbs M) (r a : ZMod M) :
    (∑ d : ZMod M, (univ.filter fun b : ZMod M => b * r = a * d - (n : ZMod M)).card) =
      Nat.gcd M r.val *
        (M / Nat.gcd M r.val * (if Nat.Coprime a.val (Nat.gcd M r.val) then 1 else 0)) := by
  have hgM : Nat.gcd M r.val ∣ M := Nat.gcd_dvd_left _ _
  have : NeZero (Nat.gcd M r.val) := ⟨(Nat.gcd_pos_of_pos_left _ (NeZero.pos M)).ne'⟩
  have h1 : ∀ d : ZMod M,
      (if ((Nat.gcd M r.val : ℕ) : ℤ) ∣ (a.val : ℤ) * d.val - n then Nat.gcd M r.val else 0) =
        Nat.gcd M r.val *
          (if ((Nat.gcd M r.val : ℕ) : ℤ) ∣ (a.val : ℤ) * d.val - n then 1 else 0) := by
    intro d; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun d _ => (card_b n r a d).trans (h1 d)), ← Finset.mul_sum,
    ← Finset.card_filter, card_dvd_val n hgM a.val, gf_gcd_eq n hn hgM]

theorem card_TR (n : ℤ) (hn : Nat.Coprime n.natAbs M) (r : ZMod M) :
    (TR M n r).card = M * (M / Nat.gcd M r.val) * Nat.totient (Nat.gcd M r.val) := by
  have hgM : Nat.gcd M r.val ∣ M := Nat.gcd_dvd_left _ _
  have h2 : ∀ a : ZMod M,
      (∑ p : ZMod M × ZMod M, if p.2 * r = a * p.1 - (n : ZMod M) then 1 else 0) =
        ∑ d : ZMod M, (univ.filter fun b : ZMod M => b * r = a * d - (n : ZMod M)).card := by
    intro a
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.card_filter]
  calc (TR M n r).card
      = ∑ a : ZMod M, ∑ p : ZMod M × ZMod M,
          (if p.2 * r = a * p.1 - (n : ZMod M) then 1 else 0) := by
        rw [card_TR_eq_triple, Finset.card_filter, Fintype.sum_prod_type]
    _ = ∑ a : ZMod M, Nat.gcd M r.val *
          (M / Nat.gcd M r.val * (if Nat.Coprime a.val (Nat.gcd M r.val) then 1 else 0)) :=
        Finset.sum_congr rfl fun a _ => (h2 a).trans (card_db n hn r a)
    _ = M * (M / Nat.gcd M r.val) * Nat.totient (Nat.gcd M r.val) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.card_filter, HypPar.card_coprime_val hgM,
          ← mul_assoc, Nat.mul_div_cancel' hgM, mul_assoc]

theorem card_TR_pos (n : ℤ) (hn : Nat.Coprime n.natAbs M) (r : ZMod M) :
    0 < (TR M n r).card := by
  rw [card_TR n hn]
  have hg : 0 < Nat.gcd M r.val := Nat.gcd_pos_of_pos_left _ (NeZero.pos M)
  exact Nat.mul_pos (Nat.mul_pos (NeZero.pos M)
    (Nat.div_pos (Nat.gcd_le_left _ (NeZero.pos M)) hg)) (Nat.totient_pos.mpr hg)

lemma gcd_val_neg (x : ZMod M) : Nat.gcd M (-x).val = Nat.gcd M x.val := by
  rw [← HypPar.card_mul_eq_zero, ← HypPar.card_mul_eq_zero]
  exact congrArg Finset.card (Finset.filter_congr (fun b _ => by rw [mul_neg, neg_eq_zero]))

theorem card_TR_neg (n : ℤ) (hn : Nat.Coprime n.natAbs M) (r : ZMod M) :
    (TR M n (-r)).card = (TR M n r).card := by
  rw [card_TR n hn, card_TR n hn, gcd_val_neg]

end RamanujanPetersson.EllW2


