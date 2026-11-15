-- Prove2me | Definitions.Def_RPLib_S3_DWSOEB
-- name    : RPLib_S3_DWSOEB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:33:45.248293+00:00
-- url     : https://prove2.me/theorems/2aa0a2ab-6b97-412c-ac05-d80ea746f3bf
-- title:
--   Weight-two Ramanujan-Petersson library: the level-one p-chain (no hypothesis)
-- statement:
--   The level-one p-chain (no hypothesis).
--
--   `E1(t, m) = Ef 1 p 1 t m = ellCount_1(t, p^m) - [m ≥ 2] p · ellCount_1(t/p, p^(m-2))`. For `D = t² - 4p^m ≠ 0` pick a
--   prime `ℓ ∣ 36 p² D - 1` (`exists_ell`): then `ℓ ≥ 5`, `ℓ ∤ pD` and `x² - tx + p^m` has a root mod `ℓ`, so summing the
--   level-`ℓ` identities `Ef_zero`, `Ef_rec` of `PC_G` over `δ` (`sum_Ef`, `DWSO_EA.sum_ellCount`) gives
--   * `Ef1_zero` : `E1(ps, m) = 0` for `p ∤ s`, `m ≥ 3`; `Ef1_rec` : `E1(ps, m) = E1(s, m - 2)` for `p ∣ s`, `m ≥ 4`;
--   * **`Ssum1_bdd`** : `Σ_{p ∣ t, |t| ≤ 2p^m} |E1(t, m)| ≤ C` uniformly in `m`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOEA
import Definitions.Def_RPLib_S3_PCG

/-!
# S3-DWS-Ordinary, part EB: the level-one p-chain (no hypothesis)

`E1(t, m) = Ef 1 p 1 t m = ellCount_1(t, p^m) - [m ≥ 2] p · ellCount_1(t/p, p^(m-2))`. For `D = t² - 4p^m ≠ 0` pick a
prime `ℓ ∣ 36 p² D - 1` (`exists_ell`): then `ℓ ≥ 5`, `ℓ ∤ pD` and `x² - tx + p^m` has a root mod `ℓ`, so summing the
level-`ℓ` identities `Ef_zero`, `Ef_rec` of `PC_G` over `δ` (`sum_Ef`, `DWSO_EA.sum_ellCount`) gives
* `Ef1_zero` : `E1(ps, m) = 0` for `p ∤ s`, `m ≥ 3`; `Ef1_rec` : `E1(ps, m) = E1(s, m - 2)` for `p ∣ s`, `m ≥ 4`;
* **`Ssum1_bdd`** : `Σ_{p ∣ t, |t| ≤ 2p^m} |E1(t, m)| ≤ C` uniformly in `m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open RamanujanPetersson.S3.Conj RamanujanPetersson.S3.DWSS

namespace RamanujanPetersson.S3.DWSO

lemma neg_of_mem_redForms {D : ℤ} {Q : ℤ × ℤ × ℤ} (hQ : Q ∈ redForms D) : D < 0 := by
  rw [redForms, Finset.mem_filter] at hQ
  obtain ⟨-, h1, hD, h2, h3, h4, -⟩ := hQ
  nlinarith [mul_nonneg (sub_nonneg.2 h3) (by linarith : (0 : ℤ) ≤ Q.1 + Q.2.1),
    mul_nonneg (by linarith : (0 : ℤ) ≤ Q.1) (sub_nonneg.2 h4)]

lemma ellCount_eq_zero_of_le {M : ℕ} [NeZero M] (δ : ZMod M) {t : ℤ} {n : ℕ} (h : 4 * (n : ℤ) ≤ t ^ 2) :
    ellCount M δ t n = 0 := by
  unfold ellCount
  refine Finset.sum_eq_zero fun Q hQ => ?_
  exact absurd (neg_of_mem_redForms hQ) (by linarith)

/-- A prime `ℓ ≥ 4`, prime to `p` and to `t² - 4n`, modulo which `x² - t x + n` has a root. -/
theorem exists_ell (p : ℕ) [Fact p.Prime] (t n : ℤ) (hD : t ^ 2 - 4 * n ≠ 0) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 4 ≤ ℓ ∧ (p : ZMod ℓ) ≠ 0 ∧ ¬ (ℓ : ℤ) ∣ t ^ 2 - 4 * n ∧
      ∃ x : ZMod ℓ, x ^ 2 - (t : ZMod ℓ) * x + (n : ZMod ℓ) = 0 := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hX : (p : ℤ) ^ 2 * (t ^ 2 - 4 * n) ≠ 0 := mul_ne_zero (pow_ne_zero 2 (by omega)) hD
  have hK1 : (36 * ((p : ℤ) ^ 2 * (t ^ 2 - 4 * n)) - 1).natAbs ≠ 1 := by
    generalize (p : ℤ) ^ 2 * (t ^ 2 - 4 * n) = X at hX
    intro h
    rcases Int.natAbs_eq_iff.mp h with h | h <;> push_cast at h <;> omega
  set ℓ := (36 * ((p : ℤ) ^ 2 * (t ^ 2 - 4 * n)) - 1).natAbs.minFac with hℓdef
  have hℓ : ℓ.Prime := Nat.minFac_prime hK1
  haveI := Fact.mk hℓ
  have hdvd : (ℓ : ℤ) ∣ 36 * ((p : ℤ) ^ 2 * (t ^ 2 - 4 * n)) - 1 :=
    Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _)
  have hK : (36 : ZMod ℓ) * (p : ZMod ℓ) ^ 2 * ((t : ZMod ℓ) ^ 2 - 4 * (n : ZMod ℓ)) = 1 := by
    have h0 := (CharP.intCast_eq_zero_iff (ZMod ℓ) ℓ _).mpr hdvd
    push_cast at h0
    linear_combination h0
  have h36 : ¬ ℓ ∣ 36 := fun h => by
    have h0 : ((36 : ℕ) : ZMod ℓ) = 0 := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 36).mpr h
    push_cast at h0
    rw [h0] at hK
    simp at hK
  have hl2 : ℓ ≠ 2 := fun h => h36 (by rw [h]; norm_num)
  have hl3 : ℓ ≠ 3 := fun h => h36 (by rw [h]; norm_num)
  have hl4 : 4 ≤ ℓ := by have := hℓ.two_le; omega
  have hpne : (p : ZMod ℓ) ≠ 0 := fun h => by rw [h] at hK; simp at hK
  have h6ne : (6 : ZMod ℓ) * p ≠ 0 := fun h => by
    have : (36 : ZMod ℓ) * (p : ZMod ℓ) ^ 2 = 0 := by linear_combination (6 * (p : ZMod ℓ)) * h
    rw [this] at hK; simp at hK
  have h2ne : (2 : ZMod ℓ) ≠ 0 := fun h => by
    have h0 : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    exact h36 (dvd_trans ((CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 2).mp h0) (by norm_num))
  refine ⟨ℓ, hℓ, hl4, hpne, fun h => ?_, ?_⟩
  · have h0 := (CharP.intCast_eq_zero_iff (ZMod ℓ) ℓ _).mpr h
    push_cast at h0
    rw [h0] at hK; simp at hK
  · set s := ((6 : ZMod ℓ) * p)⁻¹
    have h6 : (6 : ZMod ℓ) * p * s = 1 := mul_inv_cancel₀ h6ne
    have h2 : (2 : ZMod ℓ) * 2⁻¹ = 1 := mul_inv_cancel₀ h2ne
    refine ⟨((t : ZMod ℓ) + s) * 2⁻¹, ?_⟩
    have hsx : 2 * (((t : ZMod ℓ) + s) * 2⁻¹) - t = s := by linear_combination ((t : ZMod ℓ) + s) * h2
    have hss : s ^ 2 = (t : ZMod ℓ) ^ 2 - 4 * (n : ZMod ℓ) := by
      linear_combination (-s ^ 2) * hK + ((t : ZMod ℓ) ^ 2 - 4 * (n : ZMod ℓ)) * (6 * p * s + 1) * h6
    have h4 : (4 : ZMod ℓ) * ((((t : ZMod ℓ) + s) * 2⁻¹) ^ 2 - t * (((t : ZMod ℓ) + s) * 2⁻¹) + n) = 0 := by
      linear_combination (2 * (((t : ZMod ℓ) + s) * 2⁻¹) - t + s) * hsx + hss
    have h4ne : (4 : ZMod ℓ) ≠ 0 := by
      have : (4 : ZMod ℓ) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2ne h2ne
    exact (mul_eq_zero.mp h4).resolve_left h4ne

section Ell

variable {ℓ : ℕ} [NeZero ℓ] [Fact ℓ.Prime] {p : ℕ} [Fact p.Prime]

lemma rootCount_mul (hp : (p : ZMod ℓ) ≠ 0) (s n' : ℤ) :
    rootCount ℓ ((p : ℤ) * s) ((p : ℤ) ^ 2 * n') = rootCount ℓ s n' := by
  unfold rootCount
  refine Finset.card_bij' (fun x _ => (p : ZMod ℓ)⁻¹ * x) (fun y _ => (p : ZMod ℓ) * y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hy : x = (p : ZMod ℓ) * ((p : ZMod ℓ)⁻¹ * x) := (mul_inv_cancel_left₀ hp x).symm
    have h := hx.2
    rw [hy] at h
    push_cast at h
    have h' : (p : ZMod ℓ) ^ 2 * (((p : ZMod ℓ)⁻¹ * x) ^ 2 - (s : ZMod ℓ) * ((p : ZMod ℓ)⁻¹ * x) + n') = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 hp)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    push_cast
    linear_combination (p : ZMod ℓ) ^ 2 * hy.2
  · intro x _; exact mul_inv_cancel_left₀ hp x
  · intro y _; exact inv_mul_cancel_left₀ hp y

lemma sum_shift {u : ZMod ℓ} (hu : u ≠ 0) (g : ZMod ℓ → ℚ) : ∑ δ, g (δ * u) = ∑ δ, g δ :=
  Fintype.sum_bijective _ (mulRight_bijective₀ u hu) _ _ (fun _ => rfl)

/-- Summing the level-`ℓ` p-chain error over `δ` gives `(ℓ - 1) r` times the level-one error. -/
theorem sum_Ef (hp : (p : ZMod ℓ) ≠ 0) (s : ℤ) {m : ℕ} (hm : 2 ≤ m)
    (hD : ¬ (ℓ : ℤ) ∣ ((p : ℤ) * s) ^ 2 - 4 * ((p ^ m : ℕ) : ℤ)) :
    ∑ δ : ZMod ℓ, Ef ℓ p δ ((p : ℤ) * s) m =
      (((ℓ - 1) * rootCount ℓ ((p : ℤ) * s) ((p ^ m : ℕ) : ℤ) : ℕ) : ℚ) * Ef 1 p 1 ((p : ℤ) * s) m := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e3 : ((p ^ m : ℕ) : ℤ) = (p : ℤ) ^ 2 * ((p ^ (m - 2) : ℕ) : ℤ) := by
    push_cast; rw [← pow_add]; congr 1; omega
  have hD' : ¬ (ℓ : ℤ) ∣ s ^ 2 - 4 * ((p ^ (m - 2) : ℕ) : ℤ) := fun h => hD (by
    rw [e3, show ((p : ℤ) * s) ^ 2 - 4 * ((p : ℤ) ^ 2 * ((p ^ (m - 2) : ℕ) : ℤ)) =
      (p : ℤ) ^ 2 * (s ^ 2 - 4 * ((p ^ (m - 2) : ℕ) : ℤ)) by ring]
    exact Dvd.dvd.mul_left h _)
  have hr : rootCount ℓ ((p : ℤ) * s) ((p ^ m : ℕ) : ℤ) = rootCount ℓ s ((p ^ (m - 2) : ℕ) : ℤ) := by
    rw [e3]; exact rootCount_mul hp s _
  have e1 : (1 : ZMod 1) * (p : ZMod 1)⁻¹ = 1 := Subsingleton.elim _ _
  simp only [Ef, if_pos hm, Int.mul_ediv_cancel_left _ hp0, Finset.sum_sub_distrib, ← Finset.mul_sum, e1]
  rw [sum_shift (g := fun δ => ellCount ℓ δ s (p ^ (m - 2))) (inv_ne_zero hp), sum_ellCount _ _ hD,
    sum_ellCount _ _ hD', hr]
  push_cast
  ring

end Ell

section One

variable {p : ℕ} [Fact p.Prime]

theorem Ef1_le (δ : ZMod 1) {t : ℤ} (ht : (p : ℤ) ∣ t) {m : ℕ} (h : 4 * (p : ℤ) ^ m ≤ t ^ 2) :
    Ef 1 p δ t m = 0 := by
  obtain ⟨u, rfl⟩ := ht
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [Ef, ellCount_eq_zero_of_le _ (by push_cast; exact h)]
  split_ifs with hm
  · rw [Int.mul_ediv_cancel_left _ hp0.ne', ellCount_eq_zero_of_le]
    · simp
    · have e : (p : ℤ) ^ m = p ^ 2 * p ^ (m - 2) := by rw [← pow_add]; congr 1; omega
      have h' : (p : ℤ) ^ 2 * (4 * p ^ (m - 2)) ≤ p ^ 2 * u ^ 2 := by
        calc (p : ℤ) ^ 2 * (4 * p ^ (m - 2)) = 4 * (p : ℤ) ^ m := by rw [e]; ring
          _ ≤ (p * u) ^ 2 := h
          _ = p ^ 2 * u ^ 2 := by ring
      push_cast
      exact le_of_mul_le_mul_left h' (pow_pos hp0 2)
  · simp

/-- Common setup: for `D ≠ 0` an auxiliary prime with nonzero `(ℓ - 1) r`. -/
theorem exists_aux (s : ℤ) (m : ℕ) (hD : ((p : ℤ) * s) ^ 2 - 4 * ((p ^ m : ℕ) : ℤ) ≠ 0) :
    ∃ ℓ : ℕ, ∃ _ : NeZero ℓ, ∃ _ : Fact ℓ.Prime, 4 ≤ ℓ ∧ (p : ZMod ℓ) ≠ 0 ∧
      ¬ (ℓ : ℤ) ∣ ((p : ℤ) * s) ^ 2 - 4 * ((p ^ m : ℕ) : ℤ) ∧
      (((ℓ - 1) * rootCount ℓ ((p : ℤ) * s) ((p ^ m : ℕ) : ℤ) : ℕ) : ℚ) ≠ 0 := by
  obtain ⟨ℓ, hℓ, hl4, hp, hdv, x, hx⟩ := exists_ell p ((p : ℤ) * s) ((p ^ m : ℕ) : ℤ) hD
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine ⟨ℓ, inferInstance, ⟨hℓ⟩, hl4, hp, hdv, ?_⟩
  have hr : 0 < rootCount ℓ ((p : ℤ) * s) ((p ^ m : ℕ) : ℤ) :=
    Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩
  have : 0 < ℓ - 1 := by omega
  exact_mod_cast (Nat.mul_pos this hr).ne'

theorem Ef1_zero {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) {m : ℕ} (hm : 3 ≤ m) : Ef 1 p 1 ((p : ℤ) * s) m = 0 := by
  by_cases hD : ((p : ℤ) * s) ^ 2 - 4 * ((p ^ m : ℕ) : ℤ) = 0
  · exact Ef1_le 1 (dvd_mul_right _ _) (by push_cast at hD; linarith)
  obtain ⟨ℓ, _, _, hl4, hp, hdv, hne⟩ := exists_aux s m hD
  have hu : IsUnit (p : ZMod ℓ) := isUnit_iff_ne_zero.mpr hp
  have h := sum_Ef hp s (by omega) hdv
  rw [Finset.sum_eq_zero fun δ _ => Ef_zero hl4 hu δ hs hm] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hne

theorem Ef1_rec {s : ℤ} (hs : (p : ℤ) ∣ s) {m : ℕ} (hm : 4 ≤ m) :
    Ef 1 p 1 ((p : ℤ) * s) m = Ef 1 p 1 s (m - 2) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨s', rfl⟩ := hs
  have e3 : ((p ^ m : ℕ) : ℤ) = (p : ℤ) ^ 2 * ((p ^ (m - 2) : ℕ) : ℤ) := by
    push_cast; rw [← pow_add]; congr 1; omega
  have hDD : ((p : ℤ) * (p * s')) ^ 2 - 4 * ((p ^ m : ℕ) : ℤ) =
      (p : ℤ) ^ 2 * (((p : ℤ) * s') ^ 2 - 4 * ((p ^ (m - 2) : ℕ) : ℤ)) := by rw [e3]; ring
  by_cases hD : ((p : ℤ) * (p * s')) ^ 2 - 4 * ((p ^ m : ℕ) : ℤ) = 0
  · have hD' : ((p : ℤ) * s') ^ 2 - 4 * ((p ^ (m - 2) : ℕ) : ℤ) = 0 := by
      rw [hDD] at hD; exact (mul_eq_zero.mp hD).resolve_left (pow_ne_zero 2 hp0.ne')
    rw [Ef1_le 1 (dvd_mul_right _ _) (by push_cast at hD; linarith),
      Ef1_le 1 (dvd_mul_right _ _) (by push_cast at hD'; linarith)]
  obtain ⟨ℓ, _, _, hl4, hp, hdv, hne⟩ := exists_aux (p * s') m hD
  have hu : IsUnit (p : ZMod ℓ) := isUnit_iff_ne_zero.mpr hp
  have hdv' : ¬ (ℓ : ℤ) ∣ ((p : ℤ) * s') ^ 2 - 4 * ((p ^ (m - 2) : ℕ) : ℤ) := fun h =>
    hdv (by rw [hDD]; exact Dvd.dvd.mul_left h _)
  have h1 := sum_Ef hp (p * s') (by omega) hdv
  have h2 := sum_Ef hp s' (by omega : 2 ≤ m - 2) hdv'
  have hr : rootCount ℓ ((p : ℤ) * (p * s')) ((p ^ m : ℕ) : ℤ) =
      rootCount ℓ ((p : ℤ) * s') ((p ^ (m - 2) : ℕ) : ℤ) := by rw [e3]; exact rootCount_mul hp _ _
  rw [Finset.sum_congr rfl fun δ _ => Ef_rec hl4 hu δ (dvd_mul_right (p : ℤ) s') hm,
    sum_shift (g := fun δ => Ef ℓ p δ (p * s') (m - 2)) (inv_ne_zero hp), h2, ← hr] at h1
  exact (mul_left_cancel₀ hne h1).symm

theorem Ssum1_rec {m : ℕ} (hm : 4 ≤ m) : Ssum 1 p 1 m = Ssum 1 p 1 (m - 2) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have e : (p : ℤ) ^ m = p ^ 2 * p ^ (m - 2) := by rw [← pow_add]; congr 1; omega
  have hP : (1 : ℤ) ≤ p ^ (m - 2) := one_le_pow₀ (by omega)
  have hp1 : (1 : ℤ) ≤ p := by omega
  have hpp : (p : ℤ) ≤ p ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hp1 hp0.le]
  have key : ∀ t : ℤ, (p : ℤ) ∣ t → |Ef 1 p 1 t m| ≠ 0 →
      (p : ℤ) ∣ t / p ∧ Ef 1 p 1 t m = Ef 1 p 1 (t / p) (m - 2) := by
    intro t ht h0
    obtain ⟨s, rfl⟩ := ht
    rw [Int.mul_ediv_cancel_left _ hp0.ne']
    by_cases hs : (p : ℤ) ∣ s
    · exact ⟨hs, Ef1_rec hs hm⟩
    · exact (h0 (by rw [Ef1_zero hs (by omega), abs_zero])).elim
  unfold Ssum
  refine Finset.sum_bij_ne_zero (fun (t : ℤ) _ _ => t / (p : ℤ)) ?_ ?_ ?_ ?_
  · intro t ht h0
    show t / (p : ℤ) ∈ _
    rw [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
    obtain ⟨hs, hE⟩ := key t ht.2 h0
    refine ⟨?_, hs⟩
    by_contra hout
    apply h0
    have hw : 4 * (p : ℤ) ^ (m - 2) ≤ (t / p) ^ 2 := by
      rcases not_and_or.1 hout with h | h <;> push_neg at h
      · nlinarith [mul_pos (by linarith : (0 : ℤ) < -(2 * p ^ (m - 2)) - t / p)
          (by linarith : (0 : ℤ) < 2 * p ^ (m - 2) - t / p)]
      · nlinarith [mul_pos (by linarith : (0 : ℤ) < t / p - 2 * p ^ (m - 2))
          (by linarith : (0 : ℤ) < t / p + 2 * p ^ (m - 2))]
    rw [hE, Ef1_le _ hs hw, abs_zero]
  · intro t₁ ht₁ _ t₂ ht₂ _ h
    rw [Finset.mem_filter] at ht₁ ht₂
    rw [← Int.ediv_mul_cancel ht₁.2, ← Int.ediv_mul_cancel ht₂.2]
    exact congrArg (· * (p : ℤ)) h
  · intro s hs h0
    rw [Finset.mem_filter, Finset.mem_Icc] at hs
    refine ⟨p * s, ?_, ?_, Int.mul_ediv_cancel_left _ hp0.ne'⟩
    · rw [Finset.mem_filter, Finset.mem_Icc, e]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
      · nlinarith [mul_le_mul_of_nonneg_left hs.1.1 hp0.le,
          mul_le_mul_of_nonneg_right hpp (by linarith : (0 : ℤ) ≤ 2 * p ^ (m - 2))]
      · nlinarith [mul_le_mul_of_nonneg_left hs.1.2 hp0.le,
          mul_le_mul_of_nonneg_right hpp (by linarith : (0 : ℤ) ≤ 2 * p ^ (m - 2))]
    · rwa [Ef1_rec hs.2 hm]
  · intro t ht h0
    exact congrArg abs (key t (Finset.mem_filter.1 ht).2 h0).2

/-- **Level-one p-chain sum.** `Σ_{p ∣ t, |t| ≤ 2p^m} |E1(t, m)|` is bounded uniformly in `m`. -/
theorem Ssum1_bdd : ∃ C : ℚ, 0 ≤ C ∧ ∀ m : ℕ, Ssum 1 p 1 m ≤ C := by
  refine ⟨∑ m ∈ Finset.range 4, Ssum 1 p 1 m, Finset.sum_nonneg fun m _ => Ssum_nonneg 1 m, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 4
    · exact Finset.single_le_sum (f := fun m => Ssum 1 p 1 m) (fun m _ => Ssum_nonneg 1 m)
        (Finset.mem_range.2 hm)
    · rw [Ssum1_rec (by omega)]
      exact ih (m - 2) (by omega)

end One

end RamanujanPetersson.S3.DWSO


