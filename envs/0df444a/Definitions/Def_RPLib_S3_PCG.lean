-- Prove2me | Definitions.Def_RPLib_S3_PCG
-- name    : RPLib_S3_PCG
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:31:58.974322+00:00
-- url     : https://prove2.me/theorems/6081102f-2f88-4868-bdf4-2673ab409f09
-- title:
--   Weight-two Ramanujan-Petersson library: the recursion and the p-chain lemma
-- statement:
--   The recursion and the p-chain lemma.
--
--   With `E(δ, t, m) = ellCount(δ, t, p^m) - [m ≥ 2] p · ellCount(δ p⁻¹, t/p, p^(m-2))` (`Ef`), for `p ∣ t`:
--   `E = 0` if `p ∤ t/p` and `m ≥ 3` (`Ef_zero`), and `E(δ, t, m) = E(δ p⁻¹, t/p, m - 2)` if `p ∣ t/p` and `m ≥ 4`
--   (`Ef_rec`). Hence the sums `Ssum δ m = Σ_{p ∣ t, |t| ≤ 2p^m} |E(δ, t, m)|` satisfy `Ssum δ m = Ssum (δ p⁻¹) (m-2)`
--   for `m ≥ 4` and are bounded uniformly (`Ssum_bdd`): `PChainSum` and the frozen `PChain`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_PCF

/-!
# S3-DWS-Supersingular, part C (G): the recursion and the p-chain lemma

With `E(δ, t, m) = ellCount(δ, t, p^m) - [m ≥ 2] p · ellCount(δ p⁻¹, t/p, p^(m-2))` (`Ef`), for `p ∣ t`:
`E = 0` if `p ∤ t/p` and `m ≥ 3` (`Ef_zero`), and `E(δ, t, m) = E(δ p⁻¹, t/p, m - 2)` if `p ∣ t/p` and `m ≥ 4`
(`Ef_rec`). Hence the sums `Ssum δ m = Σ_{p ∣ t, |t| ≤ 2p^m} |E(δ, t, m)|` satisfy `Ssum δ m = Ssum (δ p⁻¹) (m-2)`
for `m ≥ 4` and are bounded uniformly (`Ssum_bdd`): `PChainSum` and the frozen `PChain`.
-/

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup RamanujanPetersson.S3.Conj

namespace RamanujanPetersson.S3.DWSS

/-- The p-chain error term. -/
noncomputable def Ef (M p : ℕ) [NeZero M] (δ : ZMod M) (t : ℤ) (m : ℕ) : ℚ :=
  ellCount M δ t (p ^ m) -
    (if 2 ≤ m then (p : ℚ) * ellCount M (δ * (p : ZMod M)⁻¹) (t / p) (p ^ (m - 2)) else 0)

/-- The total p-chain error at level `p^m`. -/
noncomputable def Ssum (M p : ℕ) [NeZero M] (δ : ZMod M) (m : ℕ) : ℚ :=
  ∑ t ∈ (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)).filter (fun t => (p : ℤ) ∣ t), |Ef M p δ t m|

section Rec

variable {M p : ℕ} [NeZero M] [Fact p.Prime]

lemma det_out {δ : ZMod M} {t : ℤ} {n : ℕ} (c : QE M δ t n) : (c.out : Mat).det = n :=
  (mem_EllPos_iff'.1 c.out.2).1

lemma trace_out {δ : ZMod M} {t : ℤ} {n : ℕ} (c : QE M δ t n) : (c.out : Mat).trace = t :=
  (mem_EllPos_iff'.1 c.out.2).2.1

lemma card_QE_eq_zero {δ : ZMod M} {t : ℤ} {n : ℕ} (h : 4 * (n : ℤ) ≤ t ^ 2) : Nat.card (QE M δ t n) = 0 := by
  have : IsEmpty (EllPos M δ t n) := ⟨fun x => by
    have := (mem_EllPos_iff'.1 x.2).2.2.2.1
    linarith⟩
  have : IsEmpty (QE M δ t n) := ⟨fun q => Quotient.inductionOn' q fun x => isEmptyElim x⟩
  exact Nat.card_of_isEmpty

theorem card_split_imp (hu : IsUnit (p : ZMod M)) {δ'' : ZMod M} {t' : ℤ} {n' : ℕ} :
    Nat.card (QE M (δ'' * p) (p * t') (p ^ 2 * n')) = Nat.card (QE M δ'' t' n') +
      Nat.card {C : QE M (δ'' * p) (p * t') (p ^ 2 * n') // ¬ DvdMat p (C.out : Mat)} := by
  have := finite_QE M (δ'' * p) (p * t') (p ^ 2 * n')
  have hs : Nat.card (QE M (δ'' * p) (p * t') (p ^ 2 * n')) =
      Nat.card {C : QE M (δ'' * p) (p * t') (p ^ 2 * n') // DvdMat p (C.out : Mat)} +
      Nat.card {C : QE M (δ'' * p) (p * t') (p ^ 2 * n') // ¬ DvdMat p (C.out : Mat)} := card_split _
  rwa [card_imp (Fact.out : p.Prime).pos hu] at hs

/-- **R1.** `p ∤ t'`, `p ∣ n'`: every class has `p - 1` non-stable lines. -/
theorem card_rec_tr (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) {δ'' : ZMod M} {t' : ℤ} {n' : ℕ}
    (ht : ¬ (p : ℤ) ∣ t') (hn : p ∣ n') :
    Nat.card (QE M (δ'' * p) (p * t') (p ^ 2 * n')) = p * Nat.card (QE M δ'' t' n') := by
  have := finite_QE M δ'' t' n'
  have := Fintype.ofFinite (QE M δ'' t' n')
  rw [card_split_imp hu, card_prim hM hu]
  have hN : ∀ c : QE M δ'' t' n', Nat.card {ℓ : Option (ZMod p) // qv p (c.out : Mat) ℓ ≠ 0} = p - 1 :=
    fun c => card_qv_tr (by rw [det_out]; exact_mod_cast hn) (by rw [trace_out]; exact ht)
  rw [Finset.sum_congr rfl (fun c _ => hN c), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card]
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  rw [hk, Nat.add_sub_cancel]; ring

/-- **R2.** `p ∣ t'`, `p ∣ n'`: non-divisible classes have `p` non-stable lines, divisible ones none. -/
theorem card_rec_nil (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) {δ'' : ZMod M} {t' : ℤ} {n' : ℕ}
    (ht : (p : ℤ) ∣ t') (hn : p ∣ n') :
    Nat.card (QE M (δ'' * p) (p * t') (p ^ 2 * n')) =
      Nat.card (QE M δ'' t' n') + p * Nat.card {c : QE M δ'' t' n' // ¬ DvdMat p (c.out : Mat)} := by
  classical
  have := finite_QE M δ'' t' n'
  have := Fintype.ofFinite (QE M δ'' t' n')
  rw [card_split_imp hu, card_prim hM hu,
    ← Fintype.sum_subtype_add_sum_subtype (fun c : QE M δ'' t' n' => DvdMat p (c.out : Mat))]
  have h1 : ∀ c : {c : QE M δ'' t' n' // DvdMat p (c.out : Mat)},
      Nat.card {ℓ : Option (ZMod p) // qv p ((c : QE M δ'' t' n').out : Mat) ℓ ≠ 0} = 0 :=
    fun c => card_qv_dvd c.2
  have h2 : ∀ c : {c : QE M δ'' t' n' // ¬ DvdMat p (c.out : Mat)},
      Nat.card {ℓ : Option (ZMod p) // qv p ((c : QE M δ'' t' n').out : Mat) ℓ ≠ 0} = p :=
    fun c => card_qv_nil (by rw [det_out]; exact_mod_cast hn) (by rw [trace_out]; exact ht) c.2
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_congr rfl (fun c _ => h2 c), Finset.sum_const_zero,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, zero_add, mul_comm]

theorem Ef_zero (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) (δ : ZMod M) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) {m : ℕ}
    (hm : 3 ≤ m) : Ef M p δ (p * s) m = 0 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e1 : δ * (p : ZMod M)⁻¹ * p = δ := by rw [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
  have e3 : p ^ 2 * p ^ (m - 2) = p ^ m := by rw [← pow_add]; congr 1; omega
  have hR := card_rec_tr (M := M) (p := p) hM hu (δ'' := δ * (p : ZMod M)⁻¹) (t' := s) (n' := p ^ (m - 2)) hs
    (dvd_pow_self p (by omega))
  rw [e1, e3] at hR
  rw [Ef, if_pos (by omega : 2 ≤ m), Int.mul_ediv_cancel_left _ hp0]
  simp only [ellCount_eq_card hM]
  rw [hR, Nat.cast_mul]; ring

theorem Ef_rec (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) (δ : ZMod M) {s : ℤ} (hs : (p : ℤ) ∣ s) {m : ℕ}
    (hm : 4 ≤ m) : Ef M p δ (p * s) m = Ef M p (δ * (p : ZMod M)⁻¹) s (m - 2) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e1 : δ * (p : ZMod M)⁻¹ * p = δ := by rw [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
  have e2 : δ * (p : ZMod M)⁻¹ * (p : ZMod M)⁻¹ * p = δ * (p : ZMod M)⁻¹ := by
    rw [mul_assoc (δ * (p : ZMod M)⁻¹), ZMod.inv_mul_of_unit _ hu, mul_one]
  have e3 : p ^ 2 * p ^ (m - 2) = p ^ m := by rw [← pow_add]; congr 1; omega
  have e4 : p ^ 2 * p ^ (m - 2 - 2) = p ^ (m - 2) := by rw [← pow_add]; congr 1; omega
  have e5 : (p : ℤ) * (s / p) = s := Int.mul_ediv_cancel' hs
  have hR := card_rec_nil (M := M) (p := p) hM hu (δ'' := δ * (p : ZMod M)⁻¹) (t' := s) (n' := p ^ (m - 2)) hs
    (dvd_pow_self p (by omega))
  rw [e1, e3] at hR
  have hY := card_split_imp (M := M) (p := p) hu (δ'' := δ * (p : ZMod M)⁻¹ * (p : ZMod M)⁻¹) (t' := s / p)
    (n' := p ^ (m - 2 - 2))
  rw [e2, e4, e5] at hY
  rw [Ef, Ef, if_pos (by omega : 2 ≤ m), if_pos (by omega : 2 ≤ m - 2), Int.mul_ediv_cancel_left _ hp0]
  simp only [ellCount_eq_card hM]
  rw [hR, hY]; push_cast; ring

theorem Ef_eq_zero_of_le (hM : 4 ≤ M) (δ : ZMod M) {t : ℤ} (ht : (p : ℤ) ∣ t) {m : ℕ}
    (h : 4 * (p : ℤ) ^ m ≤ t ^ 2) : Ef M p δ t m = 0 := by
  obtain ⟨u, rfl⟩ := ht
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [Ef, ellCount_eq_card hM δ (p * u) (p ^ m), card_QE_eq_zero (M := M) (δ := δ) (t := p * u) (n := p ^ m) (by push_cast; exact h)]
  split_ifs with hm
  · rw [Int.mul_ediv_cancel_left _ hp0.ne', ellCount_eq_card hM, card_QE_eq_zero]
    · simp
    · have e : (p : ℤ) ^ m = p ^ 2 * p ^ (m - 2) := by rw [← pow_add]; congr 1; omega
      have h' : (p : ℤ) ^ 2 * (4 * p ^ (m - 2)) ≤ p ^ 2 * u ^ 2 := by
        calc (p : ℤ) ^ 2 * (4 * p ^ (m - 2)) = 4 * (p : ℤ) ^ m := by rw [e]; ring
          _ ≤ (p * u) ^ 2 := h
          _ = p ^ 2 * u ^ 2 := by ring
      push_cast
      exact le_of_mul_le_mul_left h' (pow_pos hp0 2)
  · simp

theorem Ssum_nonneg (δ : ZMod M) (m : ℕ) : 0 ≤ Ssum M p δ m := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem Ssum_rec (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) (δ : ZMod M) {m : ℕ} (hm : 4 ≤ m) :
    Ssum M p δ m = Ssum M p (δ * (p : ZMod M)⁻¹) (m - 2) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have e : (p : ℤ) ^ m = p ^ 2 * p ^ (m - 2) := by rw [← pow_add]; congr 1; omega
  have hP : (1 : ℤ) ≤ p ^ (m - 2) := one_le_pow₀ (by omega)
  have hPP : (p : ℤ) ^ (m - 2) ≤ p ^ (m - 2) * p ^ (m - 2) := le_mul_of_one_le_right (by linarith) hP
  have hp1 : (1 : ℤ) ≤ p := by omega
  have hpp : (p : ℤ) ≤ p ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hp1 hp0.le]
  have key : ∀ t : ℤ, (p : ℤ) ∣ t → |Ef M p δ t m| ≠ 0 →
      (p : ℤ) ∣ t / p ∧ Ef M p δ t m = Ef M p (δ * (p : ZMod M)⁻¹) (t / p) (m - 2) := by
    intro t ht h0
    obtain ⟨s, rfl⟩ := ht
    rw [Int.mul_ediv_cancel_left _ hp0.ne']
    by_cases hs : (p : ℤ) ∣ s
    · exact ⟨hs, Ef_rec hM hu δ hs hm⟩
    · exact (h0 (by rw [Ef_zero hM hu δ hs (by omega), abs_zero])).elim
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
    rw [hE, Ef_eq_zero_of_le hM _ hs hw, abs_zero]
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
    · rwa [Ef_rec hM hu δ hs.2 hm]
  · intro t ht h0
    exact congrArg abs (key t (Finset.mem_filter.1 ht).2 h0).2

theorem Ssum_bdd (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) :
    ∃ C : ℚ, 0 ≤ C ∧ ∀ (m : ℕ) (δ : ZMod M), Ssum M p δ m ≤ C := by
  refine ⟨∑ δ : ZMod M, ∑ m ∈ Finset.range 4, Ssum M p δ m,
    Finset.sum_nonneg fun δ _ => Finset.sum_nonneg fun m _ => Ssum_nonneg δ m, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro δ
    by_cases hm : m < 4
    · calc Ssum M p δ m ≤ ∑ m ∈ Finset.range 4, Ssum M p δ m :=
            Finset.single_le_sum (f := fun m => Ssum M p δ m) (fun m _ => Ssum_nonneg δ m)
              (Finset.mem_range.2 hm)
        _ ≤ ∑ δ : ZMod M, ∑ m ∈ Finset.range 4, Ssum M p δ m :=
            Finset.single_le_sum (f := fun δ => ∑ m ∈ Finset.range 4, Ssum M p δ m)
              (fun δ _ => Finset.sum_nonneg fun m _ => Ssum_nonneg δ m) (Finset.mem_univ δ)
    · rw [Ssum_rec hM hu δ (by omega)]
      exact ih (m - 2) (by omega) _

end Rec

end RamanujanPetersson.S3.DWSS

namespace RamanujanPetersson.S3

open DWSS

/-- (S3-DWS-Supersingular, sum form; needed by S3-Matching) The p-chain errors summed over `p ∣ t` are bounded
uniformly in `m`. -/
def PChainSum : Prop :=
  ∀ (M : ℕ) [NeZero M], 4 ≤ M → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∃ C : ℚ, ∀ m : ℕ,
    ∑ t ∈ (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)).filter (fun t => (p : ℤ) ∣ t),
      |ellCount M 1 t (p ^ m) - (if 2 ≤ m then p * ellCount M (p : ZMod M)⁻¹ (t / p) (p ^ (m - 2)) else 0)| ≤ C

theorem pChainSum : PChainSum := by
  intro M _ hM p _ hpM
  have hu : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd (Fact.out : p.Prime)).2 hpM
  obtain ⟨C, -, hC⟩ := Ssum_bdd (M := M) (p := p) hM hu
  refine ⟨C, fun m => ?_⟩
  have := hC m 1
  simpa only [Ssum, Ef, one_mul] using this

theorem pChain : PChain := by
  intro M _ hM p _ hpM
  have hu : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd (Fact.out : p.Prime)).2 hpM
  obtain ⟨C, hC0, hC⟩ := Ssum_bdd (M := M) (p := p) hM hu
  refine ⟨C, fun m t ht => ?_⟩
  have hE : |Ef M p 1 t m| ≤ C := by
    by_cases hin : t ∈ Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)
    · exact le_trans (Finset.single_le_sum (f := fun t => |Ef M p 1 t m|) (fun _ _ => abs_nonneg _)
        (Finset.mem_filter.2 ⟨hin, ht⟩)) (hC m 1)
    · have hQ : (1 : ℤ) ≤ p ^ m := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
      have hQQ : (p : ℤ) ^ m ≤ p ^ m * p ^ m := le_mul_of_one_le_right (by linarith) hQ
      have hw : 4 * (p : ℤ) ^ m ≤ t ^ 2 := by
        rw [Finset.mem_Icc, not_and_or] at hin
        rcases hin with h | h <;> push_neg at h
        · nlinarith [mul_pos (by linarith : (0 : ℤ) < -(2 * p ^ m) - t) (by linarith : (0 : ℤ) < 2 * p ^ m - t)]
        · nlinarith [mul_pos (by linarith : (0 : ℤ) < t - 2 * p ^ m) (by linarith : (0 : ℤ) < t + 2 * p ^ m)]
      rw [Ef_eq_zero_of_le hM 1 ht hw, abs_zero]
      exact hC0
  simpa only [Ef, one_mul] using hE

end RamanujanPetersson.S3


