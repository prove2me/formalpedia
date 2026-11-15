-- Prove2me | Definitions.Def_RPLib_S3_MatchingE
-- name    : RPLib_S3_MatchingE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:20:02.112931+00:00
-- url     : https://prove2.me/theorems/a1a57af2-f4cb-4bc9-968c-8239b48a499f
-- title:
--   Weight-two Ramanujan-Petersson library: the elliptic terms at `p^m` and the `p`-chain
-- statement:
--   The elliptic terms at `p^m` and the `p`-chain.
--
--   * `ellG1_eq_Icc`: `ellG1 M k n δ = -Σ_{|t| ≤ 2n} U_{k-2}(t, n) ellCount_M(δ⁻¹, t, n)`.
--   * `chain_reindex`: `p^{k-1} Σ_{|s| ≤ 2q'} U(s, q') E(s) = Σ_{|t| ≤ 2p²q', p ∣ t} U(t, p²q') p E(t/p)` when `E` vanishes
--     outside the Hasse range (`SymTrace.U_smul`, `t = p s`).
--   * `ell_split` (`1 ≤ m`): `ellG1(p^m, 1) - [m ≥ 2] p^{k-1} ellG1(p^{m-2}, p) =
--     -Σ_{p ∤ t} U ellCount(1, t) - Σ_{p ∣ t} U (ellCount(1, t) - [m ≥ 2] p ellCount(p⁻¹, t/p, p^{m-2}))`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_Statements
import Definitions.Def_RPLib_S3_EllipticTermC

/-!
# S3-Matching, part E: the elliptic terms at `p^m` and the `p`-chain

* `ellG1_eq_Icc`: `ellG1 M k n δ = -Σ_{|t| ≤ 2n} U_{k-2}(t, n) ellCount_M(δ⁻¹, t, n)`.
* `chain_reindex`: `p^{k-1} Σ_{|s| ≤ 2q'} U(s, q') E(s) = Σ_{|t| ≤ 2p²q', p ∣ t} U(t, p²q') p E(t/p)` when `E` vanishes
  outside the Hasse range (`SymTrace.U_smul`, `t = p s`).
* `ell_split` (`1 ≤ m`): `ellG1(p^m, 1) - [m ≥ 2] p^{k-1} ellG1(p^{m-2}, p) =
  -Σ_{p ∤ t} U ellCount(1, t) - Σ_{p ∣ t} U (ellCount(1, t) - [m ≥ 2] p ellCount(p⁻¹, t/p, p^{m-2}))`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

variable {M : ℕ} [NeZero M]

lemma ellG1_eq_Icc (k n : ℕ) (δ : ZMod M) :
    ellG1 M k n δ =
      -∑ t ∈ Finset.Icc (-(2 * n : ℤ)) (2 * n), (chebU (k - 2) t n : ℚ) * ellCount M δ⁻¹ t n := by
  unfold ellG1
  congr 1
  refine Finset.sum_nbij' (fun i : ℕ => (i : ℤ) - 2 * n) (fun t => (t + 2 * n).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢; omega
  · intro t ht; simp only [Finset.mem_range, Finset.mem_Icc] at ht ⊢; omega
  · intro i _; omega
  · intro t ht; simp only [Finset.mem_Icc] at ht; omega
  · intro i _; rfl

lemma chain_reindex (p : ℕ) (hp : p.Prime) (k m : ℕ) (hk : 2 ≤ k) (E : ℤ → ℚ)
    (hE : ∀ s : ℤ, 4 * ((p ^ m : ℕ) : ℤ) ≤ s ^ 2 → E s = 0) :
    (p : ℚ) ^ (k - 1) * ∑ s ∈ Finset.Icc (-(2 * (p ^ m : ℕ) : ℤ)) (2 * (p ^ m : ℕ)),
        (chebU (k - 2) s (p ^ m : ℕ) : ℚ) * E s =
      ∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ (m + 2))) (2 * (p : ℤ) ^ (m + 2))).filter (fun t => (p : ℤ) ∣ t),
        (chebU (k - 2) t (p ^ (m + 2) : ℕ) : ℚ) * (p * E (t / p)) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hQ1 : (1 : ℤ) ≤ (p : ℤ) ^ m := one_le_pow₀ hp1
  have hterm : ∀ s : ℤ, (p : ℚ) ^ (k - 1) * ((chebU (k - 2) s (p ^ m : ℕ) : ℚ) * E s) =
      (chebU (k - 2) (p * s) (p ^ (m + 2) : ℕ) : ℚ) * (p * E s) := by
    intro s
    have hU := SymTrace.U_smul (R := ℤ) (k - 2) (p : ℤ) s ((p ^ m : ℕ) : ℤ)
    have hq : ((p ^ (m + 2) : ℕ) : ℤ) = (p : ℤ) ^ 2 * ((p ^ m : ℕ) : ℤ) := by push_cast; ring
    unfold chebU
    rw [hq, hU]
    have hk' : k - 1 = (k - 2) + 1 := by omega
    rw [hk', pow_succ]; push_cast; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun s _ => hterm s)]
  have hsub : (Finset.Icc (-(2 * (p ^ m : ℕ) : ℤ)) (2 * (p ^ m : ℕ))).image (fun s => (p : ℤ) * s) ⊆
      (Finset.Icc (-(2 * (p : ℤ) ^ (m + 2))) (2 * (p : ℤ) ^ (m + 2))).filter (fun t => (p : ℤ) ∣ t) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_Icc] at hs
    push_cast at hs
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hq : (p : ℤ) ^ (m + 2) = p ^ 2 * p ^ m := by ring
    have hpp : (p : ℤ) * p ^ m ≤ p ^ 2 * p ^ m :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    rw [hq]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · nlinarith [mul_le_mul_of_nonneg_left hs.1 (by linarith : (0 : ℤ) ≤ p)]
    · nlinarith [mul_le_mul_of_nonneg_left hs.2 (by linarith : (0 : ℤ) ≤ p)]
  have hvan : ∀ x ∈ (Finset.Icc (-(2 * (p : ℤ) ^ (m + 2))) (2 * (p : ℤ) ^ (m + 2))).filter (fun t => (p : ℤ) ∣ t),
      x ∉ (Finset.Icc (-(2 * (p ^ m : ℕ) : ℤ)) (2 * (p ^ m : ℕ))).image (fun s => (p : ℤ) * s) →
      (chebU (k - 2) x (p ^ (m + 2) : ℕ) : ℚ) * (p * E (x / p)) = 0 := by
    intro x hx hnx
    obtain ⟨s, rfl⟩ := (Finset.mem_filter.1 hx).2
    have hs : s ∉ Finset.Icc (-(2 * (p ^ m : ℕ) : ℤ)) (2 * (p ^ m : ℕ)) := fun h =>
      hnx (Finset.mem_image.2 ⟨s, h, rfl⟩)
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hs
    push_cast at hs
    have h4 : 4 * ((p ^ m : ℕ) : ℤ) ≤ s ^ 2 := by
      push_cast
      rcases hs with h | h
      · have h' : 2 * (p : ℤ) ^ m < -s := by linarith
        nlinarith [mul_lt_mul'' h' h' (by positivity) (by positivity)]
      · nlinarith [mul_lt_mul'' h h (by positivity) (by positivity)]
    rw [Int.mul_ediv_cancel_left _ hp0, hE s h4, mul_zero, mul_zero]
  rw [← Finset.sum_subset hsub hvan, Finset.sum_image fun x _ y _ h => mul_left_cancel₀ hp0 h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Int.mul_ediv_cancel_left _ hp0]

lemma Icc_cast (p n : ℕ) : Finset.Icc (-(2 * (p ^ n : ℕ) : ℤ)) (2 * (p ^ n : ℕ)) =
    Finset.Icc (-(2 * (p : ℤ) ^ n)) (2 * (p : ℤ) ^ n) := by push_cast; rfl

/-- **Elliptic split** at `p^m`, `m ≥ 1`. -/
lemma ell_split {p : ℕ} (hp : p.Prime) (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    ellG1 M k (p ^ m) 1 - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * ellG1 M k (p ^ (m - 2)) (p : ZMod M) else 0) =
      -∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => ¬ (p : ℤ) ∣ t),
          (chebU (k - 2) t (p ^ m : ℕ) : ℚ) * ellCount M 1 t (p ^ m) -
        ∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => (p : ℤ) ∣ t),
          (chebU (k - 2) t (p ^ m : ℕ) : ℚ) * (ellCount M 1 t (p ^ m) -
            (if 2 ≤ m then p * ellCount M (p : ZMod M)⁻¹ (t / p) (p ^ (m - 2)) else 0)) := by
  obtain ⟨m', rfl⟩ | h1 : (∃ m', m = m' + 2) ∨ m = 1 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · right; omega
    · left; exact ⟨m - 2, by omega⟩
  · have h2 : 2 ≤ m' + 2 := by omega
    simp only [h2, ↓reduceIte, Nat.add_sub_cancel]
    rw [ellG1_eq_Icc, ellG1_eq_Icc, ZMod.inv_one,
      mul_neg, chain_reindex p hp k m' hk (fun s => ellCount M (p : ZMod M)⁻¹ s (p ^ m'))
        (fun s hs => EllTerm.ellCount_eq_zero _ hs), Icc_cast,
      ← Finset.sum_filter_add_sum_filter_not _ (fun t => (p : ℤ) ∣ t)]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · subst h1
    simp only [show ¬ (2 ≤ 1) by omega, ↓reduceIte, sub_zero]
    rw [ellG1_eq_Icc, ZMod.inv_one, Icc_cast,
      ← Finset.sum_filter_add_sum_filter_not _ (fun t => (p : ℤ) ∣ t)]
    ring

end RamanujanPetersson.S3.Match


