-- Prove2me | Definitions.Def_RPLib_S3_MatchingG
-- name    : RPLib_S3_MatchingG
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:23:49.881174+00:00
-- url     : https://prove2.me/theorems/714e3e6c-fadf-4679-a2e8-f3e21f01af5a
-- title:
--   Weight-two Ramanujan-Petersson library: `Tr Φ^m` as a trace-formula difference, and its decomposition
-- statement:
--   `Tr Φ^m` as a trace-formula difference, and its decomposition.
--
--   * `TD M k p m = TF(p^m, 1) - [m ≥ 2] p^{k-1} TF(p^{m-2}, p)`; `trace_phiOp_pow`: `Tr Φ^m = TD` (`m ≥ 1`,
--     `tracePhiPow` + `EllW2.eichlerSelbergG1`).
--   * `TD_decomp`: `TD + Σ U(pairs) - [k = 2](1 + q) = (scalar diff) + (hyp diff) - Σ_{p ∤ t} U (ellCount - pairCount)
--     - Σ_{p ∣ t} U (ellCount - p-chain) + Σ_{p ∣ t} U pairCount`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_MatchingA
import Definitions.Def_RPLib_S3_MatchingB
import Definitions.Def_RPLib_S3_MatchingE
import Definitions.Def_RPLib_S3_EichlerSelbergWt2

/-!
# S3-Matching, part G: `Tr Φ^m` as a trace-formula difference, and its decomposition

* `TD M k p m = TF(p^m, 1) - [m ≥ 2] p^{k-1} TF(p^{m-2}, p)`; `trace_phiOp_pow`: `Tr Φ^m = TD` (`m ≥ 1`,
  `tracePhiPow` + `EllW2.eichlerSelbergG1`).
* `TD_decomp`: `TD + Σ U(pairs) - [k = 2](1 + q) = (scalar diff) + (hyp diff) - Σ_{p ∤ t} U (ellCount - pairCount)
  - Σ_{p ∣ t} U (ellCount - p-chain) + Σ_{p ∣ t} U pairCount`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

open RamanujanPetersson.Diamond RamanujanPetersson.Hecke

/-- `TF(p^m, 1) - [m ≥ 2] p^{k-1} TF(p^{m-2}, p)`. -/
def TD (M : ℕ) [NeZero M] (k p m : ℕ) : ℚ :=
  traceFormulaG1 M k (p ^ m) 1 -
    (if 2 ≤ m then (p : ℚ) ^ (k - 1) * traceFormulaG1 M k (p ^ (m - 2)) (p : ZMod M) else 0)

variable {M : ℕ} [NeZero M]

lemma trace_phiOp_pow (hM : 4 ≤ M) (k : ℕ) (hk : 2 ≤ k) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ)
    (hm : 1 ≤ m) : LinearMap.trace ℂ _ (phiOp p hpM (k : ℤ) ^ m) = ((TD M k p m : ℚ) : ℂ) := by
  have ES := EllW2.eichlerSelbergG1 M hM k hk p hpM
  have hc : (p : ℂ) ^ ((k : ℤ) - 1) = (((p : ℚ) ^ (k - 1) : ℚ) : ℂ) := by
    rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]; push_cast; rfl
  have hu : ((unitP hpM : (ZMod M)ˣ) : ZMod M) = (p : ZMod M) := ZMod.coe_unitOfCoprime _ _
  obtain ⟨m', rfl⟩ | h1 : (∃ m', m = m' + 2) ∨ m = 1 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · right; omega
    · left; exact ⟨m - 2, by omega⟩
  · obtain ⟨-, h2⟩ := tracePhiPow M p hpM (k : ℤ)
    have e1 := ES (m' + 2) 1
    have e2 := ES m' (unitP hpM)
    rw [map_one, mul_one, Units.val_one] at e1
    rw [hu] at e2
    rw [h2 m', LinearMap.trace_mul_comm ℂ (diamond _ _), e1, e2, hc, TD, if_pos (by omega),
      Nat.add_sub_cancel]
    push_cast; ring
  · subst h1
    obtain ⟨h1, -⟩ := tracePhiPow M p hpM (k : ℤ)
    have e1 := ES 1 1
    rw [map_one, mul_one, Units.val_one] at e1
    rw [pow_one, h1, show heckeT p (k : ℤ) = Tpow (M := M) p hpM (k : ℤ) 1 from rfl, e1, TD, if_neg (by omega),
      sub_zero]

lemma TD_eq (k p m : ℕ) : TD M k p m =
    (scalarG1 M k (p ^ m) 1 - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * scalarG1 M k (p ^ (m - 2)) (p : ZMod M) else 0)) +
    (ellG1 M k (p ^ m) 1 - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * ellG1 M k (p ^ (m - 2)) (p : ZMod M) else 0)) +
    (hypG1 M k (p ^ m) 1 - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * hypG1 M k (p ^ (m - 2)) (p : ZMod M) else 0)) +
    (eisG1 M k (p ^ m) - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * eisG1 M k (p ^ (m - 2)) else 0)) := by
  unfold TD traceFormulaG1
  split_ifs <;> ring

omit [NeZero M] in
lemma eisD_eq {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (k m : ℕ) (hm : 1 ≤ m) :
    eisG1 M k (p ^ m) - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * eisG1 M k (p ^ (m - 2)) else 0) =
      if k = 2 then 1 + (p : ℚ) ^ m else 0 := by
  obtain ⟨m', rfl⟩ | h1 : (∃ m', m = m' + 2) ∨ m = 1 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · right; omega
    · left; exact ⟨m - 2, by omega⟩
  · rw [if_pos (by omega), Nat.add_sub_cancel, eis_diff hp hpM]
  · subst h1
    rw [if_neg (by omega), sub_zero, eisG1_pow hp hpM]
    split_ifs
    · rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
    · rfl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [NeZero M] [Fintype F] in
lemma pairSumU_split (k p m : ℕ) :
    (((pairSumU F M k (p ^ m) : ℤ)) : ℚ) =
      ∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => (p : ℤ) ∣ t),
          (chebU (k - 2) t (p ^ m : ℕ) : ℚ) * pairCount F M t +
        ∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => ¬ (p : ℤ) ∣ t),
          (chebU (k - 2) t (p ^ m : ℕ) : ℚ) * pairCount F M t := by
  unfold pairSumU
  rw [Int.cast_sum, Icc_cast, ← Finset.sum_filter_add_sum_filter_not _ (fun t => (p : ℤ) ∣ t)]
  congr 1 <;> refine Finset.sum_congr rfl fun t _ => ?_ <;> push_cast <;> ring

/-- **The decomposition of (I').** -/
lemma TD_decomp {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    TD M k p m + (((pairSumU F M k (p ^ m) : ℤ)) : ℚ) - (if k = 2 then 1 + (p : ℚ) ^ m else 0) =
      (scalarG1 M k (p ^ m) 1 -
          (if 2 ≤ m then (p : ℚ) ^ (k - 1) * scalarG1 M k (p ^ (m - 2)) (p : ZMod M) else 0)) +
        (hypG1 M k (p ^ m) 1 -
          (if 2 ≤ m then (p : ℚ) ^ (k - 1) * hypG1 M k (p ^ (m - 2)) (p : ZMod M) else 0)) -
        ∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => ¬ (p : ℤ) ∣ t),
          (chebU (k - 2) t (p ^ m : ℕ) : ℚ) * (ellCount M 1 t (p ^ m) - pairCount F M t) -
        ∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => (p : ℤ) ∣ t),
          (chebU (k - 2) t (p ^ m : ℕ) : ℚ) * (ellCount M 1 t (p ^ m) -
            (if 2 ≤ m then p * ellCount M (p : ZMod M)⁻¹ (t / p) (p ^ (m - 2)) else 0)) +
        ∑ t ∈ (Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => (p : ℤ) ∣ t),
          (chebU (k - 2) t (p ^ m : ℕ) : ℚ) * pairCount F M t := by
  rw [TD_eq, eisD_eq hp hpM k m hm, ell_split hp k m hk hm, pairSumU_split]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end RamanujanPetersson.S3.Match


