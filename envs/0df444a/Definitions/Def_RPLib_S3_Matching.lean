-- Prove2me | Definitions.Def_RPLib_S3_Matching
-- name    : RPLib_S3_Matching
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:26:10.741727+00:00
-- url     : https://prove2.me/theorems/2e462a0d-5f16-4e3d-812e-3c6672c71e88
-- title:
--   Weight-two Ramanujan-Petersson library: identity (I') (conditional on Tate and Kronecker-Hurwitz)
-- statement:
--   Identity (I') (conditional on Tate and Kronecker-Hurwitz).
--
--   **`identityI'`**, **`identityI'_j`** from `TD_decomp`: scalar (`abs_scalarG1_le`), hyperbolic (`abs_hyp_diff_le`),
--   and three `U`-sums bounded by `DWSOrdinary`, `PChainSum`, `DWSSuper` (helpers in `Matching_H`).
--   `tracePhiPow`, `rootOfPhi`: `Matching_A`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_MatchingA
import Definitions.Def_RPLib_S3_MatchingG
import Definitions.Def_RPLib_S3_MatchingH
import Definitions.Def_RPLib_S3_DWSOrdinary
import Definitions.Def_RPLib_S3_DWSSupersingular
import Definitions.Def_RPLib_S3_PCG

/-!
# S3-Matching: identity (I') (conditional on Tate and Kronecker-Hurwitz)

**`identityI'`**, **`identityI'_j`** from `TD_decomp`: scalar (`abs_scalarG1_le`), hyperbolic (`abs_hyp_diff_le`),
and three `U`-sums bounded by `DWSOrdinary`, `PChainSum`, `DWSSuper` (helpers in `Matching_H`).
`tracePhiPow`, `rootOfPhi`: `Matching_A`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.Match

theorem identityI' (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) (hKH : KroneckerHurwitz) : IdentityI' := by
  intro M _ hM k hk p _ hpM
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨C1, hC1⟩ := DWSO.dwsOrdinary hT hKH M hM p hpM
  obtain ⟨C2, hC2⟩ := pChainSum M hM p hpM
  obtain ⟨C3, hC3⟩ := dwsSupersingular.1 M hM p hpM
  refine ⟨((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) * (1 + p) + (hypB M : ℝ) +
    (((k - 2 : ℕ) : ℝ) + 1) * ((C1 : ℝ) + (C2 : ℝ) + (C3 : ℝ)), fun m hm F _ _ _ hq => ?_⟩
  have hS1 : 1 ≤ Real.sqrt p ^ ((k - 2) * m) :=
    one_le_pow₀ (Real.one_le_sqrt.2 (by exact_mod_cast hp.one_lt.le))
  have hB0 : (0 : ℝ) ≤ (hypB M : ℝ) := by unfold hypB; positivity
  rw [trace_phiOp_pow hM k hk p hpM m hm]
  have hcast : ((TD M k p m : ℚ) : ℂ) + ((pairSumU F M k (p ^ m) : ℤ) : ℂ) -
      (if k = 2 then 1 + (p : ℂ) ^ m else 0) =
      (((TD M k p m + ((pairSumU F M k (p ^ m) : ℤ) : ℚ) - (if k = 2 then 1 + (p : ℚ) ^ m else 0) : ℚ) : ℝ) : ℂ) := by
    split_ifs <;> push_cast <;> ring
  have hq4 : ∀ t : ℤ, 4 * ((p ^ m : ℕ) : ℤ) < t ^ 2 → 4 * (Fintype.card F : ℤ) < t ^ 2 := fun t h => by
    rw [hq]; exact h
  have hR := abs5q (abs_scalD_le (M := M) (p := p) k m hk hm)
    (show |((hypG1 M k (p ^ m) 1 - (if 2 ≤ m then (p : ℚ) ^ (k - 1) * hypG1 M k (p ^ (m - 2)) (p : ZMod M)
      else 0) : ℚ) : ℝ)| ≤ (hypB M : ℝ) * Real.sqrt p ^ ((k - 2) * m) by
        rw [← Rat.cast_abs]
        exact (by exact_mod_cast abs_hypD_le (by omega) hp hpM k m hm : _ ≤ (hypB M : ℝ)).trans
          (le_mul_of_one_le_right hB0 hS1))
    (piece_sum p m (k - 2) ((Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => ¬ (p : ℤ) ∣ t))
      (fun t => ellCount M 1 t (p ^ m) - pairCount F M t) (fun t _ h => by
        rw [EllTerm.ellCount_eq_zero _ h.le, pairCount_eq_zero M (hq4 t h), Nat.cast_zero, sub_zero])
      (X := (C1 : ℝ)) (by
        rw [Finset.sum_congr rfl fun t ht => abs_of_nonneg (by
          have := (hC1 m F hq).1 t (Finset.mem_filter.1 ht).2
          exact_mod_cast sub_nonneg.2 this)]
        exact_mod_cast (hC1 m F hq).2))
    (piece_sum p m (k - 2) ((Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => (p : ℤ) ∣ t))
      (fun t => ellCount M 1 t (p ^ m) -
        (if 2 ≤ m then p * ellCount M (p : ZMod M)⁻¹ (t / p) (p ^ (m - 2)) else 0)) (fun t ht h => by
        obtain ⟨s, rfl⟩ := (Finset.mem_filter.1 ht).2
        rw [EllTerm.ellCount_eq_zero _ h.le]
        split_ifs with h2
        · rw [Int.mul_ediv_cancel_left _ hp0, EllTerm.ellCount_eq_zero _ ?_, mul_zero, sub_zero]
          have hpm : ((p ^ m : ℕ) : ℤ) = (p : ℤ) ^ 2 * ((p ^ (m - 2) : ℕ) : ℤ) := by
            push_cast; rw [← pow_add]; congr 1; omega
          rw [hpm] at h
          have h' : (p : ℤ) ^ 2 * (4 * ((p ^ (m - 2) : ℕ) : ℤ)) < (p : ℤ) ^ 2 * s ^ 2 := by nlinarith
          exact (lt_of_mul_lt_mul_left h' (by positivity)).le
        · rw [sub_zero])
      (X := (C2 : ℝ)) (by
        simp only [← Rat.cast_abs]
        exact_mod_cast hC2 m))
    (piece_sum p m (k - 2) ((Finset.Icc (-(2 * (p : ℤ) ^ m)) (2 * (p : ℤ) ^ m)).filter (fun t => (p : ℤ) ∣ t))
      (fun t => (pairCount F M t : ℚ)) (fun t _ h => by rw [pairCount_eq_zero M (hq4 t h), Nat.cast_zero])
      (X := (C3 : ℝ)) (by
        simp only [Rat.cast_natCast, Nat.abs_cast]
        exact_mod_cast hC3 m F hq))
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, TD_decomp hp hpM k m hk hm]
  have hCS : 0 ≤ (((k : ℝ) - 1) / 12 * (dedekindPsi M : ℝ) * (M + 1) * (1 + p) + (hypB M : ℝ) +
      (((k - 2 : ℕ) : ℝ) + 1) * ((C1 : ℝ) + (C2 : ℝ) + (C3 : ℝ))) * Real.sqrt p ^ ((k - 2) * m) :=
    (abs_nonneg _).trans (hR.trans_eq (by ring))
  refine (hR.trans_eq (by ring)).trans (le_mul_of_one_le_right hCS ?_)
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem identityI'_j (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) (hKH : KroneckerHurwitz) : IdentityI'_j := by
  intro M _ hM k hk p _ hpM
  obtain ⟨C, hC⟩ := identityI' hT hKH M hM k hk p hpM
  refine ⟨C + (((k - 2 : ℕ) : ℝ) + 1) * (2 * M ^ 2), fun m hm F _ _ _ hq => ?_⟩
  have h1 := hC m hm F hq
  have h2 := abs_pairSumU_sub_j_le (F := F) M hM p hpM m k hq
  have hS1 : 1 ≤ Real.sqrt p ^ ((k - 2) * m) :=
    one_le_pow₀ (Real.one_le_sqrt.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))
  have heq : LinearMap.trace ℂ _ (phiOp p hpM (k : ℤ) ^ m) + ((pairSumU_j F M k (p ^ m) : ℤ) : ℂ) -
      (if k = 2 then 1 + (p : ℂ) ^ m else 0) =
      (LinearMap.trace ℂ _ (phiOp p hpM (k : ℤ) ^ m) + ((pairSumU F M k (p ^ m) : ℤ) : ℂ) -
        (if k = 2 then 1 + (p : ℂ) ^ m else 0)) -
      ((((pairSumU F M k (p ^ m) - pairSumU_j F M k (p ^ m) : ℤ) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h3 : (((k - 2 : ℕ) : ℝ) + 1) * Real.sqrt p ^ ((k - 2) * m) * (2 * M ^ 2) ≤
      (((k - 2 : ℕ) : ℝ) + 1) * Real.sqrt p ^ ((k - 2) * m) * (2 * M ^ 2) * (1 + m) :=
    le_mul_of_one_le_right (by positivity) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have hexp : (C + (((k - 2 : ℕ) : ℝ) + 1) * (2 * M ^ 2)) * Real.sqrt p ^ ((k - 2) * m) * (1 + m) =
      C * Real.sqrt p ^ ((k - 2) * m) * (1 + m) +
        (((k - 2 : ℕ) : ℝ) + 1) * Real.sqrt p ^ ((k - 2) * m) * (2 * M ^ 2) * (1 + m) := by ring
  rw [hexp]
  linarith

end RamanujanPetersson.S3.Match


