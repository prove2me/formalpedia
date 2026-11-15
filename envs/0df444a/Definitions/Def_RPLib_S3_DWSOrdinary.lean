-- Prove2me | Definitions.Def_RPLib_S3_DWSOrdinary
-- name    : RPLib_S3_DWSOrdinary
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:21:04.791655+00:00
-- url     : https://prove2.me/theorems/e86e6968-77fc-4e0a-b3f0-ecf516b3ee23
-- title:
--   Weight-two Ramanujan-Petersson library: `DWSOrdinary`, conditional on Tate and Kronecker-Hurwitz
-- statement:
--   `DWSOrdinary`, conditional on Tate and Kronecker-Hurwitz.
--
--   `dwsOrdinary (hT : TateIsogenyPrimeToP.{0}) (hKH : KroneckerHurwitz) : DWSOrdinary`. Both hypotheses are frozen
--   `Prop`s stated in pure Mathlib terms (`TateStmtP.lean`, `Statements.lean`); no axiom, no `sorry`.
--   * (i) `pairCount_le_ellCount` (DWSO_CC).
--   * (ii) `Σ_{p ∤ t} (ellCount_M - pairCount) ≤ M² Σ_{p ∤ t} (ellCount_1 - #WT_t/#G)` (`deficit_le`, DWSO_DB)
--     `≤ M² ((q + C₁) - (q⁵ - K_p q⁴)/((q - 1) q³)) ≤ M² (C₁ + 2 K_p)` (`sum_ord_ell1_le`, DWSO_EC;
--     `sum_card_WT`, `card_ord_ge`, DWSO_FB; `card_variableChange`, DWSO_FA).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSODB
import Definitions.Def_RPLib_S3_DWSOEC
import Definitions.Def_RPLib_S3_DWSOFB

/-!
# S3-DWS-Ordinary: **`DWSOrdinary`**, conditional on Tate and Kronecker-Hurwitz

`dwsOrdinary (hT : TateIsogenyPrimeToP.{0}) (hKH : KroneckerHurwitz) : DWSOrdinary`. Both hypotheses are frozen
`Prop`s stated in pure Mathlib terms (`TateStmtP.lean`, `Statements.lean`); no axiom, no `sorry`.
* (i) `pairCount_le_ellCount` (DWSO_CC).
* (ii) `Σ_{p ∤ t} (ellCount_M - pairCount) ≤ M² Σ_{p ∤ t} (ellCount_1 - #WT_t/#G)` (`deficit_le`, DWSO_DB)
  `≤ M² ((q + C₁) - (q⁵ - K_p q⁴)/((q - 1) q³)) ≤ M² (C₁ + 2 K_p)` (`sum_ord_ell1_le`, DWSO_EC;
  `sum_card_WT`, `card_ord_ge`, DWSO_FB; `card_variableChange`, DWSO_FA).
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.DWSO

open RPLib RPLib.DWS RamanujanPetersson.S3.DWSS

/-- **DWSOrdinary**, conditional on `TateIsogenyPrimeToP` and `KroneckerHurwitz`. -/
theorem dwsOrdinary (hT : TateIsogenyPrimeToP.{0}) (hKH : KroneckerHurwitz) : DWSOrdinary := by
  intro M _ hM4 p _ hpM
  obtain ⟨C₁, -, hC₁⟩ := sum_ord_ell1_le (p := p) hKH
  refine ⟨(M : ℚ) ^ 2 * (C₁ + 2 * Kp p), fun m F _ _ _ hq =>
    ⟨fun t hpt => pairCount_le_ellCount hT F hq hM4 hpM hpt, ?_⟩⟩
  have : CharP F p := charP_of_card_eq_prime_pow hq
  have hstep := Finset.sum_le_sum (s := (Finset.Icc (-(2 * p ^ m : ℤ)) (2 * p ^ m)).filter
      (fun t => ¬ (p : ℤ) ∣ t)) (fun t ht => deficit_le hT F hq hM4 hpM (Finset.mem_filter.mp ht).2)
  refine hstep.trans ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div,
    sum_card_WT (F := F) p (2 * p ^ m : ℤ) (by rw [hq]; push_cast; rfl)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hq1 : 2 ≤ p ^ m := by
    have h := Fintype.one_lt_card (α := F); rw [hq] at h; omega
  have hq2 : (2 : ℚ) ≤ (p : ℚ) ^ m := by exact_mod_cast hq1
  have hE := hC₁ m
  have hN := card_ord_ge p hq
  rw [hq] at hN
  rw [card_variableChange, hq]
  set N := (Finset.univ.filter (fun W : WeierstrassCurve F => W.Δ ≠ 0 ∧ ¬ (p : ℤ) ∣ EllFq.trace W)).card
  have hN' : ((p : ℚ) ^ m) ^ 5 - Kp p * ((p : ℚ) ^ m) ^ 4 ≤ N := by exact_mod_cast hN
  have hG : (0 : ℚ) < (((p ^ m - 1) * (p ^ m) ^ 3 : ℕ) : ℚ) := by
    have : 0 < (p ^ m - 1) * (p ^ m) ^ 3 := Nat.mul_pos (by omega) (pow_pos (by omega) 3)
    exact_mod_cast this
  have hGc : (((p ^ m - 1) * (p ^ m) ^ 3 : ℕ) : ℚ) = ((p : ℚ) ^ m - 1) * ((p : ℚ) ^ m) ^ 3 := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p ^ m)]; push_cast; ring
  have hK : (0 : ℚ) ≤ Kp p := Nat.cast_nonneg _
  have h0 : 0 ≤ ((p : ℚ) ^ m) ^ 3 * ((Kp p : ℚ) * ((p : ℚ) ^ m - 2) + (p : ℚ) ^ m) :=
    mul_nonneg (by positivity) (add_nonneg (mul_nonneg hK (by linarith)) (by positivity))
  have hdiv : ((p : ℚ) ^ m - 2 * Kp p) ≤ (N : ℚ) / (((p ^ m - 1) * (p ^ m) ^ 3 : ℕ) : ℚ) := by
    rw [le_div_iff₀ hG, hGc]
    nlinarith [hN', h0]
  linarith

end RamanujanPetersson.S3.DWSO


