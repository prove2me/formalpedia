-- Prove2me | Definitions.Def_RPLib_S3_KHE
-- name    : RPLib_S3_KHE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:36:50.27533+00:00
-- url     : https://prove2.me/theorems/90ba7057-23b7-4ca7-8f6d-6933477322ac
-- title:
--   Kronecker-Hurwitz class number relation: Hurwitz class numbers as weighted counts on the closed half domain
-- statement:
--   Hurwitz class numbers as weighted counts on the closed half domain.
--
--   **`hH`** : for `D > 0`, `hurwitzH D = 2 ∑ᶠ_{[A,B,C], B² - 4AC = -D, A > 0} wt A B C`.
--   Proof: the mirror `B ↦ -B` (`muE`) and the pointwise identity
--   `rdF Q + rdF (μ Q) = 2 (Wd Q + Wd (μ Q))` (`2/#Stab` on reduced forms versus the half-domain weight).
--
--   **Formalization note.** Library module of an elementary formalization of the Kronecker-Hurwitz class number relation $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$ (Popa-Zagier's tessellation proof, recast as a telescoping identity over integer matrices of determinant $n$), part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016); L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KHA
import Definitions.Def_RPLib_S3_KHB
import Definitions.Def_RPLib_S3_ConjClassesA

/-!
# S3-KH, part E: Hurwitz class numbers as weighted counts on the closed half domain

**`hH`** : for `D > 0`, `hurwitzH D = 2 ∑ᶠ_{[A,B,C], B² - 4AC = -D, A > 0} wt A B C`.
Proof: the mirror `B ↦ -B` (`muE`) and the pointwise identity
`rdF Q + rdF (μ Q) = 2 (Wd Q + Wd (μ Q))` (`2/#Stab` on reduced forms versus the half-domain weight).
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.KH

open RamanujanPetersson.S3 RamanujanPetersson.S3.Conj RamanujanPetersson.Hurwitz

lemma mem_rF {D : ℤ} {Q : ℤ × ℤ × ℤ} : Q ∈ redForms D ↔
    Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = D ∧ -Q.1 < Q.2.1 ∧ Q.2.1 ≤ Q.1 ∧ Q.1 ≤ Q.2.2 ∧
      (Q.1 = Q.2.2 → 0 ≤ Q.2.1) := by
  rw [mem_redForms]; simp only [toBQF, BQF.disc, BQF.IsReduced]

/-- Half-domain weight of the forms of discriminant `D`. -/
def Wd (D : ℤ) (Q : ℤ × ℤ × ℤ) : ℚ :=
  if Q.2.1 ^ 2 - 4 * Q.1 * Q.2.2 = D ∧ 0 < Q.1 then wt Q.1 Q.2.1 Q.2.2 else 0

/-- `2/#Stab` on the reduced forms of discriminant `D`. -/
def rdF (D : ℤ) (Q : ℤ × ℤ × ℤ) : ℚ := if Q ∈ redForms D then 2 / (stabOrd Q : ℚ) else 0

/-- The mirror `[A, B, C] ↦ [A, -B, C]`. -/
def muE : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) where
  toFun Q := (Q.1, -Q.2.1, Q.2.2)
  invFun Q := (Q.1, -Q.2.1, Q.2.2)
  left_inv Q := by simp
  right_inv Q := by simp

lemma two_div_stab (A B C : ℤ) : (2 : ℚ) / (stabOrd (A, B, C) : ℚ) =
    if A = B ∧ B = C then 1 / 3 else if B = 0 ∧ A = C then 1 / 2 else 1 := by
  unfold stabOrd; split_ifs <;> norm_num

lemma pt_mirror (D : ℤ) (Q : ℤ × ℤ × ℤ) :
    rdF D Q + rdF D (muE Q) = 2 * (Wd D Q + Wd D (muE Q)) := by
  classical
  obtain ⟨A, B, C⟩ := Q
  simp only [rdF, Wd, muE, Equiv.coe_fn_mk, mem_rF, two_div_stab, wt, neg_sq]
  by_cases hD : B ^ 2 - 4 * A * C = D
  · simp only [hD, eq_self_iff_true, true_and]
    rcases lt_trichotomy B 0 with h1 | h1 | h1 <;> rcases lt_trichotomy B A with h2 | h2 | h2 <;>
    rcases lt_trichotomy (-B) A with h3 | h3 | h3 <;> rcases lt_trichotomy A C with h4 | h4 | h4 <;>
    rcases lt_or_ge 0 A with h5 | h5 <;>
    first
    | omega
    | (simp (disch := omega) only [if_pos, if_neg, hs_pos, hs_zero, hs_neg, cor_one, cor_l, cor_r] <;>
        norm_num)
  · simp [hD]

/-- **Hurwitz class number as a half-domain count.** -/
theorem hH {D : ℕ} (hD : 0 < D) : hurwitzH D = 2 * ∑ᶠ Q, Wd (-(D : ℤ)) Q := by
  classical
  have fr : (Function.support (rdF (-(D : ℤ)))).Finite :=
    (redForms (-(D : ℤ))).finite_toSet.subset fun Q hQ => by
      by_contra h; exact hQ (if_neg h)
  have fW : (Function.support (Wd (-(D : ℤ)))).Finite := by
    refine (Finset.Icc (-(D : ℤ)) D ×ˢ Finset.Icc (-(D : ℤ)) D ×ˢ Finset.Icc (-(D : ℤ)) D).finite_toSet.subset
      fun Q hQ => ?_
    obtain ⟨A, B, C⟩ := Q
    rw [Function.mem_support] at hQ
    simp only [Wd] at hQ
    split_ifs at hQ with h
    · obtain ⟨h1, h2, h3⟩ := wt_ne h.2 hQ
      obtain ⟨hd, hA⟩ := h
      simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
      have h6 : 3 * (A * C) ≤ D := by
        nlinarith [mul_le_mul_of_nonneg_left h3 hA.le, mul_le_mul h2 h2 h1 hA.le]
      have h7 : A ≤ A * C := by nlinarith
      have h8 : C ≤ A * C := by nlinarith
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
    · exact absurd rfl hQ
  have h1 : hurwitzH D = ∑ᶠ Q, rdF (-(D : ℤ)) Q := by
    rw [hurwitzH, if_neg hD.ne', finsum_eq_sum_of_support_subset _ (s := redForms (-(D : ℤ))) ?_]
    · exact Finset.sum_congr rfl fun Q hQ => (if_pos hQ).symm
    · intro Q hQ; rw [Function.mem_support] at hQ; by_contra h; exact hQ (if_neg h)
  have key := finsum_congr (pt_mirror (-(D : ℤ)))
  rw [finsum_add_distrib fr (fr.preimage muE.injective.injOn), finsum_comp_equiv muE (f := rdF (-(D : ℤ))),
    ← mul_finsum, finsum_add_distrib fW (fW.preimage muE.injective.injOn),
    finsum_comp_equiv muE (f := Wd (-(D : ℤ)))] at key
  rw [h1]; linarith

end RamanujanPetersson.S3.KH


