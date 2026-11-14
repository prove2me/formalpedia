-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingE
-- name    : RPLib_S2_WeilPairingE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:56:03.497199+00:00
-- url     : https://prove2.me/theorems/1d1ed08d-0114-43b7-a447-2b6c89d7ed40
-- title:
--   Weil pairing, part E: degree zero and Abel-Jacobi
-- statement:
--   Principal divisors have degree $0$, and a degree-$0$ divisor whose sum in $E$ is $O$ is principal.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Corollary III.3.5

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingD
import Definitions.Def_RPLib_S2_Torsion

/-!
# WPE: degree zero and Abel-Jacobi existence (unit S2-WeilPairing, O3 part 2)

* `deg_smul_eq_zero`, `sum_ord_eq_zero` : `deg (div f) = 0` (translate the sum identity, then use a point of
  prime order `ℓ > |deg|`, `ℓ ≠ char`).
* `exists_of_sum_eq_zero` : a degree-0 divisor with sum `O` is principal.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.Weil

section Degree

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma deg_smul_eq_zero {f : FF W L} (hf : f ≠ 0) (Z : Finset (Pt W L))
    (hZ : ∀ P, ord W L f P ≠ 0 → P ∈ Z) (S : Pt W L) : (∑ P ∈ Z, ord W L f P) • S = 0 := by
  have h1 := sum_ord_smul hf Z (fun P _ hP => hZ P hP)
  have h2 := sum_ord_smul (tau_ne_zero S hf) (Z.image (· - S)) (fun P _ hP => by
    rw [ord_tau] at hP
    exact Finset.mem_image.mpr ⟨P + S, hZ _ hP, by abel⟩)
  rw [Finset.sum_image (fun a _ b _ h => sub_left_injective h)] at h2
  simp only [ord_tau, sub_add_cancel] at h2
  rw [show (∑ x ∈ Z, ord W L f x • (x - S)) =
      (∑ x ∈ Z, ord W L f x • x) - (∑ x ∈ Z, ord W L f x) • S by
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib]; simp only [smul_sub]] at h2
  rw [h1, zero_sub, neg_eq_zero] at h2
  exact h2

/-- **Degree zero**: `∑_P ord_P(f) = 0` (over any finite set containing the support). -/
theorem sum_ord_eq_zero {f : FF W L} (hf : f ≠ 0) (Z : Finset (Pt W L))
    (hZ : ∀ P, ord W L f P ≠ 0 → P ∈ Z) : ∑ P ∈ Z, ord W L f P = 0 := by
  obtain ⟨ℓ, hℓ, hℓp⟩ := Nat.exists_infinite_primes ((∑ P ∈ Z, ord W L f P).natAbs + ringChar L + 1)
  have hℓL : (ℓ : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L (ringChar L)] at h
    rcases hℓp.eq_one_or_self_of_dvd _ h with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hcard := RPLib.Torsion.card_tors (W := W.baseChange L) ℓ hℓL
  obtain ⟨S, hS, hS0⟩ := (AddSubgroup.bot_or_exists_ne_zero
    (RPLib.Torsion.tors (W.baseChange L) ℓ)).resolve_left (by
      intro hb
      rw [hb, AddSubgroup.card_bot] at hcard
      nlinarith [hℓp.two_le])
  have hord : addOrderOf S = ℓ := addOrderOf_eq_prime (RPLib.Torsion.mem_tors.mp hS) hS0
  have hdvd : ((addOrderOf S : ℕ) : ℤ) ∣ ∑ P ∈ Z, ord W L f P :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr (deg_smul_eq_zero hf Z hZ S)
  rw [hord] at hdvd
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using (by omega :
    (∑ P ∈ Z, ord W L f P).natAbs < ℓ))

/-- The divisor has degree `0`. -/
theorem deg_divf {f : FF W L} (hf : f ≠ 0) : ∑ P ∈ (divf f).support, divf f P = 0 := by
  rw [Finset.sum_congr rfl (fun P _ => divf_apply hf P)]
  exact sum_ord_eq_zero hf _ (fun P hP => mem_support_divf hf hP)

/-- The divisor sums to `O`. -/
theorem sum_divf {f : FF W L} (hf : f ≠ 0) : ∑ P ∈ (divf f).support, divf f P • P = 0 := by
  rw [Finset.sum_congr rfl (fun P _ => by rw [divf_apply hf P])]
  exact sum_ord_smul hf _ (fun P _ hP => mem_support_divf hf hP)

/-- **Abel-Jacobi (existence)**: a divisor of degree `0` summing to `O` is the divisor of a function. -/
theorem exists_of_sum_eq_zero (D : Pt W L →₀ ℤ) (hdeg : ∑ P ∈ D.support, D P = 0)
    (hsum : ∑ P ∈ D.support, D P • P = 0) :
    ∃ g : FF W L, g ≠ 0 ∧ ∀ P, ord W L g P = D P := by
  have hmk : ClassGroup.mk (FF W L) (∏ Q ∈ D.support, unitP Q ^ D Q) = 1 := by
    have h := toClass_sum (W := W) (L := L) D.support D
    rw [hsum, map_zero] at h
    exact Additive.ofMul.injective (by rw [← h]; rfl)
  rw [ClassGroup.mk_eq_one_iff] at hmk
  obtain ⟨g, hg⟩ := (FractionalIdeal.isPrincipal_iff _).mp hmk
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hg
    exact Units.ne_zero _ hg
  have haff : ∀ P, P ≠ 0 → ord W L g P = D P := by
    intro P hP
    rw [← count_hosP hP hg0, ← hg,
      count_hosP_prod hP D.support D (fun Q _ hQ => Finsupp.mem_support_iff.mpr hQ)]
  refine ⟨g, hg0, fun P => ?_⟩
  by_cases hP : P = 0
  · subst hP
    have h1 := sum_ord_eq_zero hg0 (insert 0 D.support) (fun Q hQ => by
      by_cases hQ0 : Q = 0
      · rw [hQ0]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr (by rw [← haff Q hQ0]; exact hQ)))
    have h2 : ∑ Q ∈ insert 0 D.support, D Q = 0 := by
      by_cases h0 : (0 : Pt W L) ∈ D.support
      · rw [Finset.insert_eq_of_mem h0]; exact hdeg
      · rw [Finset.sum_insert h0, show D 0 = 0 by simpa using h0, zero_add]; exact hdeg
    have h3 : ∑ Q ∈ insert 0 D.support, (ord W L g Q - D Q) = ord W L g 0 - D 0 :=
      Finset.sum_eq_single_of_mem 0 (Finset.mem_insert_self _ _)
        (fun Q _ hQ => by rw [haff Q hQ, sub_self])
    rw [Finset.sum_sub_distrib, h1, h2, sub_zero] at h3
    linarith
  · exact haff P hP

/-- Two functions with the same orders everywhere differ by a nonzero constant. -/
theorem exists_const_of_ord_eq {f g : FF W L} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ P : Pt W L, P ≠ 0 → ord W L f P = ord W L g P) :
    ∃ c : L, c ≠ 0 ∧ f = algebraMap L (FF W L) c * g := by
  obtain ⟨c, hc, hfg⟩ := exists_const_of_ord (div_ne_zero hf hg)
    (fun P hP => by rw [ord_div hf hg, h P hP, sub_self])
  exact ⟨c, hc, by rw [← hfg, div_mul_cancel₀ _ hg]⟩

end Degree

end RPLib.Weil


