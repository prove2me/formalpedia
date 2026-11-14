-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingH
-- name    : RPLib_S2_WeilPairingH
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:00:06.322748+00:00
-- url     : https://prove2.me/theorems/2a485f49-d473-4ed8-9d68-bbdbc376e535
-- title:
--   Weil pairing, part H: descent of $E[n]$-invariant divisors
-- statement:
--   A nonzero function with $E[n]$-invariant divisor is $c \cdot g_T \cdot H$ with $T \in E[n]$ and $H$ invariant under all translations by $E[n]$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   L. C. Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., CRC Press 2008, doi:10.1201/9781420071474, Section 11.2

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingG

/-!
# WPH: descent of `E[n]`-invariant divisors (unit S2-WeilPairing, O8 part 1)

* `descent` : if `g ≠ 0` has an `E[n]`-invariant divisor, then `g = c · g_T · H` with `T ∈ E[n]`
  and `H` fixed by every `τ_R`, `R ∈ E[n]`. No `[n]^*` is needed: pick one representative per
  `E[n]`-orbit of the support, build `F` with divisor `∑ ord_A(g) (A) - (S') + (O)` on the
  representatives, and take `H = ∏_{R ∈ E[n]} τ_R F`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.Weil

section Descent

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma sum_En_ite_c {n : ℕ} (hn : (n : L) ≠ 0) (P A : Pt W L) (c : ℤ) :
    ∑ R ∈ En W L n hn, (if P + R = A then c else 0) = if n • P = n • A then c else 0 := by
  have h1 : ∀ R : Pt W L, (P + R = A) ↔ (R = A - P) :=
    fun R => ⟨fun h => by rw [← h]; abel, fun h => by rw [h]; abel⟩
  simp only [h1, Finset.sum_ite_eq', mem_En]
  by_cases h : n • P = n • A
  · rw [if_pos (by rw [nsmul_sub, h, sub_self]), if_pos h]
  · rw [if_neg (fun h' => h (by rw [nsmul_sub, sub_eq_zero] at h'; exact h'.symm)), if_neg h]

lemma tau_prod_En {n : ℕ} (hn : (n : L) ≠ 0) {S : Pt W L} (hS : n • S = 0) (u : FF W L) :
    tau W L S (∏ R ∈ En W L n hn, tau W L R u) = ∏ R ∈ En W L n hn, tau W L R u := by
  rw [map_prod]
  simp only [← tau_add_apply]
  exact Finset.prod_equiv (Equiv.addLeft S)
    (fun R => by simp only [mem_En, Equiv.coe_addLeft, nsmul_add, hS, zero_add]) (fun R _ => rfl)

lemma sum_reps_En {n : ℕ} (hn : (n : L) ≠ 0) (Reps : Finset (Pt W L))
    (huniq : ∀ A ∈ Reps, ∀ B ∈ Reps, n • A = n • B → A = B) {M : Type*} [AddCommMonoid M]
    (φ : Pt W L → M) :
    ∑ P ∈ (Reps ×ˢ En W L n hn).image (fun p => p.1 + p.2), φ P =
      ∑ A ∈ Reps, ∑ R ∈ En W L n hn, φ (A + R) := by
  rw [Finset.sum_image (fun p hp q hq h => by
    obtain ⟨A₁, R₁⟩ := p
    obtain ⟨A₂, R₂⟩ := q
    simp only [Finset.mem_coe, Finset.mem_product, mem_En] at hp hq
    have hA : A₁ = A₂ := huniq A₁ hp.1 A₂ hq.1 (by
      have h' := congrArg (fun x => n • x) h
      simp only [nsmul_add, hp.2, hq.2, add_zero] at h'
      exact h')
    subst hA
    simp only [Prod.mk.injEq, true_and]
    exact add_left_cancel h), Finset.sum_product]

/-- **Descent**: a function whose divisor is `E[n]`-invariant is `c · g_T · H` with `H` invariant. -/
theorem descent {n : ℕ} (hn : (n : L) ≠ 0) {g : FF W L} (hg : g ≠ 0)
    (hinv : ∀ R : Pt W L, n • R = 0 → ∀ P, ord W L g (P + R) = ord W L g P) :
    ∃ T : Pt W L, n • T = 0 ∧ ∃ c : L, c ≠ 0 ∧ ∃ H : FF W L, H ≠ 0 ∧
      (∀ R : Pt W L, n • R = 0 → tau W L R H = H) ∧
      g = algebraMap L (FF W L) c * (gT W L n T * H) := by
  classical
  have hn0 : n ≠ 0 := ne_zero_of_cast hn
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset (Pt W L), ∀ P, ord W L g P ≠ 0 → P ∈ Z :=
    ⟨(ord_finite hg).toFinset, fun P hP => (ord_finite hg).mem_toFinset.mpr hP⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Finset (Pt W L), Y = Z.image (fun P => n • P) := ⟨_, rfl⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : Pt W L → Pt W L, ∀ Q ∈ Y, rep Q ∈ Z ∧ n • rep Q = Q := by
    refine ⟨fun Q => if h : ∃ P ∈ Z, n • P = Q then h.choose else 0, fun Q hQ => ?_⟩
    have h : ∃ P ∈ Z, n • P = Q := by rw [hY] at hQ; exact Finset.mem_image.mp hQ
    simp only [dif_pos h]
    exact h.choose_spec
  obtain ⟨Reps, hRepsdef⟩ : ∃ Reps : Finset (Pt W L), Reps = Y.image rep := ⟨_, rfl⟩
  have hReps : ∀ A ∈ Reps, rep (n • A) = A := by
    intro A hA
    rw [hRepsdef] at hA
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hA
    rw [(hrep Q hQ).2]
  have huniq : ∀ A ∈ Reps, ∀ B ∈ Reps, n • A = n • B → A = B := by
    intro A hA B hB h
    rw [← hReps A hA, ← hReps B hB, h]
  have hcov : ∀ P, ord W L g P ≠ 0 → rep (n • P) ∈ Reps ∧ n • rep (n • P) = n • P := by
    intro P hP
    have hQ : n • P ∈ Y := by rw [hY]; exact Finset.mem_image_of_mem _ (hZ P hP)
    refine ⟨?_, (hrep _ hQ).2⟩
    rw [hRepsdef]
    exact Finset.mem_image_of_mem _ hQ
  have hkey : ∀ P, ∑ A ∈ Reps, (if n • P = n • A then ord W L g A else 0) = ord W L g P := by
    intro P
    by_cases hP : ∃ A ∈ Reps, n • A = n • P
    · obtain ⟨A, hA, hAP⟩ := hP
      rw [Finset.sum_eq_single_of_mem A hA (fun B hB hBA =>
        if_neg (fun h => hBA (huniq B hB A hA (h.symm.trans hAP.symm)))), if_pos hAP.symm]
      have hR : n • (P - A) = 0 := by rw [nsmul_sub, hAP, sub_self]
      have h := hinv (P - A) hR A
      rw [show A + (P - A) = P by abel] at h
      exact h.symm
    · rw [Finset.sum_eq_zero (fun A hA => if_neg (fun h => hP ⟨A, hA, h.symm⟩))]
      by_contra h
      exact hP ⟨_, (hcov P (Ne.symm h)).1, (hcov P (Ne.symm h)).2⟩
  have hZ' : ∀ P, ord W L g P ≠ 0 → P ∈ (Reps ×ˢ En W L n hn).image (fun p => p.1 + p.2) := by
    intro P hP
    obtain ⟨h1, h2⟩ := hcov P hP
    exact Finset.mem_image.mpr ⟨(rep (n • P), P - rep (n • P)),
      Finset.mem_product.mpr ⟨h1, mem_En.mpr (by rw [nsmul_sub, h2, sub_self])⟩, by simp⟩
  -- degree
  have hdeg0 : ∑ A ∈ Reps, ord W L g A = 0 := by
    have h := sum_ord_eq_zero hg _ hZ'
    rw [sum_reps_En hn Reps huniq] at h
    have h2 : ∀ A ∈ Reps, ∑ R ∈ En W L n hn, ord W L g (A + R) =
        ((n ^ 2 : ℕ) : ℤ) * ord W L g A := by
      intro A _
      have h3 : ∀ R ∈ En W L n hn, ord W L g (A + R) = ord W L g A :=
        fun R hR => hinv R (mem_En.mp hR) A
      rw [Finset.sum_congr rfl h3, Finset.sum_const, card_En, nsmul_eq_mul]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast pow_ne_zero 2 hn0)
  -- sum
  obtain ⟨S', hS'⟩ : ∃ S' : Pt W L, S' = ∑ A ∈ Reps, ord W L g A • A := ⟨_, rfl⟩
  have hsum0 : (n ^ 2) • S' = 0 := by
    have h := sum_ord_smul hg _ (fun P _ hP => hZ' P hP)
    rw [sum_reps_En hn Reps huniq] at h
    have h2 : ∀ A ∈ Reps, ∑ R ∈ En W L n hn, ord W L g (A + R) • (A + R) =
        ord W L g A • ((n ^ 2) • A) + ord W L g A • ∑ R ∈ En W L n hn, R := by
      intro A _
      have h3 : ∀ R ∈ En W L n hn, ord W L g (A + R) • (A + R) = ord W L g A • (A + R) :=
        fun R hR => by rw [hinv R (mem_En.mp hR) A]
      rw [Finset.sum_congr rfl h3, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const,
        card_En, smul_add]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.sum_smul, hdeg0, zero_smul,
      add_zero] at h
    rw [hS', Finset.smul_sum]
    exact (Finset.sum_congr rfl (fun A _ => smul_comm (n ^ 2) (ord W L g A) A)).trans h
  have hT : n • (n • S') = 0 := by rw [smul_smul, ← sq, hsum0]
  -- the function `F` on representatives
  have hsubR : Reps ⊆ insert S' (insert 0 Reps) :=
    fun A hA => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hA)
  obtain ⟨F, hF0, hF⟩ := exists_of_sum_eq_zero' (W := W) (L := L)
    (fun P => (if P ∈ Reps then ord W L g P else 0) - (if P = S' then 1 else 0) +
      (if P = 0 then 1 else 0))
    (insert S' (insert 0 Reps))
    (fun P hP => by
      by_contra hPZ
      simp only [Finset.mem_insert, not_or] at hPZ
      obtain ⟨e1, e2, e3⟩ := hPZ
      exact hP (by simp [e1, e2, e3]))
    (by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr hsubR, hdeg0]
      simp)
    (by
      simp only [add_smul, sub_smul, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr hsubR]
      simp [hS'])
  have hH0 : (∏ R ∈ En W L n hn, tau W L R F) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun R _ => tau_ne_zero R hF0)
  have hordH : ∀ P, ord W L (∏ R ∈ En W L n hn, tau W L R F) P =
      ord W L g P - dT W L n (n • S') P := by
    intro P
    rw [ord_prod _ _ (fun R _ => tau_ne_zero R hF0)]
    simp only [ord_tau, hF, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hfirst : ∑ R ∈ En W L n hn, (if P + R ∈ Reps then ord W L g (P + R) else 0) =
        ord W L g P := by
      rw [show (∑ R ∈ En W L n hn, (if P + R ∈ Reps then ord W L g (P + R) else 0)) =
          ∑ R ∈ En W L n hn, ∑ A ∈ Reps, (if P + R = A then ord W L g A else 0) from
        Finset.sum_congr rfl (fun R _ => (Finset.sum_ite_eq Reps (P + R) (ord W L g)).symm),
        Finset.sum_comm]
      simp only [sum_En_ite_c hn]
      exact hkey P
    rw [hfirst, sum_En_ite hn, sum_En_ite hn, smul_zero]
    simp only [dT]
    ring
  obtain ⟨c, hc, hgc⟩ := exists_const_of_ord_eq hg (mul_ne_zero (gT_ne_zero n (n • S')) hH0)
    (fun P _ => by rw [ord_mul (gT_ne_zero n (n • S')) hH0, ord_gT hn hT, hordH]; ring)
  exact ⟨n • S', hT, c, hc, _, hH0, fun R hR => tau_prod_En hn hR F, hgc⟩

end Descent

end RPLib.Weil


