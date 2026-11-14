-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingG
-- name    : RPLib_S2_WeilPairingG
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:58:10.520914+00:00
-- url     : https://prove2.me/theorems/60b5493c-37b2-4d97-9a7d-76bb1c78473b
-- title:
--   Weil pairing, part G: bilinearity and alternation
-- statement:
--   The Weil pairing is bimultiplicative, $e_n(T,T) = 1$ and $e_n(S,T)e_n(T,S) = 1$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Proposition III.8.1

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingF

/-!
# WPG: the Weil pairing is bilinear and alternating (unit S2-WeilPairing, O7)

* `ePair_add_right` : `e(S, T₁ + T₂) = e(S, T₁) e(S, T₂)`, via `h = ∏_{R ∈ E[n]} τ_R u`,
  `div u = (T₁' + T₂') - (T₁') - (T₂') + (O)`.
* `ePair_self` : `e(T, T) = 1`, via `G = ∏_{i < n} τ_{i T'} g_T`, which has no zeros or poles.
* `ePair_swap` : `e(S, T) e(T, S) = 1`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.Weil

section Bilinear

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma ord_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → FF W L)
    (hf : ∀ i ∈ s, f i ≠ 0) (P : Pt W L) :
    ord W L (∏ i ∈ s, f i) P = ∑ i ∈ s, ord W L (f i) P := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, ord_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma sum_En_ite {n : ℕ} (hn : (n : L) ≠ 0) (P A : Pt W L) :
    ∑ R ∈ En W L n hn, (if P + R = A then (1 : ℤ) else 0) = if n • P = n • A then 1 else 0 := by
  have h1 : ∀ R : Pt W L, (P + R = A) ↔ (R = A - P) :=
    fun R => ⟨fun h => by rw [← h]; abel, fun h => by rw [h]; abel⟩
  simp only [h1, Finset.sum_ite_eq', mem_En]
  by_cases h : n • P = n • A
  · rw [if_pos (by rw [nsmul_sub, h, sub_self]), if_pos h]
  · rw [if_neg (fun h' => h (by rw [nsmul_sub, sub_eq_zero] at h'; exact h'.symm)), if_neg h]

/-- **Bilinearity in the second variable.** -/
theorem ePair_add_right {n : ℕ} (hn : (n : L) ≠ 0) {S T₁ T₂ : Pt W L} (hS : n • S = 0)
    (hT₁ : n • T₁ = 0) (hT₂ : n • T₂ = 0) :
    ePair W L n S (T₁ + T₂) = ePair W L n S T₁ * ePair W L n S T₂ := by
  obtain ⟨T₁', h₁⟩ := exists_nsmul_eq hn hT₁
  obtain ⟨T₂', h₂⟩ := exists_nsmul_eq hn hT₂
  have hT : n • (T₁ + T₂) = 0 := by rw [nsmul_add, hT₁, hT₂, add_zero]
  obtain ⟨u, hu0, hu⟩ := exists_of_sum_eq_zero' (W := W) (L := L)
    (fun P => (if P = T₁' + T₂' then 1 else 0) - (if P = T₁' then 1 else 0) -
      (if P = T₂' then 1 else 0) + (if P = 0 then 1 else 0))
    {T₁' + T₂', T₁', T₂', 0}
    (fun P hP => by
      by_contra hPZ
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hPZ
      obtain ⟨e1, e2, e3, e4⟩ := hPZ
      exact hP (by simp [e1, e2, e3, e4]))
    (by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib])
    (by
      simp only [add_smul, sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_insert, Finset.mem_singleton,
        true_or, or_true, if_true]
      abel)
  set h := ∏ R ∈ En W L n hn, tau W L R u with hh
  have hh0 : h ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun R _ => tau_ne_zero R hu0)
  have hordh : ∀ P, ord W L h P = (if n • P = T₁ + T₂ then 1 else 0) -
      (if n • P = T₁ then 1 else 0) - (if n • P = T₂ then 1 else 0) +
      (if n • P = 0 then 1 else 0) := by
    intro P
    rw [hh, ord_prod _ _ (fun R _ => tau_ne_zero R hu0)]
    simp only [ord_tau, hu, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_En_ite hn]
    rw [nsmul_add, h₁, h₂, smul_zero]
  have htauh : tau W L S h = h := by
    rw [hh, map_prod]
    simp only [← tau_add_apply]
    exact Finset.prod_equiv (Equiv.addLeft S)
      (fun R => by simp only [mem_En, Equiv.coe_addLeft, nsmul_add, hS, zero_add]) (fun R _ => rfl)
  have hg1 := gT_ne_zero (W := W) (L := L) n T₁
  have hg2 := gT_ne_zero (W := W) (L := L) n T₂
  obtain ⟨c, hc, hgc⟩ := exists_const_of_ord_eq (gT_ne_zero n (T₁ + T₂))
    (mul_ne_zero (mul_ne_zero hg1 hg2) hh0) (fun P _ => by
      rw [ord_mul (mul_ne_zero hg1 hg2) hh0, ord_mul hg1 hg2, ord_gT hn hT, ord_gT hn hT₁,
        ord_gT hn hT₂, hordh]
      simp only [dT]
      ring)
  have key := tau_gT hn hS hT
  rw [hgc] at key
  simp only [map_mul, AlgEquiv.commutes] at key
  rw [tau_gT hn hS hT₁, tau_gT hn hS hT₂, htauh] at key
  apply alg_cancel (g := algebraMap L (FF W L) c * (gT W L n T₁ * gT W L n T₂ * h))
    (mul_ne_zero ((_root_.map_ne_zero _).mpr hc) (mul_ne_zero (mul_ne_zero hg1 hg2) hh0))
  rw [map_mul]
  linear_combination -key

lemma sum_cyc {n : ℕ} (hn0 : n ≠ 0) {T : Pt W L} (hT : n • T = 0) (Q : Pt W L) :
    ∑ i ∈ Finset.range n, (if Q + i • T = T then (1 : ℤ) else 0) =
      ∑ i ∈ Finset.range n, (if Q + i • T = 0 then (1 : ℤ) else 0) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have hm : m • T = -T := by
    rw [succ_nsmul] at hT
    exact eq_neg_of_add_eq_zero_left hT
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : (Q + (i + 1) • T = T) ↔ (Q + i • T = 0) :=
      ⟨fun h => by
        rw [succ_nsmul, ← add_assoc] at h
        exact add_right_cancel (h.trans (zero_add T).symm),
       fun h => by rw [succ_nsmul, ← add_assoc, h, zero_add]⟩
    simp only [e]
  · have e : (Q + 0 • T = T) ↔ (Q + m • T = 0) :=
      ⟨fun h => by
        rw [zero_nsmul, add_zero] at h
        rw [hm, h, add_neg_cancel],
       fun h => by
        rw [zero_nsmul, add_zero]
        rw [hm, ← sub_eq_add_neg] at h
        exact sub_eq_zero.mp h⟩
    simp only [e]

/-- **Alternation**: `e(T, T) = 1`. -/
theorem ePair_self {n : ℕ} (hn : (n : L) ≠ 0) {T : Pt W L} (hT : n • T = 0) :
    ePair W L n T T = 1 := by
  obtain ⟨T', hT'⟩ := exists_nsmul_eq hn hT
  have hg := gT_ne_zero (W := W) (L := L) n T
  set G := ∏ i ∈ Finset.range n, tau W L (i • T') (gT W L n T) with hG
  have hG0 : G ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => tau_ne_zero _ hg)
  have hc : ∀ i : ℕ, n • (i • T') = i • T := fun i => by rw [smul_comm, hT']
  have hordG : ∀ P : Pt W L, P ≠ 0 → ord W L G P = 0 := by
    intro P _
    rw [hG, ord_prod _ _ (fun i _ => tau_ne_zero _ hg)]
    simp only [ord_tau, ord_gT hn hT, dT, Finset.sum_sub_distrib, nsmul_add, hc]
    rw [sum_cyc (ne_zero_of_cast hn) hT (n • P), sub_self]
  obtain ⟨c, _, hGc⟩ := exists_const_of_ord hG0 hordG
  have h1 : tau W L T' G = G := by rw [hGc, AlgEquiv.commutes]
  have h2 : tau W L T' G = ∏ i ∈ Finset.range n, tau W L ((i + 1) • T') (gT W L n T) := by
    rw [hG, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← tau_add_apply, succ_nsmul']
  have h3 := Finset.prod_range_succ (fun i => tau W L (i • T') (gT W L n T)) n
  rw [Finset.prod_range_succ', ← h2, h1, ← hG, zero_nsmul, tau_zero_apply, hT',
    tau_gT hn hT hT] at h3
  apply alg_cancel hg
  rw [map_one, one_mul]
  exact (mul_left_cancel₀ hG0 h3).symm

/-- **Skew-symmetry**: `e(S, T) e(T, S) = 1`. -/
theorem ePair_swap {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0) (hT : n • T = 0) :
    ePair W L n S T * ePair W L n T S = 1 := by
  have hST : n • (S + T) = 0 := by rw [nsmul_add, hS, hT, add_zero]
  have h := ePair_self hn hST
  rw [ePair_add_left hn hS hT hST, ePair_add_right hn hS hS hT, ePair_add_right hn hT hS hT,
    ePair_self hn hS, ePair_self hn hT] at h
  linear_combination h

end Bilinear

end RPLib.Weil


