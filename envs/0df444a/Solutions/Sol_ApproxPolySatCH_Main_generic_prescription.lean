-- Prove2me | solution 1 for ApproxPolySatCH.Main.generic_prescription
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:39:15.503196+00:00
-- url     : https://prove2.me/submissions/52503581-8e8d-4204-a36b-3778c44d8fe7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ApproxPolySatCH_Main_annihilator_presentation
import Theorems.Thm_ApproxPolySatCH_Main_positive_valuation_root
import Theorems.Thm_ApproxPolySatCH_Main_finite_fiber
import Theorems.Thm_ApproxPolySatCH_Main_lift_annihilator_roots
import Theorems.Thm_ApproxPolySatCH_Main_permuted_annihilator_data
import Theorems.Thm_ApproxPolySatCH_Main_positive_valuation_implies_APS

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution {k : Type} [Field k] {n : ℕ}
    (hn : 1 ≤ n) (f : Fin (n + 1) → Poly k n)
    (hf : MinimallyDependent f) (v : EpsilonValuation k) :
    ∃ (Q : Poly k n) (sigma : Equiv.Perm (Fin (n + 1))), Q ≠ 0 ∧
      Q.totalDegree ≤ maxDegree f ^ (n + 1) + n * maxDegree f ^ n - 1 ∧
      ∀ a : Fin n → Constants k, MvPolynomial.eval₂ (algebraMap k (Constants k)) a Q ≠ 0 →
        (prescribedFiber (fun i => f (sigma i)) a).Finite ∧
        (prescribedFiber (fun i => f (sigma i)) a).Nonempty ∧
        (APS f ↔ ∃ x ∈ prescribedFiber (fun i => f (sigma i)) a,
          0 < v.val (evaluateValued (f (sigma (Fin.last n))) x)) := by
  obtain ⟨H, hH, hHdeg, hHzero⟩ := annihilator_presentation hn f hf
  obtain ⟨sigma, G, hG0, ⟨d, hd, hGhom⟩, hroot⟩ :=
    positive_valuation_root hn f hf H hH v
  let f' : Fin (n + 1) → Poly k n := fun i => f (sigma i)
  let H' : Poly k (n + 1) := MvPolynomial.rename sigma.symm H
  obtain ⟨hf', hH', hAPS', hmax⟩ := permuted_annihilator_data f hf sigma H hH
  have hmax' : maxDegree f' = maxDegree f := hmax
  have hfin := finite_fiber hn f' hf'
  let r : LocalizationRelations f' := hfin.1.some
  have hr := hfin.2 r
  rw [hmax'] at hr
  refine ⟨G * localizationProduct r, sigma, mul_ne_zero hG0 hr.1, ?_, ?_⟩
  · have hGdeg : G.totalDegree ≤ H.totalDegree - 1 := by
      refine Finset.sup_le (fun e he => ?_)
      rw [Finsupp.sum_fintype]
      · exact (le_of_eq (hGhom e he)).trans hd
      · simp
    calc
      (G * localizationProduct r).totalDegree ≤
          G.totalDegree + (localizationProduct r).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ (H.totalDegree - 1) + n * maxDegree f ^ n :=
        Nat.add_le_add hGdeg hr.2.1
      _ ≤ maxDegree f ^ (n + 1) + n * maxDegree f ^ n - 1 := by
        by_cases hD : maxDegree f = 0
        · have hn0 : n ≠ 0 := by omega
          simp only [hD, zero_pow hn0, zero_pow (Nat.succ_ne_zero n), mul_zero,
            add_zero, nonpos_iff_eq_zero] at hHdeg ⊢
          omega
        · have hDpos : 0 < maxDegree f := Nat.pos_of_ne_zero hD
          have hP : 0 < maxDegree f ^ (n + 1) := pow_pos hDpos _
          omega
  · intro a ha
    simp only [MvPolynomial.eval₂_mul] at ha
    have haG : MvPolynomial.eval₂ (algebraMap k (Constants k)) a G ≠ 0 :=
      (mul_ne_zero_iff.mp ha).1
    have hah : MvPolynomial.eval₂ (algebraMap k (Constants k)) a
        (localizationProduct r) ≠ 0 := (mul_ne_zero_iff.mp ha).2
    refine ⟨hr.2.2 a hah, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := (hroot a haG).1
      obtain ⟨x, hx, hxz⟩ :=
        lift_annihilator_roots hn f' hf' H' hH' r a hah z hz
      exact ⟨x, hx⟩
    · constructor
      · intro hpos
        obtain ⟨z, hz, hzpos⟩ := (hroot a haG).2 hpos
        obtain ⟨x, hx, hxz⟩ :=
          lift_annihilator_roots hn f' hf' H' hH' r a hah z hz
        refine ⟨x, hx, ?_⟩
        change 0 < v.val (evaluateValued (f' (Fin.last n)) x)
        rwa [hxz]
      · intro hpos
        exact hAPS'.mp (positive_valuation_implies_APS hn f' hf' H' hH' v a hpos)
