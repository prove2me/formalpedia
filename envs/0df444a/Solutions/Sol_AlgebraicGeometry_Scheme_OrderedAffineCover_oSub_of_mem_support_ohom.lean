-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.oSub_of_mem_support_ohom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7a7317d7-c5c7-564a-bfa7-42ff1d8e96b9

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_oSub_of_mem_support_ohom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace H3Aux
p2m_open "AlgebraicGeometry AlgebraicGeometry.Scheme.OrderedAffineCover"

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

theorem mem_support_olin {n m : ℕ} (f : K.OIdx n → K.OCh m) (x : K.OCh n) (w : K.OIdx m)
    (hw : w ∈ (K.olin n f x).support) : ∃ u ∈ x.support, w ∈ (f u).support := by
  classical
  have h : K.olin n f x = x.sum (fun u r => r • f u) := by
    simp only [olin, Finsupp.lift_apply]
  rw [h, Finsupp.sum] at hw
  have hw' : ∑ u ∈ x.support, (x u • f u) w ≠ 0 := by
    have := Finsupp.mem_support_iff.1 hw
    rwa [Finsupp.finset_sum_apply] at this
  obtain ⟨u, hu, hwu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw'
  refine ⟨u, hu, Finsupp.mem_support_iff.2 ?_⟩
  intro h0
  apply hwu
  show (x u • f u) w = 0
  rw [Finsupp.smul_apply, h0, smul_zero]

theorem support_single_subset' {n : ℕ} (u w : K.OIdx n) (hw : w ∈ (Finsupp.single u (1 : ℤ)).support) : w = u := by
  classical
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hw
  exact hw

theorem oSub_cons {n k : ℕ} (m : K.ι) (u : K.OIdx n) (t : K.OIdx k) (i₀ : Fin (k + 1)) (hm : t i₀ = m)
    (hu : K.OSub u t) : K.OSub (Fin.cons m u : K.OIdx (n + 1)) t := by
  intro j
  refine Fin.cases ?_ (fun j' => ?_) j
  · exact ⟨i₀, by simp [hm]⟩
  · obtain ⟨i, hi⟩ := hu j'
    exact ⟨i, by simp [hi]⟩

theorem oSub_oface {n : ℕ} (σ : K.OIdx (n + 1)) (j : Fin (n + 2)) : K.OSub (K.oface σ j) σ :=
  fun k => ⟨j.succAbove k, rfl⟩

theorem oSub_comp_perm {n : ℕ} (σ : K.OIdx n) (p : Equiv.Perm (Fin (n + 1))) : K.OSub (σ ∘ p : K.OIdx n) σ :=
  fun k => ⟨p k, rfl⟩

end H3Aux

open H3Aux in
theorem solution
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (σ : K.OIdx n) (u : K.OIdx (n + 1))
    (hu : u ∈ (K.ohom n σ).support) : K.OSub u σ := by
  classical
  induction n with
  | zero =>
    exfalso
    rw [Scheme.OrderedAffineCover.ohom_zero] at hu
    simp at hu
  | succ n ih =>
    rw [Scheme.OrderedAffineCover.ohom_succ] at hu

    obtain ⟨w, hw, huw⟩ := H3Aux.mem_support_olin K _ _ u hu
    have hu' : u = Fin.cons (σ 0) w := H3Aux.support_single_subset' K _ _ huw

    have hwσ : K.OSub w σ := by
      have hmem : w ∈ (Finsupp.single σ (1 : ℤ)).support ∨
          w ∈ (K.oesort (n + 1) (Finsupp.single σ 1)).support ∨
          w ∈ (K.olin n (K.ohom n) (K.obd n (Finsupp.single σ 1))).support := by
        by_contra h
        simp only [not_or] at h
        obtain ⟨h1, h2, h3⟩ := h
        rw [Finsupp.notMem_support_iff] at h1 h2 h3
        have : w ∉ (Finsupp.single σ (1 : ℤ) - K.oesort (n + 1) (Finsupp.single σ 1) -
            K.olin n (K.ohom n) (K.obd n (Finsupp.single σ 1))).support := by
          rw [Finsupp.notMem_support_iff, Finsupp.sub_apply, Finsupp.sub_apply, h1, h2, h3]; simp
        exact this hw
      rcases hmem with h1 | h2 | h3
      · rw [H3Aux.support_single_subset' K _ _ h1]; exact K.oSub_refl σ
      · by_cases hinj : Function.Injective σ
        · rw [K.oesort_single_of_injective _ _ hinj] at h2
          have h2' : w ∈ (Finsupp.single (σ ∘ Tuple.sort σ : K.OIdx (n + 1)) (1 : ℤ)).support :=
            Finsupp.support_smul h2
          rw [H3Aux.support_single_subset' K _ _ h2']
          exact H3Aux.oSub_comp_perm K σ _
        · rw [K.oesort_single_of_not_injective _ _ hinj] at h2
          simp at h2
      · obtain ⟨y, hy, hwy⟩ := H3Aux.mem_support_olin K _ _ w h3

        rw [K.obd_single] at hy
        obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by
          have := Finsupp.mem_support_iff.1 hy
          rwa [Finsupp.finset_sum_apply] at this)
        have hyj : y = K.oface σ j := by
          have : y ∈ (((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (K.oface σ j) (1 : ℤ)).support :=
            Finsupp.mem_support_iff.2 hj
          exact H3Aux.support_single_subset' K _ _ (Finsupp.support_smul this)
        have h' := ih (K.oface σ j) w (hyj ▸ hwy)
        exact K.oSub_trans h' (H3Aux.oSub_oface K σ j)
    rw [hu']
    exact H3Aux.oSub_cons K (σ 0) w σ 0 rfl hwσ

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_oSub_of_mem_support_ohom
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_oSub_of_mem_support_ohom (solution)
