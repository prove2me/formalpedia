-- Prove2me | solution 1 for Aumann1987.BayesRational.sum_over_partition
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:27:45.302603+00:00
-- url     : https://prove2.me/submissions/d57c0b25-0f79-4414-83e2-d82a78cce07a

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Real.Basic
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem

open Finset

open Aumann1987.BayesRational in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Ω : Type*} [Fintype Ω] (h : ι → (∀ i, S i) → ℝ) (I : InformationSystem Ω S) (i : ι)
    (hrat : ∀ ω, IsBayesRationalAt h I.p I.P I.s i ω)
    (g : Ω → S i) (hg : ∀ ω ω', (I.P i).r ω ω' → g ω = g ω') :
    expPayoff h I.p (deviate I.s i g) i ≤ expPayoff h I.p I.s i := by
  classical
  have hp0 : ∀ ω, 0 ≤ I.p ω := I.isProb.1
  -- membership in a cell
  have hcellmem : ∀ (ω x : Ω),
      x ∈ Finset.univ.filter (fun y => (I.P i).r ω y) ↔ (I.P i).r ω x := by
    intro ω x
    simp [Finset.mem_filter]
  -- the per-cell inequality: deviating inside one information set cannot help
  have hcellIneq : ∀ ω : Ω,
      (∑ ω' ∈ Finset.univ.filter (fun y => (I.P i).r ω y),
          I.p ω' * h i (Function.update (I.s ω') i (g ω')))
        ≤ (∑ ω' ∈ Finset.univ.filter (fun y => (I.P i).r ω y),
          I.p ω' * h i (I.s ω')) := by
    intro ω
    by_cases hm : ∑ ω' ∈ Finset.univ.filter (fun y => (I.P i).r ω y), I.p ω' = 0
    · -- null cell: every weight in the cell vanishes
      have hvanish : ∀ ω' ∈ Finset.univ.filter (fun y => (I.P i).r ω y), I.p ω' = 0 :=
        fun ω' hω' =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun ω'' _ => hp0 ω'')).mp hm ω' hω'
      rw [Finset.sum_eq_zero fun ω' hω' => by rw [hvanish ω' hω']; ring,
        Finset.sum_eq_zero fun ω' hω' => by rw [hvanish ω' hω']; ring]
    · -- positive cell: multiply the conditional inequality by the cell mass
      have hpos : 0 < ∑ ω' ∈ Finset.univ.filter (fun y => (I.P i).r ω y), I.p ω' :=
        lt_of_le_of_ne (Finset.sum_nonneg fun ω' _ => hp0 ω') (fun hcon => hm hcon.symm)
      have hr := hrat ω (g ω)
      simp only [condExp] at hr
      have hconv : ∀ ω' ∈ Finset.univ.filter (fun y => (I.P i).r ω y),
          I.p ω' * h i (Function.update (I.s ω') i (g ω'))
            = I.p ω' * h i (Function.update (I.s ω') i (g ω)) := by
        intro ω' hω'
        rw [hg ω ω' ((hcellmem ω ω').mp hω')]
      rw [Finset.sum_congr rfl hconv]
      exact (div_le_div_iff_of_pos_right (c :=
        ∑ ω' ∈ Finset.univ.filter (fun y => (I.P i).r ω y), I.p ω') hpos).mp hr
  -- decompose both expectations along the partition into cells, via the quotient
  letI : DecidableRel (I.P i).r := Classical.decRel _
  letI : Fintype (Quotient (I.P i)) := Quotient.fintype (I.P i)
  have hpart : ∀ F : Ω → ℝ,
      ∑ ω, I.p ω * F ω
        = ∑ c : Quotient (I.P i),
            ∑ ω ∈ Finset.univ.filter (fun ω => Quotient.mk (I.P i) ω = c), I.p ω * F ω := by
    intro F
    rw [Finset.sum_fiberwise_of_maps_to
      (t := (Finset.univ : Finset (Quotient (I.P i))))
      (g := fun ω => Quotient.mk (I.P i) ω)
      (f := fun ω => I.p ω * F ω)]
    simp
  -- the fiber over the class of `ω₀` is exactly the cell of `ω₀`
  have hfiber : ∀ (c : Quotient (I.P i)) (ω₀ : Ω),
      c = Quotient.mk (I.P i) ω₀ →
        Finset.univ.filter (fun ω => Quotient.mk (I.P i) ω = c)
          = Finset.univ.filter (fun y => (I.P i).r ω₀ y) := by
    intro c ω₀ hc
    rw [hc]
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Quotient.eq]
    constructor
    · intro hh
      exact (I.P i).symm hh
    · intro hh
      exact (I.P i).symm hh
  show ∑ ω, I.p ω * h i (Function.update (I.s ω) i (g ω))
      ≤ ∑ ω, I.p ω * h i (I.s ω)
  rw [hpart (fun ω => h i (Function.update (I.s ω) i (g ω))),
    hpart (fun ω => h i (I.s ω))]
  refine Finset.sum_le_sum fun c _ => ?_
  obtain ⟨ω₀, hc⟩ := c.exists_rep
  rw [hfiber c ω₀ hc.symm]
  exact hcellIneq ω₀
