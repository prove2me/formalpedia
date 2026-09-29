-- Prove2me | Definitions.Def_KServer_prophecy3
-- name    : KServer_prophecy3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T00:39:30.489644+00:00
-- url     : https://prove2.me/theorems/351bf59c-08a7-41ff-8aa6-51aecb120b8e
-- title:
--   Tail variance bounded by variance plus prophecy energy
-- statement:
--   Tail variance from the prophecy bound. The variance of any tail mass tailSum j of a chunk system equals its full Doob energy (trivial initial history, measurability at the final depth). Splitting the depths at j: below j the increments are exactly the two-cell prophecy partition (0, j, m), so their energy is at most PE; from j on, the prefix below j is measurable, so the tail's increments coincide with the total's, whose interval energy is at most the total's variance V. Hence Var(tailSum j) <= V + PE for every j. This is the workhorse for centring the survivor-side tails in the coin-phase prophecy analysis of the race.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_prophecy2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable {C : ChunkSystemB X s t cLo cHi total price mLo}

/-- The tail mass is measurable at the end of time. -/
theorem tailSum_congr (j : ℕ) {ω ω' : C.Ω}
    (hh : C.hist C.m ω' = C.hist C.m ω) :
    C.tailSum j ω' = C.tailSum j ω := by
  unfold ChunkSystemB.tailSum
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  exact C.sizeN_congr (C.href i C.m (by omega) ω' ω hh)

/-- Doob increments of the tail beyond its start are those of the
total. -/
theorem dinc_tail_deep {j h : ℕ} (hjh : j ≤ h) (ω : C.Ω) :
    C.dinc (C.tailSum j) h ω = C.dinc C.totalSize h ω := by
  have hsplit : ∀ ω' : C.Ω, C.totalSize ω'
      = (∑ i ∈ Finset.range (min j C.m), C.sizeN i ω') + C.tailSum j ω' := by
    intro ω'
    rw [totalSize_eq_range]
    unfold ChunkSystemB.tailSum
    rcases Nat.le_total j C.m with hjm | hmj
    · rw [min_eq_left hjm, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun i => C.sizeN i ω')
          (Nat.zero_le j) hjm, ← Finset.range_eq_Ico]
    · rw [min_eq_right hmj, Finset.Ico_eq_empty (by omega),
        Finset.sum_empty, add_zero]
  have h1 : C.dinc C.totalSize h ω
      = C.dinc (fun ω' => (∑ i ∈ Finset.range (min j C.m), C.sizeN i ω')
          + C.tailSum j ω') h ω :=
    dinc_congr_fun hsplit h ω
  rw [h1, dinc_add]
  have h2 : C.dinc (fun ω' =>
      ∑ i ∈ Finset.range (min j C.m), C.sizeN i ω') h ω = 0 := by
    refine dinc_of_meas (a := min j C.m) (by omega) (fun ω ω' hh => ?_) ω
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    exact C.sizeN_congr (C.href i (min j C.m) (by omega) ω' ω hh)
  rw [h2, zero_add]

/-- **Tail variance from the prophecy bound**: the variance of any tail
mass is at most the total's variance budget plus the prophecy energy. -/
theorem var_tail_le {V PE : ℝ}
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * (C.totalSize ω
      - ∑ ω', C.P ω' * C.totalSize ω') ^ 2 ≤ V)
    (hPPE : C.ProphecyBound PE) (j : ℕ) :
    ∑ ω, C.P ω * (C.tailSum j ω
      - ∑ ω', C.P ω' * C.tailSum j ω') ^ 2 ≤ V + PE := by
  set j' := min j C.m with hj'
  have hjj' : ∀ ω : C.Ω, C.tailSum j ω = C.tailSum j' ω := by
    intro ω
    unfold ChunkSystemB.tailSum
    rcases Nat.le_total j C.m with hjm | hmj
    · rw [hj', min_eq_left hjm]
    · rw [hj', min_eq_right hmj, Finset.Ico_eq_empty (by omega),
        Finset.Ico_eq_empty (by omega)]
  rw [Finset.sum_congr rfl fun ω _ => by
    rw [hjj' ω, Finset.sum_congr rfl fun ω' _ => by rw [hjj' ω']]]
  -- variance of tail j' equals its full Doob energy
  have hmeas : ∀ ω ω' : C.Ω, C.hist C.m ω' = C.hist C.m ω →
      C.tailSum j' ω' = C.tailSum j' ω := fun ω ω' hh => tailSum_congr j' hh
  have hc0 : ∀ ω : C.Ω, C.condExp (C.tailSum j') 0 ω
      = ∑ ω', C.P ω' * C.tailSum j' ω' := by
    intro ω
    have hatom : C.atom 0 ω = Finset.univ := by
      ext ω'
      simp only [C.mem_atom, Finset.mem_univ, iff_true]
      exact h0triv ω' ω
    unfold ChunkSystemB.condExp ChunkSystemB.mass
    rw [hatom, C.hPsum, div_one]
  have henergy : ∑ ω, C.P ω * (C.tailSum j' ω
      - ∑ ω', C.P ω' * C.tailSum j' ω') ^ 2
      = ∑ h ∈ Finset.Ico 0 C.m,
          ∑ ω, C.P ω * (C.dinc (C.tailSum j') h ω) ^ 2 := by
    have h1 := interval_energy (C := C) (C.tailSum j') (Nat.zero_le C.m)
      hmeas
    rw [← h1]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hc0 ω]
  rw [henergy]
  -- split at j'
  have hsplit : ∑ h ∈ Finset.Ico 0 C.m,
      ∑ ω, C.P ω * (C.dinc (C.tailSum j') h ω) ^ 2
      = (∑ h ∈ Finset.Ico 0 j',
          ∑ ω, C.P ω * (C.dinc (C.tailSum j') h ω) ^ 2)
        + ∑ h ∈ Finset.Ico j' C.m,
          ∑ ω, C.P ω * (C.dinc (C.tailSum j') h ω) ^ 2 := by
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le j')
      (min_le_right j C.m)]
  rw [hsplit]
  -- first part: the two-cell prophecy partition
  have hfirst : ∑ h ∈ Finset.Ico 0 j',
      ∑ ω, C.P ω * (C.dinc (C.tailSum j') h ω) ^ 2 ≤ PE := by
    set e : ℕ → ℕ := fun k => if k = 0 then 0 else if k = 1 then j' else C.m
      with he_def
    have hj'm : j' ≤ C.m := min_le_right j C.m
    have he0' : e 0 = 0 := by simp [he_def]
    have he1' : e 1 = j' := by simp [he_def]
    have he2' : e 2 = C.m := by simp [he_def]
    have heB : ∀ n : ℕ, e (n + 2) = C.m := by
      intro n
      simp only [he_def]
      rw [if_neg (by omega), if_neg (by omega)]
    have hp := hPPE 2 e he0'
      (by
        intro k
        match k with
        | 0 =>
          rw [he0', he1']
          omega
        | 1 =>
          rw [he1', show (1 + 1 : ℕ) = 2 from rfl, he2']
          exact hj'm
        | (n + 2) =>
          rw [heB n, show n + 2 + 1 = (n + 1) + 2 from by omega,
            heB (n + 1)])
      he2'
    have he1 : e 1 = j' := by simp [he_def]
    have he0 : e 0 = 0 := by simp [he_def]
    have he2 : e 2 = C.m := by simp [he_def]
    have hterm0 : ∑ h ∈ Finset.Ico (e 0) (e 1),
        ∑ ω, C.P ω * (C.dinc (C.tailSum (e 1)) h ω) ^ 2
        = ∑ h ∈ Finset.Ico 0 j',
          ∑ ω, C.P ω * (C.dinc (C.tailSum j') h ω) ^ 2 := by
      rw [he0, he1]
    have hsum2 : ∑ k ∈ Finset.range 2, ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
        ∑ ω, C.P ω * (C.dinc (C.tailSum (e (k + 1))) h ω) ^ 2
        = (∑ h ∈ Finset.Ico (e 0) (e 1),
            ∑ ω, C.P ω * (C.dinc (C.tailSum (e 1)) h ω) ^ 2)
          + ∑ h ∈ Finset.Ico (e 1) (e 2),
            ∑ ω, C.P ω * (C.dinc (C.tailSum (e 2)) h ω) ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
    rw [hsum2, hterm0] at hp
    have hnn : 0 ≤ ∑ h ∈ Finset.Ico (e 1) (e 2),
        ∑ ω, C.P ω * (C.dinc (C.tailSum (e 2)) h ω) ^ 2 :=
      Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun ω _ =>
        mul_nonneg (le_of_lt (C.hP ω)) (sq_nonneg _)
    linarith
  -- second part: increments of the total
  have hsecond : ∑ h ∈ Finset.Ico j' C.m,
      ∑ ω, C.P ω * (C.dinc (C.tailSum j') h ω) ^ 2 ≤ V := by
    have h1 : ∀ h ∈ Finset.Ico j' C.m, ∀ ω : C.Ω,
        C.dinc (C.tailSum j') h ω = C.dinc C.totalSize h ω := by
      intro h hm ω
      simp only [Finset.mem_Ico] at hm
      exact dinc_tail_deep hm.1 ω
    rw [Finset.sum_congr rfl fun h hm =>
      Finset.sum_congr rfl fun ω _ => by rw [h1 h hm ω]]
    refine le_trans (interval_energy_le_var C.totalSize j' C.m) ?_
    have hvex : (∑ ω, C.P ω * C.totalSize ω ^ 2)
        - (∑ ω, C.P ω * C.totalSize ω) ^ 2
        = ∑ ω, C.P ω * (C.totalSize ω
            - ∑ ω', C.P ω' * C.totalSize ω') ^ 2 := by
      set μ := ∑ ω', C.P ω' * C.totalSize ω' with hμ
      have h2 : ∑ ω, C.P ω * (C.totalSize ω - μ) ^ 2
          = ∑ ω, (C.P ω * C.totalSize ω ^ 2
            - 2 * μ * (C.P ω * C.totalSize ω) + μ ^ 2 * C.P ω) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        ring
      rw [h2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← hμ, C.hPsum]
      ring
    linarith [hVar, le_of_eq hvex]
  linarith

end ChunkSystemB

end KServer


