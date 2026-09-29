-- Prove2me | Definitions.Def_KServer_race_ppe2
-- name    : KServer_race_ppe2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T00:53:46.069655+00:00
-- url     : https://prove2.me/theorems/7e22cc17-8339-4d5b-a405-67147f9fa8a9
-- title:
--   Race tail decompositions and the race tail variance
-- statement:
--   Race tail decompositions and the race tail variance bound. Every race tail cut at or beyond the head decomposes exactly: inside the coin phase as the coin suffix plus the survivor's side tail (beyond the consumed prefix) plus the continuation tail past its first chunk; past the coin phase (by induction over the tail slots) as the selected side's tail plus the continuation's tail at coin-determined indices. Auxiliary: side tails are monotone and Lipschitz in the index with constant c_B; coin terms lie in [0, c_B]; race sizes vanish beyond the race length; left/right/continuation marginalizations of the race measure. The main theorem race_var_rtail: every race tail concentrates around an explicit centre (the side tail mean at a fixed reference index plus the continuation tail mean plus a window offset) with second moment at most (5/4)(2 VS + VC) + 20 kappa^2 c_B^2, where VS bounds all side tail variances (both sides, all indices), VC the continuation's, and the sides have equal chunk counts and equal tail means (hmm, htails). The proof splits the tail into the selected side tail at a fixed index, the continuation tail at a fixed index, and a pointwise window remainder of size at most 2 kappa c_B; the side-continuation cross term vanishes by independence of the continuation coordinate; the selected square is bounded by the sum of the two branch squares; and the remainder enters through a weighted (5/4, 5) split. This is the per-cell workhorse for the coin-phase prophecy energy of the race.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: race prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp
import Definitions.Def_KServer_race_var3
import Definitions.Def_KServer_race_gainsum
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_prophecy2
import Definitions.Def_KServer_prophecy3
import Definitions.Def_KServer_race_ppe1

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section SideTails

variable (C : ChunkSystemB X s t 0 cB T pe mL)

/-- The tail is the total minus the prefix. -/
theorem preSum_sub_tail (j : ℕ) (x : C.Ω) :
    preSum C x C.m - preSum C x j = C.tailSum j x := by
  rcases Nat.le_total j C.m with hj | hj
  · unfold preSum ChunkSystemB.tailSum
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun i => C.sizeN i x)
        (Nat.zero_le j) hj]
    ring
  · rw [preSum_stable C x hj]
    unfold ChunkSystemB.tailSum
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    ring

/-- Tails are nonnegative. -/
theorem tailSum_nonneg (hcB : 0 ≤ cB) (j : ℕ) (x : C.Ω) :
    0 ≤ C.tailSum j x :=
  Finset.sum_nonneg fun i _ => C.sizeN_nonneg (le_refl 0) i x

/-- One-sided tail Lipschitz bound in the index. -/
theorem tailSum_sub_le (hcB : 0 ≤ cB) {j j' : ℕ} (hjj : j ≤ j') (x : C.Ω) :
    C.tailSum j x - C.tailSum j' x ≤ ((j' - j : ℕ) : ℝ) * cB := by
  have h1 : C.tailSum j x - C.tailSum j' x
      = ∑ i ∈ Finset.Ico j (min j' C.m), C.sizeN i x := by
    unfold ChunkSystemB.tailSum
    rcases Nat.le_total j' C.m with hj' | hj'
    · rw [min_eq_left hj',
        ← Finset.sum_Ico_consecutive (fun i => C.sizeN i x) hjj hj']
      ring
    · rw [min_eq_right hj', Finset.Ico_eq_empty (a := j') (by omega),
        Finset.sum_empty]
      rcases Nat.le_total j C.m with hj | hj
      · ring
      · rw [Finset.Ico_eq_empty (show ¬ j < C.m by omega)]
        simp
  rw [h1]
  have h2 : ∑ i ∈ Finset.Ico j (min j' C.m), C.sizeN i x
      ≤ ∑ _i ∈ Finset.Ico j (min j' C.m), cB :=
    Finset.sum_le_sum fun i _ => sizeN_le_cB C hcB i x
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
  have h3 : ((min j' C.m - j : ℕ) : ℝ) ≤ ((j' - j : ℕ) : ℝ) := by
    have : min j' C.m - j ≤ j' - j := by omega
    exact_mod_cast this
  have h4 : ((min j' C.m - j : ℕ) : ℝ) * cB ≤ ((j' - j : ℕ) : ℝ) * cB :=
    mul_le_mul_of_nonneg_right h3 hcB
  linarith

/-- Two-sided tail comparison: tails decrease in the index. -/
theorem tailSum_anti (hcB : 0 ≤ cB) {j j' : ℕ} (hjj : j ≤ j') (x : C.Ω) :
    C.tailSum j' x ≤ C.tailSum j x := by
  have h1 := tailSum_sub_le C hcB hjj x
  have h2 : C.tailSum j x - C.tailSum j' x
      = ∑ i ∈ Finset.Ico j (min j' C.m), C.sizeN i x := by
    unfold ChunkSystemB.tailSum
    rcases Nat.le_total j' C.m with hj' | hj'
    · rw [min_eq_left hj',
        ← Finset.sum_Ico_consecutive (fun i => C.sizeN i x) hjj hj']
      ring
    · rw [min_eq_right hj', Finset.Ico_eq_empty (a := j') (by omega),
        Finset.sum_empty]
      rcases Nat.le_total j C.m with hj | hj
      · ring
      · rw [Finset.Ico_eq_empty (show ¬ j < C.m by omega)]
        simp
  have h3 : 0 ≤ ∑ i ∈ Finset.Ico j (min j' C.m), C.sizeN i x :=
    Finset.sum_nonneg fun i _ => C.sizeN_nonneg (le_refl 0) i x
  linarith

end SideTails

section RaceDecomp

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- The survivor part is the selected side's tail beyond the consumed
prefix. -/
theorem survPart_eq_tail (ω : RΩ A BL BR CC κ) :
    survPart A BL BR CC κ ω
      = if survL A BL BR CC κ ω
        then BL.tailSum (cntL ω.2.2.2.2 κ + 1) ω.2.1
        else BR.tailSum (cntR ω.2.2.2.2 κ + 1) ω.2.2.1 := by
  unfold survPart
  by_cases hs : survL A BL BR CC κ ω
  · rw [if_pos hs, if_pos hs, preSum_sub_tail]
  · rw [if_neg hs, if_neg hs, preSum_sub_tail]

/-- The continuation part is the continuation tail past its first
chunk. -/
theorem ccPart_eq_tail (ω : RΩ A BL BR CC κ) :
    ccPart A BL BR CC κ ω = CC.tailSum 1 ω.2.2.2.1 := by
  unfold ccPart
  rw [preSum_sub_tail]

/-- **Coin-phase tail decomposition**: a race tail cut inside the coin
phase is the coin suffix plus the survivor and continuation parts. -/
theorem rtail_coin_decomp (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {j₀ : ℕ} (hj₀ : j₀ ≤ κ) (ω : RΩ A BL BR CC κ) :
    rtailN A BL BR CC κ ε (A.m + j₀) ω
      = (∑ j ∈ Finset.Ico j₀ κ, coinTerm A BL BR CC κ ε ω j)
        + survPart A BL BR CC κ ω + ccPart A BL BR CC κ ω := by
  have hbase := rtail_head_decomp A BL BR CC κ ε hκL hκR
    (le_refl A.m) ω
  rw [Finset.Ico_self, Finset.sum_empty, zero_add] at hbase
  have hstep : rtailN A BL BR CC κ ε A.m ω
      = (∑ j ∈ Finset.range j₀,
          rsize A BL BR CC κ ε ω (A.m + j))
        + rtailN A BL BR CC κ ε (A.m + j₀) ω := by
    unfold rtailN
    have hcov : A.m + j₀ ≤ mrace A BL BR CC κ := by
      unfold mrace
      omega
    rw [← Finset.sum_Ico_consecutive (fun r => rsize A BL BR CC κ ε ω r)
      (show A.m ≤ A.m + j₀ by omega) hcov]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun i _ => rfl
  have hcoin : ∀ j < κ, rsize A BL BR CC κ ε ω (A.m + j)
      = coinTerm A BL BR CC κ ε ω j := by
    intro j hj
    unfold rsize coinTerm
    rw [if_neg (by omega), if_pos (by omega)]
    have hj' : A.m + j - A.m = j := by omega
    rw [hj']
  have hpre : ∑ j ∈ Finset.range j₀,
      rsize A BL BR CC κ ε ω (A.m + j)
      = ∑ j ∈ Finset.range j₀, coinTerm A BL BR CC κ ε ω j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    exact hcoin j (by omega)
  have hsplit : (∑ j ∈ Finset.range j₀, coinTerm A BL BR CC κ ε ω j)
      + ∑ j ∈ Finset.Ico j₀ κ, coinTerm A BL BR CC κ ε ω j
      = ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le j₀) hj₀
  have hgb : gBlock A BL BR CC κ ε ω
      = (∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
        + survPart A BL BR CC κ ω := rfl
  linarith [hbase, hstep, hpre, hsplit, hgb]

/-- Coin terms lie in `[0, c_B]`. -/
theorem coinTerm_mem (hε : 0 < ε) (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ)
    (j : ℕ) : 0 ≤ coinTerm A BL BR CC κ ε ω j
      ∧ coinTerm A BL BR CC κ ε ω j ≤ cB := by
  unfold coinTerm
  have hnL0 : 0 ≤ nextL A BL BR CC κ ω j :=
    BL.sizeN_nonneg (le_refl 0) _ _
  have hnR0 : 0 ≤ nextR A BL BR CC κ ω j :=
    BR.sizeN_nonneg (le_refl 0) _ _
  have hnLB : nextL A BL BR CC κ ω j ≤ cB := sizeN_le_cB BL hcB _ _
  have hpL : 0 < probL (nextL A BL BR CC κ ω j)
      (nextR A BL BR CC κ ω j) ε := probL_pos hε
  have hpL1 : probL (nextL A BL BR CC κ ω j)
      (nextR A BL BR CC κ ω j) ε ≤ 1 := by
    unfold probL
    have h1 : (0 : ℝ) < max (nextL A BL BR CC κ ω j) ε :=
      lt_of_lt_of_le hε (le_max_right _ _)
    have h2 : (0 : ℝ) < max (nextR A BL BR CC κ ω j) ε :=
      lt_of_lt_of_le hε (le_max_right _ _)
    rw [div_le_one (by linarith)]
    linarith
  constructor
  · refine le_min (mul_nonneg (le_of_lt hpL) hnL0) ?_
    have hpR : 0 < probL (nextR A BL BR CC κ ω j)
        (nextL A BL BR CC κ ω j) ε := probL_pos hε
    exact mul_nonneg (le_of_lt hpR) hnR0
  · refine le_trans (min_le_left _ _) ?_
    calc probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
          * nextL A BL BR CC κ ω j
        ≤ 1 * nextL A BL BR CC κ ω j :=
          mul_le_mul_of_nonneg_right hpL1 hnL0
      _ = nextL A BL BR CC κ ω j := one_mul _
      _ ≤ cB := hnLB

/-- One-index tail difference is the size. -/
theorem tailSum_succ_sub (C : ChunkSystemB X s t 0 cB T pe mL)
    (j : ℕ) (x : C.Ω) :
    C.tailSum j x - C.tailSum (j + 1) x = C.sizeN j x := by
  have h1 := preSum_sub_tail C j x
  have h2 := preSum_sub_tail C (j + 1) x
  have h3 : preSum C x (j + 1) = preSum C x j + C.sizeN j x := by
    unfold preSum
    rw [Finset.sum_range_succ]
  linarith

/-- Race sizes vanish beyond the race length. -/
theorem rsize_beyond (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {r : ℕ} (hr : mrace A BL BR CC κ ≤ r) (ω : RΩ A BL BR CC κ) :
    rsize A BL BR CC κ ε ω r = 0 := by
  have hAm : A.m + κ ≤ r := by
    unfold mrace at hr
    omega
  unfold rsize
  rw [if_neg (by omega), if_neg (by omega)]
  set k := r - A.m - κ with hk
  have hkbig : max BL.m BR.m + CC.m ≤ k := by
    unfold mrace at hr
    omega
  have hrem : remCnt A BL BR CC κ ω ≤ max BL.m BR.m := by
    unfold remCnt
    by_cases hs : survL A BL BR CC κ ω
    · rw [if_pos hs]
      omega
    · rw [if_neg hs]
      omega
  by_cases h0 : k = 0 ∨ k = remCnt A BL BR CC κ ω
  · rw [if_pos h0]
  · rw [if_neg h0]
    push_neg at h0
    rw [if_neg (by omega)]
    unfold ChunkSystemB.sizeN
    rw [dif_neg (by omega)]

/-- Peeling one race chunk off a race tail. -/
theorem rtailN_peel (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m) (e : ℕ)
    (ω : RΩ A BL BR CC κ) :
    rtailN A BL BR CC κ ε e ω
      = rsize A BL BR CC κ ε ω e + rtailN A BL BR CC κ ε (e + 1) ω := by
  by_cases he : e < mrace A BL BR CC κ
  · unfold rtailN
    rw [Finset.sum_eq_sum_Ico_succ_bot he]
  · unfold rtailN
    rw [Finset.Ico_eq_empty (by omega), Finset.Ico_eq_empty (by omega),
      Finset.sum_empty,
      rsize_beyond A BL BR CC κ ε hκL hκR (by omega) ω]
    ring

/-- **Tail-phase decomposition**: past the coin phase, a race tail is
the selected side's tail plus the continuation's tail, at
coin-determined indices. -/
theorem rtail_tail_decomp (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (ω : RΩ A BL BR CC κ) :
    rtailN A BL BR CC κ ε (A.m + κ + k₀) ω
      = (if survL A BL BR CC κ ω
          then BL.tailSum (cntL ω.2.2.2.2 κ + k₀) ω.2.1
          else BR.tailSum (cntR ω.2.2.2.2 κ + k₀) ω.2.2.1)
        + CC.tailSum (max (k₀ - remCnt A BL BR CC κ ω) 1) ω.2.2.2.1 := by
  induction k₀ with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hkpos
    · subst hk
      have h1 := rtail_coin_decomp A BL BR CC κ ε hκL hκR
        (le_refl κ) ω
      rw [Finset.Ico_self, Finset.sum_empty, zero_add] at h1
      have h2 := rtailN_peel A BL BR CC κ ε hκL hκR (A.m + κ) ω
      have h3 : rsize A BL BR CC κ ε ω (A.m + κ) = 0 := by
        unfold rsize
        rw [if_neg (by omega), if_neg (by omega)]
        rw [if_pos (Or.inl (by omega))]
      have h4 : A.m + κ + 1 = A.m + κ + 1 := rfl
      rw [h3, zero_add] at h2
      rw [← h2, h1, survPart_eq_tail, ccPart_eq_tail]
      have h5 : max (1 - remCnt A BL BR CC κ ω) 1 = 1 := by omega
      rw [h5]
    · have hstep := rtailN_peel A BL BR CC κ ε hκL hκR (A.m + κ + k) ω
      have hkk : A.m + κ + k + 1 = A.m + κ + (k + 1) := by omega
      rw [hkk] at hstep
      have hrs : rsize A BL BR CC κ ε ω (A.m + κ + k)
          = (if k = 0 ∨ k = remCnt A BL BR CC κ ω then 0
             else if k < remCnt A BL BR CC κ ω then
               (if survL A BL BR CC κ ω
                then BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1
                else BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1)
             else CC.sizeN (k - remCnt A BL BR CC κ ω) ω.2.2.2.1) := by
        unfold rsize
        rw [if_neg (by omega), if_neg (by omega)]
        have hk' : A.m + κ + k - A.m - κ = k := by omega
        rw [hk']
      have hLm : cntL ω.2.2.2.2 κ + remCnt A BL BR CC κ ω = BL.m
          ∨ ¬ survL A BL BR CC κ ω := by
        by_cases hs : survL A BL BR CC κ ω
        · left
          unfold remCnt
          rw [if_pos hs]
          have := cntL_le ω.2.2.2.2 (le_refl κ)
          omega
        · right
          exact hs
      have hRm : cntR ω.2.2.2.2 κ + remCnt A BL BR CC κ ω = BR.m
          ∨ survL A BL BR CC κ ω := by
        by_cases hs : survL A BL BR CC κ ω
        · right
          exact hs
        · left
          unfold remCnt
          rw [if_neg hs]
          have := cntR_le ω.2.2.2.2 (le_refl κ)
          omega
      rw [ih hkpos] at hstep
      set rc := remCnt A BL BR CC κ ω with hrc
      -- three cases for the peeled slot
      rcases Nat.lt_trichotomy k rc with hklt | hkeq | hkgt
      · -- selected side consumes one more chunk
        have hmax1 : max (k - rc) 1 = 1 := by omega
        have hmax2 : max (k + 1 - rc) 1 = 1 := by omega
        rw [hmax1] at hstep
        rw [hmax2]
        by_cases hs : survL A BL BR CC κ ω
        · rw [if_pos hs] at hstep ⊢
          have htd := tailSum_succ_sub BL (cntL ω.2.2.2.2 κ + k) ω.2.1
          have hrs2 : rsize A BL BR CC κ ε ω (A.m + κ + k)
              = BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1 := by
            rw [hrs, if_neg (by omega), if_pos (by omega), if_pos hs]
          have hidx : cntL ω.2.2.2.2 κ + k + 1
              = cntL ω.2.2.2.2 κ + (k + 1) := by omega
          rw [hidx] at htd
          linarith [hstep, htd, hrs2]
        · rw [if_neg hs] at hstep ⊢
          have htd := tailSum_succ_sub BR (cntR ω.2.2.2.2 κ + k) ω.2.2.1
          have hrs2 : rsize A BL BR CC κ ε ω (A.m + κ + k)
              = BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1 := by
            rw [hrs, if_neg (by omega), if_pos (by omega), if_neg hs]
          have hidx : cntR ω.2.2.2.2 κ + k + 1
              = cntR ω.2.2.2.2 κ + (k + 1) := by omega
          rw [hidx] at htd
          linarith [hstep, htd, hrs2]
      · -- the zero transition slot
        have hrs2 : rsize A BL BR CC κ ε ω (A.m + κ + k) = 0 := by
          rw [hrs, if_pos (Or.inr hkeq)]
        have hmax1 : max (k - rc) 1 = 1 := by omega
        have hmax2 : max (k + 1 - rc) 1 = 1 := by omega
        rw [hmax1] at hstep
        rw [hmax2]
        by_cases hs : survL A BL BR CC κ ω
        · rw [if_pos hs] at hstep ⊢
          have hLm' : cntL ω.2.2.2.2 κ + rc = BL.m := by
            rcases hLm with h | h
            · exact h
            · exact absurd hs h
          have ht1 : BL.tailSum (cntL ω.2.2.2.2 κ + k) ω.2.1 = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          have ht2 : BL.tailSum (cntL ω.2.2.2.2 κ + (k + 1)) ω.2.1 = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          rw [ht2]
          rw [ht1] at hstep
          linarith [hstep, hrs2]
        · rw [if_neg hs] at hstep ⊢
          have hRm' : cntR ω.2.2.2.2 κ + rc = BR.m := by
            rcases hRm with h | h
            · exact h
            · exact absurd h hs
          have ht1 : BR.tailSum (cntR ω.2.2.2.2 κ + k) ω.2.2.1 = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          have ht2 : BR.tailSum (cntR ω.2.2.2.2 κ + (k + 1)) ω.2.2.1
              = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          rw [ht2]
          rw [ht1] at hstep
          linarith [hstep, hrs2]
      · -- the continuation consumes one more chunk
        have hrs2 : rsize A BL BR CC κ ε ω (A.m + κ + k)
            = CC.sizeN (k - rc) ω.2.2.2.1 := by
          rw [hrs, if_neg (by omega), if_neg (by omega)]
        have hmax1 : max (k - rc) 1 = k - rc := by omega
        have hmax2 : max (k + 1 - rc) 1 = k + 1 - rc := by omega
        rw [hmax1] at hstep
        rw [hmax2]
        have htd := tailSum_succ_sub CC (k - rc) ω.2.2.2.1
        have hidx : k - rc + 1 = k + 1 - rc := by omega
        rw [hidx] at htd
        -- the selected tail is unchanged (both indices beyond the side)
        by_cases hs : survL A BL BR CC κ ω
        · rw [if_pos hs] at hstep ⊢
          have hLm' : cntL ω.2.2.2.2 κ + rc = BL.m := by
            rcases hLm with h | h
            · exact h
            · exact absurd hs h
          have ht1 : BL.tailSum (cntL ω.2.2.2.2 κ + k) ω.2.1 = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          have ht2 : BL.tailSum (cntL ω.2.2.2.2 κ + (k + 1)) ω.2.1 = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          rw [ht2]
          rw [ht1] at hstep
          linarith [hstep, htd, hrs2]
        · rw [if_neg hs] at hstep ⊢
          have hRm' : cntR ω.2.2.2.2 κ + rc = BR.m := by
            rcases hRm with h | h
            · exact h
            · exact absurd h hs
          have ht1 : BR.tailSum (cntR ω.2.2.2.2 κ + k) ω.2.2.1 = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          have ht2 : BR.tailSum (cntR ω.2.2.2.2 κ + (k + 1)) ω.2.2.1
              = 0 := by
            unfold ChunkSystemB.tailSum
            rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          rw [ht2]
          rw [ht1] at hstep
          linarith [hstep, htd, hrs2]

end RaceDecomp

section RaceVar

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Left marginalization. -/
theorem RP_margL (hε : 0 < ε) (g : BL.Ω → ℝ) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω.2.1
      = ∑ l : BL.Ω, BL.P l * g l := by
  rw [RP_margLR A BL BR CC κ ε hε (fun l _ => g l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact sum_P_mul BR.P BR.hPsum (BL.P l * g l) _ (fun r => by ring)

/-- Right marginalization. -/
theorem RP_margR (hε : 0 < ε) (g : BR.Ω → ℝ) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω.2.2.1
      = ∑ r : BR.Ω, BR.P r * g r := by
  rw [RP_margLR A BL BR CC κ ε hε (fun _ r => g r)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : ∀ l : BL.Ω, BL.P l * BR.P r * g r
      = (BR.P r * g r) * BL.P l := fun l => by ring
  rw [Finset.sum_congr rfl fun l _ => h1 l, ← Finset.mul_sum, BL.hPsum,
    mul_one]

/-- The fixed-index selected tail. -/
noncomputable def selTail (jS : ℕ) (ω : RΩ A BL BR CC κ) : ℝ :=
  if survL A BL BR CC κ ω then BL.tailSum jS ω.2.1
  else BR.tailSum jS ω.2.2.1

open Classical in
/-- **Race tail variance**: every race tail cut at or beyond the head
concentrates around an explicit centre, up to the side and continuation
tail variances and a `(κ c_B)²` window term. -/
theorem race_var_rtail (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) (hmm : BL.m = BR.m)
    {VS VC : ℝ}
    (hvarL : ∀ j : ℕ, ∑ l : BL.Ω, BL.P l * (BL.tailSum j l
        - ∑ l' : BL.Ω, BL.P l' * BL.tailSum j l') ^ 2 ≤ VS)
    (hvarR : ∀ j : ℕ, ∑ r : BR.Ω, BR.P r * (BR.tailSum j r
        - ∑ r' : BR.Ω, BR.P r' * BR.tailSum j r') ^ 2 ≤ VS)
    (hvarC : ∀ j : ℕ, ∑ cc : CC.Ω, CC.P cc * (CC.tailSum j cc
        - ∑ cc' : CC.Ω, CC.P cc' * CC.tailSum j cc') ^ 2 ≤ VC)
    (htails : ∀ j : ℕ, ∑ l : BL.Ω, BL.P l * BL.tailSum j l
        = ∑ r : BR.Ω, BR.P r * BR.tailSum j r)
    {e : ℕ} (he : A.m ≤ e) :
    ∃ c₀ : ℝ, ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (rtailN A BL BR CC κ ε e ω - c₀) ^ 2
      ≤ 5 / 4 * (2 * VS + VC) + 20 * (κ : ℝ) ^ 2 * cB ^ 2 := by
  -- choose the reference indices and the remainder offset per case
  obtain ⟨jS, jC, b₀, hb₀, hBlo, hBhi⟩ :
      ∃ (jS jC : ℕ) (b₀ : ℝ), |b₀| ≤ (κ : ℝ) * cB ∧
        (∀ ω : RΩ A BL BR CC κ,
          b₀ - (κ : ℝ) * cB ≤ rtailN A BL BR CC κ ε e ω
            - selTail A BL BR CC κ jS ω - CC.tailSum jC ω.2.2.2.1) ∧
        (∀ ω : RΩ A BL BR CC κ,
          rtailN A BL BR CC κ ε e ω - selTail A BL BR CC κ jS ω
            - CC.tailSum jC ω.2.2.2.1 ≤ b₀ + (κ : ℝ) * cB) := by
    have hκcB : (0 : ℝ) ≤ (κ : ℝ) * cB := by positivity
    by_cases hcase : e ≤ A.m + κ
    · -- coin-phase cut
      refine ⟨κ + 1, 1, (κ : ℝ) * cB, by rw [abs_of_nonneg hκcB], ?_, ?_⟩
      all_goals
        intro ω
        have hdec := rtail_coin_decomp A BL BR CC κ ε hκL hκR
          (show e - A.m ≤ κ by omega) ω
        rw [show A.m + (e - A.m) = e from by omega] at hdec
        rw [ccPart_eq_tail A BL BR CC κ] at hdec
        have hcs : 0 ≤ ∑ j ∈ Finset.Ico (e - A.m) κ,
            coinTerm A BL BR CC κ ε ω j :=
          Finset.sum_nonneg fun j _ =>
            (coinTerm_mem A BL BR CC κ ε hε hcB ω j).1
        have hcs2 : ∑ j ∈ Finset.Ico (e - A.m) κ,
            coinTerm A BL BR CC κ ε ω j ≤ (κ : ℝ) * cB := by
          refine le_trans (Finset.sum_le_sum fun j _ =>
            (coinTerm_mem A BL BR CC κ ε hε hcB ω j).2) ?_
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          have h1 : ((κ - (e - A.m) : ℕ) : ℝ) ≤ (κ : ℝ) := by
            have : κ - (e - A.m) ≤ κ := by omega
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right h1 hcB
        have hsurv : 0 ≤ survPart A BL BR CC κ ω
              - selTail A BL BR CC κ (κ + 1) ω
            ∧ survPart A BL BR CC κ ω
              - selTail A BL BR CC κ (κ + 1) ω ≤ (κ : ℝ) * cB := by
          rw [survPart_eq_tail A BL BR CC κ]
          unfold selTail
          by_cases hs : survL A BL BR CC κ ω
          · rw [if_pos hs, if_pos hs]
            have hcnt : cntL ω.2.2.2.2 κ + 1 ≤ κ + 1 := by
              have := cntL_le ω.2.2.2.2 (le_refl κ)
              omega
            constructor
            · have := tailSum_anti BL hcB hcnt ω.2.1
              linarith
            · refine le_trans (tailSum_sub_le BL hcB hcnt ω.2.1) ?_
              have h1 : ((κ + 1 - (cntL ω.2.2.2.2 κ + 1) : ℕ) : ℝ)
                  ≤ (κ : ℝ) := by
                have : κ + 1 - (cntL ω.2.2.2.2 κ + 1) ≤ κ := by omega
                exact_mod_cast this
              exact mul_le_mul_of_nonneg_right h1 hcB
          · rw [if_neg hs, if_neg hs]
            have hcnt : cntR ω.2.2.2.2 κ + 1 ≤ κ + 1 := by
              have := cntR_le ω.2.2.2.2 (le_refl κ)
              omega
            constructor
            · have := tailSum_anti BR hcB hcnt ω.2.2.1
              linarith
            · refine le_trans (tailSum_sub_le BR hcB hcnt ω.2.2.1) ?_
              have h1 : ((κ + 1 - (cntR ω.2.2.2.2 κ + 1) : ℕ) : ℝ)
                  ≤ (κ : ℝ) := by
                have : κ + 1 - (cntR ω.2.2.2.2 κ + 1) ≤ κ := by omega
                exact_mod_cast this
              exact mul_le_mul_of_nonneg_right h1 hcB
        first
        | (rw [hdec]; linarith [hcs, hcs2, hsurv.1, hsurv.2])
        | (rw [hdec]; linarith [hcs, hcs2, hsurv.1, hsurv.2])
    · -- tail-phase cut
      push_neg at hcase
      set k₀ := e - A.m - κ with hk₀
      have hk₀1 : 1 ≤ k₀ := by omega
      refine ⟨k₀, max (k₀ - BL.m) 1, -((κ : ℝ) * cB),
        by rw [abs_neg, abs_of_nonneg hκcB], ?_, ?_⟩
      all_goals
        intro ω
        have hdec := rtail_tail_decomp A BL BR CC κ ε hκL hκR hk₀1 ω
        rw [show A.m + κ + k₀ = e from by omega] at hdec
        have hsel : -((κ : ℝ) * cB)
              ≤ (if survL A BL BR CC κ ω
                  then BL.tailSum (cntL ω.2.2.2.2 κ + k₀) ω.2.1
                  else BR.tailSum (cntR ω.2.2.2.2 κ + k₀) ω.2.2.1)
                - selTail A BL BR CC κ k₀ ω
            ∧ (if survL A BL BR CC κ ω
                  then BL.tailSum (cntL ω.2.2.2.2 κ + k₀) ω.2.1
                  else BR.tailSum (cntR ω.2.2.2.2 κ + k₀) ω.2.2.1)
                - selTail A BL BR CC κ k₀ ω ≤ 0 := by
          unfold selTail
          by_cases hs : survL A BL BR CC κ ω
          · rw [if_pos hs, if_pos hs]
            have hcnt : k₀ ≤ cntL ω.2.2.2.2 κ + k₀ := by omega
            constructor
            · have h2 := tailSum_sub_le BL hcB hcnt ω.2.1
              have h3 : ((cntL ω.2.2.2.2 κ + k₀ - k₀ : ℕ) : ℝ)
                  ≤ (κ : ℝ) := by
                have h4 := cntL_le ω.2.2.2.2 (le_refl κ)
                have : cntL ω.2.2.2.2 κ + k₀ - k₀ ≤ κ := by omega
                exact_mod_cast this
              have h5 : ((cntL ω.2.2.2.2 κ + k₀ - k₀ : ℕ) : ℝ) * cB
                  ≤ (κ : ℝ) * cB := mul_le_mul_of_nonneg_right h3 hcB
              linarith
            · have := tailSum_anti BL hcB hcnt ω.2.1
              linarith
          · rw [if_neg hs, if_neg hs]
            have hcnt : k₀ ≤ cntR ω.2.2.2.2 κ + k₀ := by omega
            constructor
            · have h2 := tailSum_sub_le BR hcB hcnt ω.2.2.1
              have h3 : ((cntR ω.2.2.2.2 κ + k₀ - k₀ : ℕ) : ℝ)
                  ≤ (κ : ℝ) := by
                have h4 := cntR_le ω.2.2.2.2 (le_refl κ)
                have : cntR ω.2.2.2.2 κ + k₀ - k₀ ≤ κ := by omega
                exact_mod_cast this
              have h5 : ((cntR ω.2.2.2.2 κ + k₀ - k₀ : ℕ) : ℝ) * cB
                  ≤ (κ : ℝ) * cB := mul_le_mul_of_nonneg_right h3 hcB
              linarith
            · have := tailSum_anti BR hcB hcnt ω.2.2.1
              linarith
        have hccw : -((κ : ℝ) * cB)
              ≤ CC.tailSum (max (k₀ - remCnt A BL BR CC κ ω) 1)
                  ω.2.2.2.1
                - CC.tailSum (max (k₀ - BL.m) 1) ω.2.2.2.1
            ∧ CC.tailSum (max (k₀ - remCnt A BL BR CC κ ω) 1) ω.2.2.2.1
                - CC.tailSum (max (k₀ - BL.m) 1) ω.2.2.2.1 ≤ 0 := by
          have hrcw : max (k₀ - BL.m) 1
                ≤ max (k₀ - remCnt A BL BR CC κ ω) 1
              ∧ max (k₀ - remCnt A BL BR CC κ ω) 1
                ≤ max (k₀ - BL.m) 1 + κ := by
            have hrc1 : BL.m - κ ≤ remCnt A BL BR CC κ ω
                ∧ remCnt A BL BR CC κ ω ≤ BL.m := by
              unfold remCnt
              by_cases hs : survL A BL BR CC κ ω
              · rw [if_pos hs]
                have h4 := cntL_le ω.2.2.2.2 (le_refl κ)
                omega
              · rw [if_neg hs]
                have h4 := cntR_le ω.2.2.2.2 (le_refl κ)
                omega
            omega
          constructor
          · have h2 := tailSum_sub_le CC hcB hrcw.1 ω.2.2.2.1
            have h3 : ((max (k₀ - remCnt A BL BR CC κ ω) 1
                - max (k₀ - BL.m) 1 : ℕ) : ℝ) ≤ (κ : ℝ) := by
              have : max (k₀ - remCnt A BL BR CC κ ω) 1
                  - max (k₀ - BL.m) 1 ≤ κ := by omega
              exact_mod_cast this
            have h5 : ((max (k₀ - remCnt A BL BR CC κ ω) 1
                  - max (k₀ - BL.m) 1 : ℕ) : ℝ) * cB
                ≤ (κ : ℝ) * cB := mul_le_mul_of_nonneg_right h3 hcB
            linarith
          · have := tailSum_anti CC hcB hrcw.1 ω.2.2.2.1
            linarith
        first
        | (rw [hdec]; linarith [hsel.1, hsel.2, hccw.1, hccw.2])
        | (rw [hdec]; linarith [hsel.1, hsel.2, hccw.1, hccw.2])
  -- the centres
  set cS := ∑ l : BL.Ω, BL.P l * BL.tailSum jS l with hcS
  set cC := ∑ cc : CC.Ω, CC.P cc * CC.tailSum jC cc with hcC
  refine ⟨cS + cC + b₀, ?_⟩
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  -- pointwise split
  have hpt : ∀ ω : RΩ A BL BR CC κ,
      (rtailN A BL BR CC κ ε e ω - (cS + cC + b₀)) ^ 2
      ≤ 5 / 4 * ((selTail A BL BR CC κ jS ω - cS)
          + (CC.tailSum jC ω.2.2.2.1 - cC)) ^ 2
        + 5 * (2 * (κ : ℝ) * cB) ^ 2 := by
    intro ω
    have h1 := hBlo ω
    have h2 := hBhi ω
    set u := (selTail A BL BR CC κ jS ω - cS)
      + (CC.tailSum jC ω.2.2.2.1 - cC) with hu
    set z := rtailN A BL BR CC κ ε e ω - selTail A BL BR CC κ jS ω
      - CC.tailSum jC ω.2.2.2.1 - b₀ with hz
    have hzb : |z| ≤ 2 * (κ : ℝ) * cB := by
      rw [abs_le]
      constructor <;> [skip; skip] <;>
        simp only [hz] <;> linarith
    have hexp : rtailN A BL BR CC κ ε e ω - (cS + cC + b₀) = u + z := by
      simp only [hu, hz]
      ring
    rw [hexp]
    have habs := abs_le.mp hzb
    nlinarith [sq_nonneg (u - 4 * z), sq_nonneg u, sq_nonneg z,
      habs.1, habs.2]
  -- expectation of the main square: expand and use independence
  have hmain : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((selTail A BL BR CC κ jS ω - cS)
        + (CC.tailSum jC ω.2.2.2.1 - cC)) ^ 2
      ≤ 2 * VS + VC := by
    have hsq : ∀ ω : RΩ A BL BR CC κ,
        ((selTail A BL BR CC κ jS ω - cS)
          + (CC.tailSum jC ω.2.2.2.1 - cC)) ^ 2
        = (selTail A BL BR CC κ jS ω - cS) ^ 2
          + (CC.tailSum jC ω.2.2.2.1 - cC) ^ 2
          + 2 * ((selTail A BL BR CC κ jS ω - cS)
              * (CC.tailSum jC ω.2.2.2.1 - cC)) := by
      intro ω
      ring
    rw [Finset.sum_congr rfl fun ω _ => by rw [hsq ω]]
    have hsplit : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((selTail A BL BR CC κ jS ω - cS) ^ 2
          + (CC.tailSum jC ω.2.2.2.1 - cC) ^ 2
          + 2 * ((selTail A BL BR CC κ jS ω - cS)
              * (CC.tailSum jC ω.2.2.2.1 - cC)))
        = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (selTail A BL BR CC κ jS ω - cS) ^ 2)
          + (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (CC.tailSum jC ω.2.2.2.1 - cC) ^ 2)
          + 2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * ((selTail A BL BR CC κ jS ω - cS)
              * (CC.tailSum jC ω.2.2.2.1 - cC)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ => ?_
      ring
    rw [hsplit]
    -- the cross term vanishes by independence of the continuation
    have hcross : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((selTail A BL BR CC κ jS ω - cS)
          * (CC.tailSum jC ω.2.2.2.1 - cC)) = 0 := by
      refine RP_cross_zero_C A BL BR CC κ ε hε
        (fun ω => selTail A BL BR CC κ jS ω - cS)
        (fun cc => CC.tailSum jC cc - cC)
        (fun a a' l r cc cc' χ => ?_) ?_
      · show selTail A BL BR CC κ jS (a, l, r, cc, χ) - cS
          = selTail A BL BR CC κ jS (a', l, r, cc', χ) - cS
        have hsel : selTail A BL BR CC κ jS (a, l, r, cc, χ)
            = selTail A BL BR CC κ jS (a', l, r, cc', χ) := rfl
        rw [hsel]
      · rw [Finset.sum_congr rfl fun cc _ =>
          show CC.P cc * (CC.tailSum jC cc - cC)
            = CC.P cc * CC.tailSum jC cc - cC * CC.P cc from by ring,
          Finset.sum_sub_distrib, ← Finset.mul_sum, CC.hPsum]
        simp [hcC]
    rw [hcross]
    -- the selected square by branch bounding
    have hselsq : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (selTail A BL BR CC κ jS ω - cS) ^ 2 ≤ 2 * VS := by
      have hptb : ∀ ω : RΩ A BL BR CC κ,
          (selTail A BL BR CC κ jS ω - cS) ^ 2
          ≤ (BL.tailSum jS ω.2.1 - cS) ^ 2
            + (BR.tailSum jS ω.2.2.1 - cS) ^ 2 := by
        intro ω
        unfold selTail
        by_cases hs : survL A BL BR CC κ ω
        · rw [if_pos hs]
          nlinarith [sq_nonneg (BR.tailSum jS ω.2.2.1 - cS)]
        · rw [if_neg hs]
          nlinarith [sq_nonneg (BL.tailSum jS ω.2.1 - cS)]
      refine le_trans (Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hptb ω) (hRP0 ω)) ?_
      have hd : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ((BL.tailSum jS ω.2.1 - cS) ^ 2
            + (BR.tailSum jS ω.2.2.1 - cS) ^ 2)
          = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * (BL.tailSum jS ω.2.1 - cS) ^ 2)
            + ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * (BR.tailSum jS ω.2.2.1 - cS) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        ring
      rw [hd, RP_margL A BL BR CC κ ε hε
          (fun l => (BL.tailSum jS l - cS) ^ 2),
        RP_margR A BL BR CC κ ε hε
          (fun r => (BR.tailSum jS r - cS) ^ 2)]
      have hL := hvarL jS
      have hR := hvarR jS
      rw [← hcS] at hL
      have hcSR : cS = ∑ r' : BR.Ω, BR.P r' * BR.tailSum jS r' := by
        rw [hcS]
        exact htails jS
      rw [← hcSR] at hR
      linarith
    -- the continuation square by marginalization
    have hccsq : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (CC.tailSum jC ω.2.2.2.1 - cC) ^ 2 ≤ VC := by
      rw [RP_margC A BL BR CC κ ε hε
        (fun cc => (CC.tailSum jC cc - cC) ^ 2)]
      have hC := hvarC jC
      rw [← hcC] at hC
      exact hC
    linarith
  -- assemble
  calc ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (rtailN A BL BR CC κ ε e ω - (cS + cC + b₀)) ^ 2
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (5 / 4 * ((selTail A BL BR CC κ jS ω - cS)
              + (CC.tailSum jC ω.2.2.2.1 - cC)) ^ 2
            + 5 * (2 * (κ : ℝ) * cB) ^ 2) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hpt ω) (hRP0 ω)
    _ = 5 / 4 * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ((selTail A BL BR CC κ jS ω - cS)
            + (CC.tailSum jC ω.2.2.2.1 - cC)) ^ 2)
        + 5 * (2 * (κ : ℝ) * cB) ^ 2 := by
        have hsplit2 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (5 / 4 * ((selTail A BL BR CC κ jS ω - cS)
                + (CC.tailSum jC ω.2.2.2.1 - cC)) ^ 2
              + 5 * (2 * (κ : ℝ) * cB) ^ 2)
            = (∑ ω : RΩ A BL BR CC κ,
                5 / 4 * (RP A BL BR CC κ ε ω
                  * ((selTail A BL BR CC κ jS ω - cS)
                    + (CC.tailSum jC ω.2.2.2.1 - cC)) ^ 2))
              + ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
                  * (5 * (2 * (κ : ℝ) * cB) ^ 2) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun ω _ => by ring
        have hs1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (5 * (2 * (κ : ℝ) * cB) ^ 2)
            = 5 * (2 * (κ : ℝ) * cB) ^ 2 := by
          rw [← Finset.sum_mul, RP_sum A BL BR CC κ ε hε, one_mul]
        rw [hsplit2, hs1, ← Finset.mul_sum]
    _ ≤ 5 / 4 * (2 * VS + VC) + 20 * (κ : ℝ) ^ 2 * cB ^ 2 := by
        have h1 : (5 : ℝ) * (2 * (κ : ℝ) * cB) ^ 2
            = 20 * (κ : ℝ) ^ 2 * cB ^ 2 := by ring
        rw [h1]
        linarith [hmain]

end RaceVar

end Race

end KServer


