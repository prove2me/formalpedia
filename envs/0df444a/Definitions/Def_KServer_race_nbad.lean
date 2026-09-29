-- Prove2me | Definitions.Def_KServer_race_nbad
-- name    : KServer_race_nbad
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T21:35:21.2285+00:00
-- url     : https://prove2.me/theorems/1771540d-7328-418d-91b5-ba4cf2837d70
-- title:
--   Closed-form expected bad-step bound for the race
-- statement:
--   The expected number of off-window (bad) coin steps of the race, multiplied by the window gap $c_B - c_{Lo}'$, is at most twice the sum of the two sides' expected mass defects $m\\,c_B - \\mathbb{E}[\\text{total}]$. This follows from the retirement argument (a bad step retires its below-floor chunk with probability at least one half) together with the counting bound relating the number of below-floor chunks to the mass defect. Stated multiplied through by the gap so that no division appears. Also provides plumbing: the pathwise total of a chunk system is at most $m\\,c_B$, and the first $n$ sizes miss at most $(m-n)c_B$ of the full total.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound

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
import Definitions.Def_KServer_race_pad
import Definitions.Def_KServer_race_bad

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

/-- The pathwise total of a chunk system is at most the chunk count
times the size ceiling. -/
theorem total_le_m_mul (C : ChunkSystemB X s t 0 cB T pe mL)
    (hcB : 0 ≤ cB) (ω : C.Ω) :
    (∑ i, C.size ω i) ≤ (C.m : ℝ) * cB := by
  refine le_trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    C.hsize ω i |>.2) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The first `n` sizes miss at most `(m - n)·c_B` of the full total. -/
theorem preSum_ge_total_sub (C : ChunkSystemB X s t 0 cB T pe mL)
    (ωc : C.Ω) (hcB : 0 ≤ cB) {n : ℕ} (hn : n ≤ C.m) :
    preSum C ωc C.m - ((C.m - n : ℕ) : ℝ) * cB ≤ preSum C ωc n := by
  have h1 : preSum C ωc C.m - preSum C ωc n
      = ∑ i ∈ Finset.Ico n C.m, C.sizeN i ωc := by
    unfold preSum
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le n) hn,
      Finset.range_eq_Ico]
    ring
  have h2 : ∑ i ∈ Finset.Ico n C.m, C.sizeN i ωc
      ≤ ((C.m - n : ℕ) : ℝ) * cB := by
    refine le_trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.Ico n C.m) =>
      sizeN_le_cB C hcB i ωc) (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  linarith

section NbadBound

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ) (cLo' : ℝ)

/-- **The expected bad-step count in closed form**: the retirement
argument reduces it to the expected side bad-chunk counts, which the
counting bound turns into the expected side mass defects.  No division:
the bound is stated multiplied through by `c_B - c_{Lo}'`. -/
theorem race_Nbad_bound (hε : 0 < ε) (hεLo : ε ≤ cLo') (hcB : 0 ≤ cB)
    (hLoB : cLo' ≤ cB) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m) :
    (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * Nbad A BL BR CC κ cLo' ω) * (cB - cLo')
      ≤ 2 * (((BL.m : ℝ) * cB
            - ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i)
          + ((BR.m : ℝ) * cB
            - ∑ r : BR.Ω, BR.P r * ∑ i, BR.size r i)) := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  have hNle := Nbad_le A BL BR CC κ ε cLo' hε hεLo
  -- pathwise: the side bad counts times the gap are at most the mass
  -- defects at full length
  have hpt : ∀ ω : RΩ A BL BR CC κ,
      (badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ)
          * (cB - cLo')
        ≤ ((BL.m : ℝ) * cB - preSum BL ω.2.1 BL.m)
          + ((BR.m : ℝ) * cB - preSum BR ω.2.2.1 BR.m) := by
    intro ω
    have hbL := badCount_bound cLo' BL ω.2.1 hcB hLoB κ
    have hbR := badCount_bound cLo' BR ω.2.2.1 hcB hLoB κ
    have htL := preSum_ge_total_sub BL ω.2.1 hcB hκL
    have htR := preSum_ge_total_sub BR ω.2.2.1 hcB hκR
    have hcastL : ((κ : ℝ)) * cB + ((BL.m - κ : ℕ) : ℝ) * cB
        = (BL.m : ℝ) * cB := by
      rw [← add_mul]
      congr 1
      rw [Nat.cast_sub hκL]
      ring
    have hcastR : ((κ : ℝ)) * cB + ((BR.m - κ : ℕ) : ℝ) * cB
        = (BR.m : ℝ) * cB := by
      rw [← add_mul]
      congr 1
      rw [Nat.cast_sub hκR]
      ring
    have hL2 : badCount cLo' BL ω.2.1 κ * (cB - cLo')
        ≤ (BL.m : ℝ) * cB - preSum BL ω.2.1 BL.m := by
      have := htL
      nlinarith [hbL]
    have hR2 : badCount cLo' BR ω.2.2.1 κ * (cB - cLo')
        ≤ (BR.m : ℝ) * cB - preSum BR ω.2.2.1 BR.m := by
      have := htR
      nlinarith [hbR]
    nlinarith [hL2, hR2]
  -- expectation of the right-hand side marginalizes to the side systems
  have hmargtot : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (((BL.m : ℝ) * cB - preSum BL ω.2.1 BL.m)
        + ((BR.m : ℝ) * cB - preSum BR ω.2.2.1 BR.m))
      = (((BL.m : ℝ) * cB
            - ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i)
          + ((BR.m : ℝ) * cB
            - ∑ r : BR.Ω, BR.P r * ∑ i, BR.size r i)) := by
    have h6 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (((BL.m : ℝ) * cB - preSum BL ω.2.1 BL.m)
          + ((BR.m : ℝ) * cB - preSum BR ω.2.2.1 BR.m))
        = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
            * (((BL.m : ℝ) * cB - preSum BL l BL.m)
              + ((BR.m : ℝ) * cB - preSum BR r BR.m)) :=
      RP_margLR A BL BR CC κ ε hε
        (fun l r => ((BL.m : ℝ) * cB - preSum BL l BL.m)
          + ((BR.m : ℝ) * cB - preSum BR r BR.m))
    have hrow : ∀ l : BL.Ω,
        ∑ r : BR.Ω, BL.P l * BR.P r
          * (((BL.m : ℝ) * cB - preSum BL l BL.m)
            + ((BR.m : ℝ) * cB - preSum BR r BR.m))
        = BL.P l * ((BL.m : ℝ) * cB - preSum BL l BL.m)
          + BL.P l * (∑ r : BR.Ω, BR.P r
              * ((BR.m : ℝ) * cB - preSum BR r BR.m)) := by
      intro l
      rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) =>
        show BL.P l * BR.P r
            * (((BL.m : ℝ) * cB - preSum BL l BL.m)
              + ((BR.m : ℝ) * cB - preSum BR r BR.m))
          = BL.P l * ((BL.m : ℝ) * cB - preSum BL l BL.m) * BR.P r
            + BL.P l * (BR.P r
                * ((BR.m : ℝ) * cB - preSum BR r BR.m))
          from by ring),
        Finset.sum_add_distrib]
      congr 1
      · exact sum_P_mul BR.P BR.hPsum
          (BL.P l * ((BL.m : ℝ) * cB - preSum BL l BL.m)) _
          (fun r => by ring)
      · rw [Finset.mul_sum]
    have h7 : ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
        * (((BL.m : ℝ) * cB - preSum BL l BL.m)
          + ((BR.m : ℝ) * cB - preSum BR r BR.m))
        = (∑ l : BL.Ω, BL.P l
              * ((BL.m : ℝ) * cB - preSum BL l BL.m))
          + ∑ r : BR.Ω, BR.P r
              * ((BR.m : ℝ) * cB - preSum BR r BR.m) := by
      rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hrow l,
        Finset.sum_add_distrib]
      congr 1
      exact sum_P_mul BL.P BL.hPsum
        (∑ r : BR.Ω, BR.P r * ((BR.m : ℝ) * cB - preSum BR r BR.m)) _
        (fun l => by ring)
    have hLtot : ∑ l : BL.Ω, BL.P l
        * ((BL.m : ℝ) * cB - preSum BL l BL.m)
        = (BL.m : ℝ) * cB
          - ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i := by
      rw [sum_mul_sub BL.P (fun _ => (BL.m : ℝ) * cB)
          (fun l => preSum BL l BL.m),
        sum_P_mul BL.P BL.hPsum ((BL.m : ℝ) * cB)
          (fun l => BL.P l * ((BL.m : ℝ) * cB)) (fun l => by ring)]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by rw [preSum_total]
    have hRtot : ∑ r : BR.Ω, BR.P r
        * ((BR.m : ℝ) * cB - preSum BR r BR.m)
        = (BR.m : ℝ) * cB
          - ∑ r : BR.Ω, BR.P r * ∑ i, BR.size r i := by
      rw [sum_mul_sub BR.P (fun _ => (BR.m : ℝ) * cB)
          (fun r => preSum BR r BR.m),
        sum_P_mul BR.P BR.hPsum ((BR.m : ℝ) * cB)
          (fun r => BR.P r * ((BR.m : ℝ) * cB)) (fun r => by ring)]
      congr 1
      exact Finset.sum_congr rfl fun r _ => by rw [preSum_total]
    rw [h6, h7, hLtot, hRtot]
  -- assemble
  have hstep1 : (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * Nbad A BL BR CC κ cLo' ω) * (cB - cLo')
      ≤ (2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ))
        * (cB - cLo') := by
    have hgap : (0 : ℝ) ≤ cB - cLo' := by linarith
    exact mul_le_mul_of_nonneg_right hNle hgap
  refine le_trans hstep1 ?_
  have hstep2 : (2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ))
        * (cB - cLo')
      = 2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ((badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ)
            * (cB - cLo')) := by
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hstep2]
  have hstep3 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ)
        * (cB - cLo'))
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (((BL.m : ℝ) * cB - preSum BL ω.2.1 BL.m)
            + ((BR.m : ℝ) * cB - preSum BR ω.2.2.1 BR.m)) :=
    Finset.sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left (hpt ω) (hRP0 ω)
  rw [hmargtot] at hstep3
  linarith

end NbadBound

end Race

end KServer


