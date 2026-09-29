-- Prove2me | Definitions.Def_KServer_race_bad
-- name    : KServer_race_bad
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T20:22:15.758026+00:00
-- url     : https://prove2.me/theorems/b4cf71af-232b-437e-a616-c89951106af9
-- title:
--   Expected bad-step bound for the race
-- statement:
--   Control of the out-of-window coin steps in the race. A coin step is bad when one of the two sides' next chunk sizes falls below the floor $c_{Lo}'$. The clamped coin probabilities favor the smaller side: at a bad step, the coin consumes a below-floor index with conditional probability at least $\tfrac12$ (if both sides are bad this is certain; if one side is bad, its clamped weight $\max(n,\varepsilon) \le c_{Lo}'$ is dominated by the other side's). By a generalized single-step tower property (any pair of prefix-measurable claims integrates against the coin weights) and a pathwise injection of retirements into below-floor indices of the consumed prefixes,
--   $$\mathbb{E}[N_{bad}] \;\le\; 2\,\mathbb{E}\big[\#\{i < \kappa : c^L_i < c_{Lo}'\} + \#\{i < \kappa : c^R_i < c_{Lo}'\}\big].$$
--   A pathwise counting bound converts per-side bad counts into total deficits: $\#\{i < n : c_i < c_{Lo}'\}\,(c_B - c_{Lo}') \le n\,c_B - \sum_{i<n} c_i$, so the expected bad-step count is controlled by the expected totals and hence, with the carried variance, by Chebyshev. This discharges the $N_b$ hypothesis of the padded anti-concentration gain for grid-regridded systems.
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt
import Definitions.Def_KServer_race_cost1
import Definitions.Def_KServer_race_cost2
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp
import Definitions.Def_KServer_race_gain
import Definitions.Def_KServer_race_pad

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section BadCount

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ) (cLo' : ℝ)

open Classical

/-- The generalized single-step tower: any pair of prefix-measurable
claims integrates against the coin weights. -/
theorem race_tower_fn (hε : 0 < ε) {j : ℕ} (hj : j < κ)
    (FL FR : ℝ → ℝ → ℝ) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω *
        (if ω.2.2.2.2 ⟨j, hj⟩ = true then
          FL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j)
         else FR (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j))
      = ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω *
          (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
              * FL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j)
            + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
              * FR (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j)) := by
  rw [sum_RΩ_expand, sum_RΩ_expand]
  refine Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun r _ =>
        Finset.sum_congr rfl fun cc _ => ?_
  have hsum : ∀ (j' : ℕ) (p : Fin j' → Bool),
      coinW A BL BR a l r (ε := ε) j' p true
        + coinW A BL BR a l r (ε := ε) j' p false = 1 := by
    intro j' p
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  show ∑ c : Fin κ → Bool,
      RP A BL BR CC κ ε (a, l, r, cc, c)
        * (if c ⟨j, hj⟩ = true then
            FL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r)
           else FR (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r))
    = ∑ c : Fin κ → Bool,
        RP A BL BR CC κ ε (a, l, r, cc, c)
          * (probL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r) ε
              * FL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r)
            + probL (BR.sizeN (cntR c j) r) (BL.sizeN (cntL c j) l) ε
              * FR (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r))
  have hK : ∀ G : (Fin κ → Bool) → ℝ,
      (∑ c : Fin κ → Bool, RP A BL BR CC κ ε (a, l, r, cc, c) * G c)
        = A.P a * (BL.P l * (BR.P r * CC.P cc))
            * ∑ c : Fin κ → Bool,
                coinWt (coinW A BL BR a l r (ε := ε)) c * G c := by
    intro G
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show A.P a * (BL.P l * (BR.P r * (CC.P cc
      * coinWt (coinW A BL BR a l r (ε := ε)) c))) * G c = _
    ring
  rw [hK, hK]
  congr 1
  calc ∑ c : Fin κ → Bool,
        coinWt (coinW A BL BR a l r (ε := ε)) c
          * (if c ⟨j, hj⟩ = true then
              FL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r)
             else FR (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r))
      = ∑ c : Fin κ → Bool,
          coinWt (coinW A BL BR a l r (ε := ε)) c
            * (if c ⟨j, hj⟩ = true then
                FL (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                  (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r)
               else
                FR (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                  (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [cntL_restrict c (le_of_lt hj) (le_refl j),
          cntR_restrict c (le_of_lt hj) (le_refl j)]
    _ = ∑ c : Fin κ → Bool,
          coinWt (coinW A BL BR a l r (ε := ε)) c
            * (coinW A BL BR a l r (ε := ε) j
                  (restrict c j (le_of_lt hj)) true
                * FL (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                    (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r)
              + coinW A BL BR a l r (ε := ε) j
                  (restrict c j (le_of_lt hj)) false
                * FR (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                    (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r)) :=
        coinWt_tower
          (fun p b => if b = true then
              FL (BL.sizeN (cntL p j) l) (BR.sizeN (cntR p j) r)
            else FR (BL.sizeN (cntL p j) l) (BR.sizeN (cntR p j) r))
          (coinW A BL BR a l r (ε := ε)) hsum hj
    _ = ∑ c : Fin κ → Bool,
          coinWt (coinW A BL BR a l r (ε := ε)) c
            * (probL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r) ε
                * FL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r)
              + probL (BR.sizeN (cntR c j) r) (BL.sizeN (cntL c j) l) ε
                * FR (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        show coinWt (coinW A BL BR a l r (ε := ε)) c
            * (probL
                (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r) ε
                * FL (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                    (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r)
              + probL
                  (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r)
                  (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l) ε
                * FR (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                    (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r))
          = _
        rw [cntL_restrict c (le_of_lt hj) (le_refl j),
          cntR_restrict c (le_of_lt hj) (le_refl j)]

/-- One-sided bad indicators. -/
noncomputable def badL (ω : RΩ A BL BR CC κ) (j : ℕ) : ℝ :=
  if nextL A BL BR CC κ ω j < cLo' then 1 else 0

noncomputable def badR (ω : RΩ A BL BR CC κ) (j : ℕ) : ℝ :=
  if nextR A BL BR CC κ ω j < cLo' then 1 else 0

/-- At an out-of-window step, the coin retires a bad index with
conditional probability at least one half. -/
theorem retire_ge (hε : 0 < ε) (hεLo : ε ≤ cLo')
    (ω : RΩ A BL BR CC κ) (j : ℕ) :
    (1 / 2) * (if windowAt A BL BR CC κ cLo' ω j then (0 : ℝ) else 1)
      ≤ probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
          * badL A BL BR CC κ cLo' ω j
        + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
          * badR A BL BR CC κ cLo' ω j := by
  have hpL := probL_pos (nL := nextL A BL BR CC κ ω j)
    (nR := nextR A BL BR CC κ ω j) hε
  have hpR := probL_pos (nL := nextR A BL BR CC κ ω j)
    (nR := nextL A BL BR CC κ ω j) hε
  by_cases hw : windowAt A BL BR CC κ cLo' ω j
  · rw [if_pos hw]
    have h1 : (0 : ℝ) ≤ badL A BL BR CC κ cLo' ω j := by
      unfold badL
      split <;> norm_num
    have h2 : (0 : ℝ) ≤ badR A BL BR CC κ cLo' ω j := by
      unfold badR
      split <;> norm_num
    nlinarith
  · rw [if_neg hw]
    unfold windowAt at hw
    rw [not_and_or, not_le, not_le] at hw
    have hprob := probL_add_probR (nextL A BL BR CC κ ω j)
      (nextR A BL BR CC κ ω j) ε hε
    by_cases hbL : nextL A BL BR CC κ ω j < cLo'
      <;> by_cases hbR : nextR A BL BR CC κ ω j < cLo'
    · -- both bad
      have h1 : badL A BL BR CC κ cLo' ω j = 1 := if_pos hbL
      have h2 : badR A BL BR CC κ cLo' ω j = 1 := if_pos hbR
      rw [h1, h2]
      linarith
    · -- left bad only: the left coin fires with probability ≥ 1/2
      have h1 : badL A BL BR CC κ cLo' ω j = 1 := if_pos hbL
      have h2 : badR A BL BR CC κ cLo' ω j = 0 := if_neg hbR
      rw [h1, h2]
      have hgeR : cLo' ≤ nextR A BL BR CC κ ω j := not_lt.mp hbR
      have hkey : (1 : ℝ) / 2
          ≤ probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε := by
        unfold probL
        have hmaxL : max (nextL A BL BR CC κ ω j) ε ≤ cLo' :=
          max_le (le_of_lt hbL) hεLo
        have hmaxR : cLo' ≤ max (nextR A BL BR CC κ ω j) ε :=
          le_trans hgeR (le_max_left _ _)
        have hD : 0 < max (nextL A BL BR CC κ ω j) ε
            + max (nextR A BL BR CC κ ω j) ε := by
          have := le_max_right (nextL A BL BR CC κ ω j) ε
          have := le_max_right (nextR A BL BR CC κ ω j) ε
          linarith
        rw [le_div_iff₀ hD]
        linarith
      linarith
    · -- right bad only
      have h1 : badL A BL BR CC κ cLo' ω j = 0 := if_neg hbL
      have h2 : badR A BL BR CC κ cLo' ω j = 1 := if_pos hbR
      rw [h1, h2]
      have hgeL : cLo' ≤ nextL A BL BR CC κ ω j := not_lt.mp hbL
      have hkey : (1 : ℝ) / 2
          ≤ probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε := by
        unfold probL
        have hmaxR : max (nextR A BL BR CC κ ω j) ε ≤ cLo' :=
          max_le (le_of_lt hbR) hεLo
        have hmaxL : cLo' ≤ max (nextL A BL BR CC κ ω j) ε :=
          le_trans hgeL (le_max_left _ _)
        have hD : 0 < max (nextR A BL BR CC κ ω j) ε
            + max (nextL A BL BR CC κ ω j) ε := by
          have := le_max_right (nextL A BL BR CC κ ω j) ε
          have := le_max_right (nextR A BL BR CC κ ω j) ε
          linarith
        rw [le_div_iff₀ hD]
        linarith
      linarith
    · -- contradiction with ¬window
      rcases hw with h | h
      · exact absurd h hbL
      · exact absurd h hbR

/-- Expected bad steps are dominated by expected retirements at each
step. -/
theorem Ebad_le_retire (hε : 0 < ε) (hεLo : ε ≤ cLo') {j : ℕ}
    (hj : j < κ) :
    (1 / 2) * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (if windowAt A BL BR CC κ cLo' ω j then (0 : ℝ) else 1)
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (if ω.2.2.2.2 ⟨j, hj⟩ = true then badL A BL BR CC κ cLo' ω j
             else badR A BL BR CC κ cLo' ω j) := by
  have htow := race_tower_fn A BL BR CC κ ε hε hj
    (fun x _ => if x < cLo' then (1 : ℝ) else 0)
    (fun _ y => if y < cLo' then (1 : ℝ) else 0)
  have hlhs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω *
      (if ω.2.2.2.2 ⟨j, hj⟩ = true then badL A BL BR CC κ cLo' ω j
       else badR A BL BR CC κ cLo' ω j)
      = ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω *
          (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
              * badL A BL BR CC κ cLo' ω j
            + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
              * badR A BL BR CC κ cLo' ω j) := htow
  rw [hlhs, Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h1 := retire_ge A BL BR CC κ ε cLo' hε hεLo ω j
  have h2 := (RP_pos A BL BR CC κ ε hε ω).le
  calc 1 / 2 * (RP A BL BR CC κ ε ω
        * (if windowAt A BL BR CC κ cLo' ω j then (0 : ℝ) else 1))
      = RP A BL BR CC κ ε ω * ((1 / 2)
          * (if windowAt A BL BR CC κ cLo' ω j then (0 : ℝ) else 1)) := by
        ring
    _ ≤ RP A BL BR CC κ ε ω
          * (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
              * badL A BL BR CC κ cLo' ω j
            + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
              * badR A BL BR CC κ cLo' ω j) :=
        mul_le_mul_of_nonneg_left h1 h2

/-- Per-side bad-index counts. -/
noncomputable def badCount (C : ChunkSystemB X s t 0 cB T pe mL)
    (ωc : C.Ω) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if C.sizeN i ωc < cLo' then (1 : ℝ) else 0

theorem badCount_mono (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    {a b : ℕ} (hab : a ≤ b) :
    badCount cLo' C ωc a ≤ badCount cLo' C ωc b := by
  unfold badCount
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega) fun i _ _ => ?_
  split <;> norm_num

/-- Pathwise: retirements inject into bad indices of the consumed
prefixes. -/
theorem retire_sum_le (ω : RΩ A BL BR CC κ) :
    ∑ j : Fin κ, (if ω.2.2.2.2 j = true
        then badL A BL BR CC κ cLo' ω (j : ℕ)
        else badR A BL BR CC κ cLo' ω (j : ℕ))
      ≤ badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ := by
  suffices h : ∀ n : ℕ, n ≤ κ →
      (∑ j ∈ Finset.univ.filter (fun j : Fin κ => (j : ℕ) < n),
        (if ω.2.2.2.2 j = true then badL A BL BR CC κ cLo' ω (j : ℕ)
         else badR A BL BR CC κ cLo' ω (j : ℕ)))
      ≤ badCount cLo' BL ω.2.1 (cntL ω.2.2.2.2 n)
        + badCount cLo' BR ω.2.2.1 (cntR ω.2.2.2.2 n) by
    have h2 := h κ (le_refl κ)
    rw [show (Finset.univ.filter (fun j : Fin κ => (j : ℕ) < κ))
        = Finset.univ from by
        ext j
        simp [j.isLt]] at h2
    refine le_trans h2 ?_
    have hL := badCount_mono cLo' BL ω.2.1
      (cntL_le ω.2.2.2.2 (le_refl κ))
    have hR := badCount_mono cLo' BR ω.2.2.1
      (cntR_le ω.2.2.2.2 (le_refl κ))
    linarith
  intro n
  induction n with
  | zero =>
    intro _
    rw [cntL_zero, cntR_zero]
    have hempty : (Finset.univ.filter (fun j : Fin κ => (j : ℕ) < 0))
        = ∅ := by
      ext j
      simp
    rw [hempty, Finset.sum_empty]
    unfold badCount
    rw [Finset.sum_range_zero, Finset.sum_range_zero]
    norm_num
  | succ n ih =>
    intro hn
    have hnκ : n < κ := by omega
    have hsplit : (Finset.univ.filter (fun j : Fin κ => (j : ℕ) < n + 1))
        = insert (⟨n, hnκ⟩ : Fin κ)
          (Finset.univ.filter (fun j : Fin κ => (j : ℕ) < n)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hj
        by_cases hjn : (j : ℕ) = n
        · left
          exact Fin.ext hjn
        · right
          omega
      · intro hj
        rcases hj with hj | hj
        · rw [hj]
          exact Nat.lt_succ_self n
        · omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp only [Fin.val_mk]
    have hih := ih (by omega)
    by_cases hb : ω.2.2.2.2 ⟨n, hnκ⟩
    · rw [if_pos hb, cntL_succ ω.2.2.2.2 hnκ, if_pos hb,
        cntR_succ ω.2.2.2.2 hnκ, if_neg (by
          intro hcon
          rw [hb] at hcon
          exact Bool.true_eq_false.mp hcon)]
      simp only [Nat.add_zero]
      have hstep : badL A BL BR CC κ cLo' ω n
          ≤ badCount cLo' BL ω.2.1 (cntL ω.2.2.2.2 n + 1)
            - badCount cLo' BL ω.2.1 (cntL ω.2.2.2.2 n) := by
        unfold badCount
        rw [Finset.sum_range_succ]
        have : badL A BL BR CC κ cLo' ω n
            = (if BL.sizeN (cntL ω.2.2.2.2 n) ω.2.1 < cLo'
              then (1 : ℝ) else 0) := rfl
        rw [this]
        linarith
      linarith
    · rw [if_neg hb, cntR_succ ω.2.2.2.2 hnκ, if_pos (by
          cases hcon : ω.2.2.2.2 ⟨n, hnκ⟩
          · rfl
          · exact absurd hcon hb),
        cntL_succ ω.2.2.2.2 hnκ, if_neg hb]
      simp only [Nat.add_zero]
      have hstep : badR A BL BR CC κ cLo' ω n
          ≤ badCount cLo' BR ω.2.2.1 (cntR ω.2.2.2.2 n + 1)
            - badCount cLo' BR ω.2.2.1 (cntR ω.2.2.2.2 n) := by
        unfold badCount
        rw [Finset.sum_range_succ]
        have : badR A BL BR CC κ cLo' ω n
            = (if BR.sizeN (cntR ω.2.2.2.2 n) ω.2.2.1 < cLo'
              then (1 : ℝ) else 0) := rfl
        rw [this]
        linarith
      linarith

/-- **The expected bad-step bound**: the expected number of
out-of-window coin steps is at most twice the expected bad-index counts
of the two sides. -/
theorem Nbad_le (hε : 0 < ε) (hεLo : ε ≤ cLo') :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * Nbad A BL BR CC κ cLo' ω
      ≤ 2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ) := by
  have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * Nbad A BL BR CC κ cLo' ω
      = ∑ j : Fin κ, ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (if windowAt A BL BR CC κ cLo' ω (j : ℕ) then (0 : ℝ)
             else 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    unfold Nbad
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
      (fun j => RP A BL BR CC κ ε ω
        * (if windowAt A BL BR CC κ cLo' ω j then (0 : ℝ) else 1)) κ]
  have h2 : ∑ j : Fin κ, ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (if windowAt A BL BR CC κ cLo' ω (j : ℕ) then (0 : ℝ) else 1)
      ≤ ∑ j : Fin κ, 2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (if ω.2.2.2.2 j = true
             then badL A BL BR CC κ cLo' ω (j : ℕ)
             else badR A BL BR CC κ cLo' ω (j : ℕ)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h3 := Ebad_le_retire A BL BR CC κ ε cLo' hε hεLo j.isLt
    linarith
  have h4 : ∑ j : Fin κ, 2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (if ω.2.2.2.2 j = true then badL A BL BR CC κ cLo' ω (j : ℕ)
         else badR A BL BR CC κ cLo' ω (j : ℕ))
      = 2 * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ j : Fin κ, (if ω.2.2.2.2 j = true
              then badL A BL BR CC κ cLo' ω (j : ℕ)
              else badR A BL BR CC κ cLo' ω (j : ℕ)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum]
  have h5 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ∑ j : Fin κ, (if ω.2.2.2.2 j = true
          then badL A BL BR CC κ cLo' ω (j : ℕ)
          else badR A BL BR CC κ cLo' ω (j : ℕ))
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (badCount cLo' BL ω.2.1 κ + badCount cLo' BR ω.2.2.1 κ) :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
      (retire_sum_le A BL BR CC κ cLo' ω)
      (RP_pos A BL BR CC κ ε hε ω).le
  rw [h1]
  refine le_trans h2 ?_
  rw [h4]
  linarith

/-- Pathwise bad-count bound from totals: sizes below the floor leave a
ceiling deficit. -/
theorem badCount_bound (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (hcB : 0 ≤ cB) (hLoB : cLo' ≤ cB) (n : ℕ) :
    badCount cLo' C ωc n * (cB - cLo')
      ≤ (n : ℝ) * cB - preSum C ωc n := by
  have h1 : ∀ i ∈ Finset.range n,
      (if C.sizeN i ωc < cLo' then (1 : ℝ) else 0) * (cB - cLo')
      ≤ cB - C.sizeN i ωc := by
    intro i _
    by_cases hb : C.sizeN i ωc < cLo'
    · rw [if_pos hb, one_mul]
      linarith
    · rw [if_neg hb, zero_mul]
      linarith [sizeN_le_cB C hcB i ωc]
  have h2 : ∑ i ∈ Finset.range n,
      (if C.sizeN i ωc < cLo' then (1 : ℝ) else 0) * (cB - cLo')
      ≤ ∑ i ∈ Finset.range n, (cB - C.sizeN i ωc) :=
    Finset.sum_le_sum h1
  rw [← Finset.sum_mul] at h2
  refine le_trans h2 (le_of_eq ?_)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  rfl

end BadCount

end Race

end KServer


