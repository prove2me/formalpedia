-- Prove2me | Definitions.Def_KServer_race_gainsum
-- name    : KServer_race_gainsum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T22:52:20.856864+00:00
-- url     : https://prove2.me/theorems/2fd41dde-a674-4530-bd8d-bf5d541bdb20
-- title:
--   The consumption martingale of the race
-- statement:
--   The consumption martingale of the race: the increments are the consumed chunk sizes minus their conditional means (the conditional consumption rates, which lie in [0, c_B]), centered on the full-reveal coin filtration. Includes the per-atom conditional mean-zero and second-moment identities, the discrete-martingale instance, increment and conditional-variance bounds, and the identity that the martingale sum equals the total consumed mass minus the accumulated conditional rates. Companion to the imbalance martingale; both feed the sharp second-moment bound on the race total's variance.
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
import Definitions.Def_KServer_discrete_martingale
import Definitions.Def_KServer_race_gain

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section GainSum

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- The one-step conditional consumption rate. -/
noncomputable def sdrift (ω : RΩ A BL BR CC κ) (j : ℕ) : ℝ :=
  probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
      * nextL A BL BR CC κ ω j
    + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
      * nextR A BL BR CC κ ω j

/-- The consumption rate depends only on the sides and the coin
prefix. -/
theorem sdrift_congr (ω ω' : RΩ A BL BR CC κ) {j : ℕ}
    (hl : ω.2.1 = ω'.2.1) (hr : ω.2.2.1 = ω'.2.2.1)
    (hc : ∀ i : Fin κ, (i : ℕ) < j → ω.2.2.2.2 i = ω'.2.2.2.2 i) :
    sdrift A BL BR CC κ ε ω j = sdrift A BL BR CC κ ε ω' j := by
  unfold sdrift
  rw [nextL_congr A BL BR CC κ ω ω' hl hc,
    nextR_congr A BL BR CC κ ω ω' hr hc]

/-- The consumption rate is between `0` and `c_B`. -/
theorem sdrift_bounds (hε : 0 < ε) (hcB : 0 ≤ cB)
    (ω : RΩ A BL BR CC κ) (j : ℕ) :
    0 ≤ sdrift A BL BR CC κ ε ω j ∧ sdrift A BL BR CC κ ε ω j ≤ cB := by
  have hnl0 : (0 : ℝ) ≤ nextL A BL BR CC κ ω j :=
    BL.sizeN_nonneg (le_refl 0) _ _
  have hnlB : nextL A BL BR CC κ ω j ≤ cB :=
    sizeN_le_cB BL hcB (cntL ω.2.2.2.2 j) ω.2.1
  have hnr0 : (0 : ℝ) ≤ nextR A BL BR CC κ ω j :=
    BR.sizeN_nonneg (le_refl 0) _ _
  have hnrB : nextR A BL BR CC κ ω j ≤ cB :=
    sizeN_le_cB BR hcB (cntR ω.2.2.2.2 j) ω.2.2.1
  have hpT : 0 < probL (nextL A BL BR CC κ ω j)
      (nextR A BL BR CC κ ω j) ε := probL_pos hε
  have hpF : 0 < probL (nextR A BL BR CC κ ω j)
      (nextL A BL BR CC κ ω j) ε := probL_pos hε
  have hp := probL_add_probR (nextL A BL BR CC κ ω j)
    (nextR A BL BR CC κ ω j) ε hε
  unfold sdrift
  constructor
  · have h1 : 0 ≤ probL (nextL A BL BR CC κ ω j)
        (nextR A BL BR CC κ ω j) ε * nextL A BL BR CC κ ω j :=
      mul_nonneg hpT.le hnl0
    have h2 : 0 ≤ probL (nextR A BL BR CC κ ω j)
        (nextL A BL BR CC κ ω j) ε * nextR A BL BR CC κ ω j :=
      mul_nonneg hpF.le hnr0
    linarith
  · have h1 : probL (nextL A BL BR CC κ ω j)
        (nextR A BL BR CC κ ω j) ε * nextL A BL BR CC κ ω j
        ≤ probL (nextL A BL BR CC κ ω j)
            (nextR A BL BR CC κ ω j) ε * cB :=
      mul_le_mul_of_nonneg_left hnlB hpT.le
    have h2 : probL (nextR A BL BR CC κ ω j)
        (nextL A BL BR CC κ ω j) ε * nextR A BL BR CC κ ω j
        ≤ probL (nextR A BL BR CC κ ω j)
            (nextL A BL BR CC κ ω j) ε * cB :=
      mul_le_mul_of_nonneg_left hnrB hpF.le
    nlinarith [h1, h2, hp]

/-- The centered consumption increments. -/
noncomputable def sgX (j : ℕ) (ω : RΩ A BL BR CC κ) : ℝ :=
  if h : j < κ then
    (if ω.2.2.2.2 ⟨j, h⟩ then nextL A BL BR CC κ ω j
     else nextR A BL BR CC κ ω j) - sdrift A BL BR CC κ ε ω j
  else 0

/-- The conditional second moments of the consumption increments. -/
noncomputable def sgV (j : ℕ) (ω : RΩ A BL BR CC κ) : ℝ :=
  if j < κ then
    probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
        * (nextL A BL BR CC κ ω j - sdrift A BL BR CC κ ε ω j) ^ 2
      + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
        * (nextR A BL BR CC κ ω j - sdrift A BL BR CC κ ε ω j) ^ 2
  else 0

/-- Conditional mean zero of the centered increments on every atom. -/
theorem race_hmart_sum (hε : 0 < ε) {j : ℕ} (hj : j < κ)
    (ω₀ : RΩ A BL BR CC κ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀),
      RP A BL BR CC κ ε ω * sgX A BL BR CC κ ε j ω = 0 := by
  have hsum : ∀ (j' : ℕ) (p : Fin j' → Bool),
      coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j' p true
        + coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j' p false = 1 := by
    intro j' p
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  rw [sum_ghist_atom A BL BR CC κ
    (fun ω => RP A BL BR CC κ ε ω * sgX A BL BR CC κ ε j ω)
    (le_of_lt hj) ω₀]
  have hterm : ∀ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
      ∀ i : Fin κ, (i : ℕ) < j → c i = ω₀.2.2.2.2 i),
      RP A BL BR CC κ ε (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
        * sgX A BL BR CC κ ε j (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
      = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
        * (coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c
          * (if c ⟨j, hj⟩ then
              nextL A BL BR CC κ ω₀ j - sdrift A BL BR CC κ ε ω₀ j
             else
              nextR A BL BR CC κ ω₀ j - sdrift A BL BR CC κ ε ω₀ j)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have hnl : nextL A BL BR CC κ
        (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
        = nextL A BL BR CC κ ω₀ j :=
      nextL_congr A BL BR CC κ _ ω₀ rfl hc.2
    have hnr : nextR A BL BR CC κ
        (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
        = nextR A BL BR CC κ ω₀ j :=
      nextR_congr A BL BR CC κ _ ω₀ rfl hc.2
    have hd : sdrift A BL BR CC κ ε
        (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
        = sdrift A BL BR CC κ ε ω₀ j :=
      sdrift_congr A BL BR CC κ ε _ ω₀ rfl rfl hc.2
    have hmgx : sgX A BL BR CC κ ε j
        (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
        = (if c ⟨j, hj⟩ then nextL A BL BR CC κ ω₀ j
           else nextR A BL BR CC κ ω₀ j)
          - sdrift A BL BR CC κ ε ω₀ j := by
      unfold sgX
      rw [dif_pos hj]
      show (if c ⟨j, hj⟩ then
          nextL A BL BR CC κ (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
        else
          nextR A BL BR CC κ (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j)
          - sdrift A BL BR CC κ ε
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j = _
      rw [hnl, hnr, hd]
    show A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * (CC.P ω₀.2.2.2.1
        * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c)))
        * sgX A BL BR CC κ ε j
            (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) = _
    rw [hmgx]
    by_cases hb : c ⟨j, hj⟩
    · rw [if_pos hb, if_pos hb]
      ring
    · rw [if_neg hb, if_neg hb]
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    coinWt_cond_step hsum hj ω₀.2.2.2.2
      (nextL A BL BR CC κ ω₀ j - sdrift A BL BR CC κ ε ω₀ j)
      (nextR A BL BR CC κ ω₀ j - sdrift A BL BR CC κ ε ω₀ j)]
  have hWt : coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
      (restrict ω₀.2.2.2.2 j (le_of_lt hj)) true
      = probL (nextL A BL BR CC κ ω₀ j) (nextR A BL BR CC κ ω₀ j) ε := by
    show probL
        (BL.sizeN (cntL (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j) ω₀.2.1)
        (BR.sizeN (cntR (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j)
          ω₀.2.2.1) ε = _
    rw [cntL_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j),
      cntR_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j)]
    rfl
  have hWf : coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
      (restrict ω₀.2.2.2.2 j (le_of_lt hj)) false
      = probL (nextR A BL BR CC κ ω₀ j) (nextL A BL BR CC κ ω₀ j) ε := by
    show probL
        (BR.sizeN (cntR (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j)
          ω₀.2.2.1)
        (BL.sizeN (cntL (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j) ω₀.2.1)
        ε = _
    rw [cntL_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j),
      cntR_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j)]
    rfl
  rw [hWt, hWf]
  have hprob := probL_add_probR (nextL A BL BR CC κ ω₀ j)
    (nextR A BL BR CC κ ω₀ j) ε hε
  have hD : probL (nextL A BL BR CC κ ω₀ j) (nextR A BL BR CC κ ω₀ j) ε
        * nextL A BL BR CC κ ω₀ j
      + probL (nextR A BL BR CC κ ω₀ j) (nextL A BL BR CC κ ω₀ j) ε
        * nextR A BL BR CC κ ω₀ j
      = sdrift A BL BR CC κ ε ω₀ j := rfl
  linear_combination
    ((A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
      * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
          (restrict ω₀.2.2.2.2 j (le_of_lt hj))) * hD
    + (-((A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
        * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
            (restrict ω₀.2.2.2.2 j (le_of_lt hj))
        * sdrift A BL BR CC κ ε ω₀ j)) * hprob

/-- Conditional second-moment identity on every atom. -/
theorem race_hvar_sum (hε : 0 < ε) {j : ℕ} (hj : j < κ)
    (ω₀ : RΩ A BL BR CC κ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀),
      RP A BL BR CC κ ε ω * (sgX A BL BR CC κ ε j ω) ^ 2
      = sgV A BL BR CC κ ε j ω₀
        * ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
            ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀),
          RP A BL BR CC κ ε ω := by
  have hsum : ∀ (j' : ℕ) (p : Fin j' → Bool),
      coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j' p true
        + coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j' p false = 1 := by
    intro j' p
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  have hWt : coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
      (restrict ω₀.2.2.2.2 j (le_of_lt hj)) true
      = probL (nextL A BL BR CC κ ω₀ j) (nextR A BL BR CC κ ω₀ j) ε := by
    show probL
        (BL.sizeN (cntL (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j) ω₀.2.1)
        (BR.sizeN (cntR (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j)
          ω₀.2.2.1) ε = _
    rw [cntL_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j),
      cntR_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j)]
    rfl
  have hWf : coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
      (restrict ω₀.2.2.2.2 j (le_of_lt hj)) false
      = probL (nextR A BL BR CC κ ω₀ j) (nextL A BL BR CC κ ω₀ j) ε := by
    show probL
        (BR.sizeN (cntR (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j)
          ω₀.2.2.1)
        (BL.sizeN (cntL (restrict ω₀.2.2.2.2 j (le_of_lt hj)) j) ω₀.2.1)
        ε = _
    rw [cntL_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j),
      cntR_restrict ω₀.2.2.2.2 (le_of_lt hj) (le_refl j)]
    rfl
  have hL : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀),
      RP A BL BR CC κ ε ω * (sgX A BL BR CC κ ε j ω) ^ 2
      = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
        * (coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
            (restrict ω₀.2.2.2.2 j (le_of_lt hj))
          * (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
                (restrict ω₀.2.2.2.2 j (le_of_lt hj)) true
              * (nextL A BL BR CC κ ω₀ j
                  - sdrift A BL BR CC κ ε ω₀ j) ^ 2
            + coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
                (restrict ω₀.2.2.2.2 j (le_of_lt hj)) false
              * (nextR A BL BR CC κ ω₀ j
                  - sdrift A BL BR CC κ ε ω₀ j) ^ 2)) := by
    rw [sum_ghist_atom A BL BR CC κ
      (fun ω => RP A BL BR CC κ ε ω * (sgX A BL BR CC κ ε j ω) ^ 2)
      (le_of_lt hj) ω₀]
    have hterm : ∀ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
        ∀ i : Fin κ, (i : ℕ) < j → c i = ω₀.2.2.2.2 i),
        RP A BL BR CC κ ε (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
          * (sgX A BL BR CC κ ε j
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)) ^ 2
        = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
          * (coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c
            * (if c ⟨j, hj⟩ then
                (nextL A BL BR CC κ ω₀ j
                  - sdrift A BL BR CC κ ε ω₀ j) ^ 2
               else
                (nextR A BL BR CC κ ω₀ j
                  - sdrift A BL BR CC κ ε ω₀ j) ^ 2)) := by
      intro c hc
      rw [Finset.mem_filter] at hc
      have hnl : nextL A BL BR CC κ
          (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
          = nextL A BL BR CC κ ω₀ j :=
        nextL_congr A BL BR CC κ _ ω₀ rfl hc.2
      have hnr : nextR A BL BR CC κ
          (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
          = nextR A BL BR CC κ ω₀ j :=
        nextR_congr A BL BR CC κ _ ω₀ rfl hc.2
      have hd : sdrift A BL BR CC κ ε
          (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
          = sdrift A BL BR CC κ ε ω₀ j :=
        sdrift_congr A BL BR CC κ ε _ ω₀ rfl rfl hc.2
      have hmgx : sgX A BL BR CC κ ε j
          (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
          = (if c ⟨j, hj⟩ then nextL A BL BR CC κ ω₀ j
             else nextR A BL BR CC κ ω₀ j)
            - sdrift A BL BR CC κ ε ω₀ j := by
        unfold sgX
        rw [dif_pos hj]
        show (if c ⟨j, hj⟩ then
            nextL A BL BR CC κ (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
          else
            nextR A BL BR CC κ
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j)
            - sdrift A BL BR CC κ ε
                (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j = _
        rw [hnl, hnr, hd]
      show A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * (CC.P ω₀.2.2.2.1
          * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c)))
          * (sgX A BL BR CC κ ε j
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)) ^ 2 = _
      rw [hmgx]
      by_cases hb : c ⟨j, hj⟩
      · rw [if_pos hb, if_pos hb]
        ring
      · rw [if_neg hb, if_neg hb]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      coinWt_cond_step hsum hj ω₀.2.2.2.2
        ((nextL A BL BR CC κ ω₀ j - sdrift A BL BR CC κ ε ω₀ j) ^ 2)
        ((nextR A BL BR CC κ ω₀ j - sdrift A BL BR CC κ ε ω₀ j) ^ 2)]
  have hM : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀),
      RP A BL BR CC κ ε ω
      = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
        * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
            (restrict ω₀.2.2.2.2 j (le_of_lt hj)) := by
    rw [sum_ghist_atom A BL BR CC κ (fun ω => RP A BL BR CC κ ε ω)
      (le_of_lt hj) ω₀]
    have hterm2 : ∀ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
        ∀ i : Fin κ, (i : ℕ) < j → c i = ω₀.2.2.2.2 i),
        RP A BL BR CC κ ε (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
        = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
          * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c := by
      intro c _
      show A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * (CC.P ω₀.2.2.2.1
          * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c))) = _
      ring
    rw [Finset.sum_congr rfl hterm2, ← Finset.mul_sum,
      sum_coinWt_restrict hsum (le_of_lt hj) ω₀.2.2.2.2]
  rw [hL, hM]
  unfold sgV
  rw [if_pos hj, hWt, hWf]
  ring

/-- The imbalance increments form a discrete martingale for the
full-reveal filtration, with conditional second moments `sgV`. -/
theorem race_martingale_sum (hε : 0 < ε) :
    IsDiscreteMartingale (RP A BL BR CC κ ε) κ (ghist A BL BR CC κ)
      (sgX A BL BR CC κ ε) (sgV A BL BR CC κ ε) := by
  refine ⟨fun ω => (RP_pos A BL BR CC κ ε hε ω).le, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij ω ω' h
    rw [ghist_iff] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h1, h2, h3, h4, ?_⟩
    exact coinCode_congr fun i' hi' => coinCode_inj h5 i'
      (lt_of_lt_of_le hi' (min_le_min hij (le_refl κ)))
  · intro j hjN ω ω' h
    rw [ghist_iff] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [min_eq_left (by omega : j + 1 ≤ κ)] at h5
    have hcoins : ∀ i : Fin κ, (i : ℕ) < j + 1
        → ω.2.2.2.2 i = ω'.2.2.2.2 i := coinCode_inj h5
    unfold sgX
    rw [dif_pos hjN, dif_pos hjN,
      nextL_congr A BL BR CC κ ω ω' h2 (fun i hi => hcoins i (by omega)),
      nextR_congr A BL BR CC κ ω ω' h3 (fun i hi => hcoins i (by omega)),
      sdrift_congr A BL BR CC κ ε ω ω' h2 h3
        (fun i hi => hcoins i (by omega)),
      hcoins ⟨j, hjN⟩ (Nat.lt_succ_self j)]
  · intro j hjN ω ω' h
    rw [ghist_iff] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [min_eq_left (by omega : j ≤ κ)] at h5
    have hcoins : ∀ i : Fin κ, (i : ℕ) < j
        → ω.2.2.2.2 i = ω'.2.2.2.2 i := coinCode_inj h5
    unfold sgV
    rw [if_pos hjN, if_pos hjN,
      nextL_congr A BL BR CC κ ω ω' h2 hcoins,
      nextR_congr A BL BR CC κ ω ω' h3 hcoins,
      sdrift_congr A BL BR CC κ ε ω ω' h2 h3 hcoins]
  · exact fun j hjN ω₀ => race_hmart_sum A BL BR CC κ ε hε hjN ω₀
  · exact fun j hjN ω₀ => race_hvar_sum A BL BR CC κ ε hε hjN ω₀

theorem sgX_abs_le (hε : 0 < ε) (hcB : 0 ≤ cB) (j : ℕ)
    (ω : RΩ A BL BR CC κ) :
    |sgX A BL BR CC κ ε j ω| ≤ cB + ε := by
  unfold sgX
  by_cases hj : j < κ
  · rw [dif_pos hj]
    obtain ⟨hd0, hdB⟩ := sdrift_bounds A BL BR CC κ ε hε hcB ω j
    have hnl0 : (0 : ℝ) ≤ nextL A BL BR CC κ ω j :=
      BL.sizeN_nonneg (le_refl 0) _ _
    have hnlB : nextL A BL BR CC κ ω j ≤ cB :=
      sizeN_le_cB BL hcB (cntL ω.2.2.2.2 j) ω.2.1
    have hnr0 : (0 : ℝ) ≤ nextR A BL BR CC κ ω j :=
      BR.sizeN_nonneg (le_refl 0) _ _
    have hnrB : nextR A BL BR CC κ ω j ≤ cB :=
      sizeN_le_cB BR hcB (cntR ω.2.2.2.2 j) ω.2.2.1
    by_cases hb : ω.2.2.2.2 ⟨j, hj⟩
    · rw [if_pos hb, abs_le]
      constructor <;> linarith [hε.le]
    · rw [if_neg hb, abs_le]
      constructor <;> linarith [hε.le]
  · rw [dif_neg hj, abs_zero]
    linarith [hε.le]

theorem sgV_nonneg (hε : 0 < ε) (j : ℕ) (ω : RΩ A BL BR CC κ) :
    0 ≤ sgV A BL BR CC κ ε j ω := by
  unfold sgV
  by_cases hj : j < κ
  · rw [if_pos hj]
    exact add_nonneg (mul_nonneg (probL_pos hε).le (sq_nonneg _))
      (mul_nonneg (probL_pos hε).le (sq_nonneg _))
  · rw [if_neg hj]

theorem sgV_le (hε : 0 < ε) (hcB : 0 ≤ cB) (j : ℕ)
    (ω : RΩ A BL BR CC κ) :
    sgV A BL BR CC κ ε j ω ≤ (cB + ε) ^ 2 := by
  unfold sgV
  by_cases hj : j < κ
  · rw [if_pos hj]
    obtain ⟨hd0, hdB⟩ := sdrift_bounds A BL BR CC κ ε hε hcB ω j
    have hnl0 : (0 : ℝ) ≤ nextL A BL BR CC κ ω j :=
      BL.sizeN_nonneg (le_refl 0) _ _
    have hnlB : nextL A BL BR CC κ ω j ≤ cB :=
      sizeN_le_cB BL hcB (cntL ω.2.2.2.2 j) ω.2.1
    have hnr0 : (0 : ℝ) ≤ nextR A BL BR CC κ ω j :=
      BR.sizeN_nonneg (le_refl 0) _ _
    have hnrB : nextR A BL BR CC κ ω j ≤ cB :=
      sizeN_le_cB BR hcB (cntR ω.2.2.2.2 j) ω.2.2.1
    have h1 : (nextL A BL BR CC κ ω j - sdrift A BL BR CC κ ε ω j) ^ 2
        ≤ (cB + ε) ^ 2 :=
      sq_le_sq' (by linarith [hε.le]) (by linarith [hε.le])
    have h2 : (nextR A BL BR CC κ ω j - sdrift A BL BR CC κ ε ω j) ^ 2
        ≤ (cB + ε) ^ 2 :=
      sq_le_sq' (by linarith [hε.le]) (by linarith [hε.le])
    have hp := probL_add_probR (nextL A BL BR CC κ ω j)
      (nextR A BL BR CC κ ω j) ε hε
    calc probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
          * (nextL A BL BR CC κ ω j - sdrift A BL BR CC κ ε ω j) ^ 2
        + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
          * (nextR A BL BR CC κ ω j - sdrift A BL BR CC κ ε ω j) ^ 2
        ≤ probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
            * (cB + ε) ^ 2
          + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
            * (cB + ε) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (probL_pos hε).le)
            (mul_le_mul_of_nonneg_left h2 (probL_pos hε).le)
      _ = (cB + ε) ^ 2 := by rw [← add_mul, hp, one_mul]
  · rw [if_neg hj]
    positivity

/-- Total conditional variance bounds. -/
theorem sgV_total_le (hε : 0 < ε) (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    ∑ j ∈ Finset.range κ, sgV A BL BR CC κ ε j ω
      ≤ (κ : ℝ) * (cB + ε) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun j _ =>
    sgV_le A BL BR CC κ ε hε hcB j ω) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The consumption martingale sum is the consumed mass minus the
accumulated conditional rates. -/
theorem race_sgSum_eq (ω : RΩ A BL BR CC κ) :
    mgSum (sgX A BL BR CC κ ε) κ ω
      = (sumL A BL BR CC κ ω + sumR A BL BR CC κ ω)
        - ∑ j ∈ Finset.range κ, sdrift A BL BR CC κ ε ω j := by
  unfold mgSum
  have h1 : ∀ j : Fin κ, sgX A BL BR CC κ ε (j : ℕ) ω
      = (if ω.2.2.2.2 j then nextL A BL BR CC κ ω (j : ℕ)
         else nextR A BL BR CC κ ω (j : ℕ))
        - sdrift A BL BR CC κ ε ω (j : ℕ) := by
    intro j
    unfold sgX
    rw [dif_pos j.isLt]
  rw [← Fin.sum_univ_eq_sum_range (fun j => sgX A BL BR CC κ ε j ω) κ,
    Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib]
  congr 1
  · unfold sumL sumR
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hb : ω.2.2.2.2 j
    · rw [if_pos hb, if_pos hb, if_pos hb]
      ring
    · rw [if_neg hb, if_neg hb, if_neg hb]
      ring
  · exact Fin.sum_univ_eq_sum_range
      (fun j => sdrift A BL BR CC κ ε ω j) κ
end GainSum

end Race

end KServer


