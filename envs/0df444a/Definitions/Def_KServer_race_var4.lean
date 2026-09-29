-- Prove2me | Definitions.Def_KServer_race_var4
-- name    : KServer_race_var4
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T23:07:13.274581+00:00
-- url     : https://prove2.me/theorems/ecf65032-f939-40e0-95e3-272c03bbf11c
-- title:
--   Martingale-form race variance
-- statement:
--   The sharp variance bound for the race total: the middle block equals the selected side's total plus half the imbalance, minus half the consumption martingale, minus a residual bounded in [-(kappa epsilon/2 + c_B), 0]. Using the second moments of the imbalance and consumption martingales (both at kappa (c_B+epsilon)^2 scale), the variance of the race total is at most VA + 3V + 2VC plus kappa (c_B+epsilon)^2-scale terms, with no (kappa c_B)^2 range term. This is the variance form whose Chebyshev consequences survive the level recursion. Includes the closed forms of the survivor tail, consumed prefix, coin terms, and the residual.
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
import Definitions.Def_KServer_race_var3
import Definitions.Def_KServer_race_sel
import Definitions.Def_KServer_discrete_martingale
import Definitions.Def_KServer_race_gain
import Definitions.Def_KServer_race_gainsum
import Definitions.Def_KServer_second_moment

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Var4

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- The consumed prefix of the surviving side, one chunk past the coin
phase. -/
noncomputable def consPre (ω : RΩ A BL BR CC κ) : ℝ :=
  if survL A BL BR CC κ ω
  then preSum BL ω.2.1 (cntL ω.2.2.2.2 κ + 1)
  else preSum BR ω.2.2.1 (cntR ω.2.2.2.2 κ + 1)

/-- The survivor tail is the selected total minus the consumed prefix. -/
theorem survPart_eq (ω : RΩ A BL BR CC κ) :
    survPart A BL BR CC κ ω
      = selTot A BL BR CC κ ω - consPre A BL BR CC κ ω := by
  unfold survPart selTot consPre
  by_cases hs : survL A BL BR CC κ ω = true
  · rw [if_pos hs, if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs, if_neg hs]

/-- The consumed prefix exceeds the consumed minimum by at most one
chunk. -/
theorem consPre_bounds (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω)
        ≤ consPre A BL BR CC κ ω
      ∧ consPre A BL BR CC κ ω
        ≤ min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω) + cB := by
  cases hs : survL A BL BR CC κ ω with
  | true =>
    have hle := (survL_true_iff A BL BR CC κ ω).mp hs
    unfold consPre
    rw [if_pos hs, preSum_succ, ← sumL_eq_preSum κ A BL BR CC ω,
      min_eq_left hle]
    constructor
    · linarith [BL.sizeN_nonneg (le_refl 0) (cntL ω.2.2.2.2 κ) ω.2.1]
    · linarith [sizeN_le_cB BL hcB (cntL ω.2.2.2.2 κ) ω.2.1]
  | false =>
    have hle := survL_false_le A BL BR CC κ ω hs
    unfold consPre
    rw [if_neg (by simp [hs]), preSum_succ,
      ← sumR_eq_preSum κ A BL BR CC ω, min_eq_right hle]
    constructor
    · linarith [BR.sizeN_nonneg (le_refl 0) (cntR ω.2.2.2.2 κ) ω.2.2.1]
    · linarith [sizeN_le_cB BR hcB (cntR ω.2.2.2.2 κ) ω.2.2.1]

/-- Each coin term is the conditional consumption rate over two, minus
half the absolute drift. -/
theorem coinTerm_eq_sdrift (ω : RΩ A BL BR CC κ) (j : ℕ) :
    coinTerm A BL BR CC κ ε ω j
      = sdrift A BL BR CC κ ε ω j / 2
        - |gdrift A BL BR CC κ ε ω j| / 2 := by
  unfold coinTerm
  rw [min_eq_avg]
  show (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
        * nextL A BL BR CC κ ω j
      + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
        * nextR A BL BR CC κ ω j) / 2
    - |probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
          * nextL A BL BR CC κ ω j
        - probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
          * nextR A BL BR CC κ ω j| / 2 = _
  rfl

/-- The residual of the middle block after the selected total, the
consumption martingale, and the imbalance are removed. -/
noncomputable def gRes (ω : RΩ A BL BR CC κ) : ℝ :=
  gBlock A BL BR CC κ ε ω - selTot A BL BR CC κ ω
    + mgSum (sgX A BL BR CC κ ε) κ ω / 2
    - |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2

/-- The residual in closed form: minus half the accumulated absolute
drift, minus the sacrificed chunk. -/
theorem gRes_eq (ω : RΩ A BL BR CC κ) :
    gRes A BL BR CC κ ε ω
      = -(∑ j ∈ Finset.range κ, |gdrift A BL BR CC κ ε ω j| / 2)
        - (consPre A BL BR CC κ ω
            - min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω)) := by
  unfold gRes gBlock
  rw [race_sgSum_eq A BL BR CC κ ε ω, survPart_eq A BL BR CC κ ω,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.range κ) =>
      coinTerm_eq_sdrift A BL BR CC κ ε ω j,
    min_eq_avg (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω),
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  ring

/-- The residual lies in `[-(κ·ε/2 + c_B), 0]`. -/
theorem gRes_bounds (hε : 0 < ε) (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    -((κ : ℝ) * ε / 2 + cB) ≤ gRes A BL BR CC κ ε ω
      ∧ gRes A BL BR CC κ ε ω ≤ 0 := by
  rw [gRes_eq A BL BR CC κ ε ω]
  have hd0 : 0 ≤ ∑ j ∈ Finset.range κ, |gdrift A BL BR CC κ ε ω j| / 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have hdK : ∑ j ∈ Finset.range κ, |gdrift A BL BR CC κ ε ω j| / 2
      ≤ (κ : ℝ) * ε / 2 := by
    have h1 : ∀ j ∈ Finset.range κ,
        |gdrift A BL BR CC κ ε ω j| / 2 ≤ ε / 2 := by
      intro j _
      have h2 := gdrift_abs_le A BL BR CC κ ε hε ω j
      linarith
    refine le_trans (Finset.sum_le_sum h1) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  obtain ⟨hc1, hc2⟩ := consPre_bounds A BL BR CC κ hcB ω
  constructor
  · linarith
  · linarith

open Classical in
/-- Second moment of the consumption martingale. -/
theorem race_sgSum_sq (hε : 0 < ε) (hcB : 0 ≤ cB) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2
      ≤ (κ : ℝ) * (cB + ε) ^ 2 := by
  haveI := Classical.decEq (RΩ A BL BR CC κ)
  rw [martingale_second_moment_eq
    (race_martingale_sum A BL BR CC κ ε hε)]
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  refine le_trans (Finset.sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left
      (sgV_total_le A BL BR CC κ ε hε hcB ω)
      (RP_pos A BL BR CC κ ε hε ω).le) (le_of_eq ?_)
  exact sum_P_mul (RP A BL BR CC κ ε) hRPs ((κ : ℝ) * (cB + ε) ^ 2)
    (fun ω => RP A BL BR CC κ ε ω * ((κ : ℝ) * (cB + ε) ^ 2))
    (fun ω => by ring)

open Classical in
/-- Second moment of the imbalance martingale. -/
theorem race_mgSum_sq (hε : 0 < ε) (hcB : 0 ≤ cB) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (mgSum (mgX A BL BR CC κ ε) κ ω) ^ 2
      ≤ (κ : ℝ) * (cB + ε) ^ 2 := by
  haveI := Classical.decEq (RΩ A BL BR CC κ)
  rw [martingale_second_moment_eq (race_martingale A BL BR CC κ ε hε)]
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  refine le_trans (Finset.sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left
      (mgV_total_le A BL BR CC κ ε hε hcB ω)
      (RP_pos A BL BR CC κ ε hε ω).le) (le_of_eq ?_)
  exact sum_P_mul (RP A BL BR CC κ ε) hRPs ((κ : ℝ) * (cB + ε) ^ 2)
    (fun ω => RP A BL BR CC κ ε ω * ((κ : ℝ) * (cB + ε) ^ 2))
    (fun ω => by ring)

/-- Second moment of the imbalance itself. -/
theorem race_imb_sq (hε : 0 < ε) (hcB : 0 ≤ cB) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2
      ≤ 2 * ((κ : ℝ) * (cB + ε) ^ 2) + 2 * ((κ : ℝ) * ε) ^ 2 := by
  have hpt : ∀ ω : RΩ A BL BR CC κ,
      (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2
      ≤ 2 * (mgSum (mgX A BL BR CC κ ε) κ ω) ^ 2
        + 2 * ((κ : ℝ) * ε) ^ 2 := by
    intro ω
    have hid := race_mgSum_eq A BL BR CC κ ε ω
    have hdr : |∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j|
        ≤ (κ : ℝ) * ε := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum fun j _ =>
        gdrift_abs_le A BL BR CC κ ε hε ω j) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hκε : (0 : ℝ) ≤ (κ : ℝ) * ε :=
      mul_nonneg (Nat.cast_nonneg κ) hε.le
    rw [abs_le] at hdr
    have hdr2 : (∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j) ^ 2
        ≤ ((κ : ℝ) * ε) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    have hΔ : sumL A BL BR CC κ ω - sumR A BL BR CC κ ω
        = mgSum (mgX A BL BR CC κ ε) κ ω
          + ∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j := by
      linarith [hid]
    rw [hΔ]
    nlinarith [sq_nonneg (mgSum (mgX A BL BR CC κ ε) κ ω
      - ∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j), hdr2]
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (2 * (mgSum (mgX A BL BR CC κ ε) κ ω) ^ 2
            + 2 * ((κ : ℝ) * ε) ^ 2) :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω)
      (RP_pos A BL BR CC κ ε hε ω).le
  refine le_trans h1 ?_
  rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ Finset.univ) =>
    show RP A BL BR CC κ ε ω
        * (2 * (mgSum (mgX A BL BR CC κ ε) κ ω) ^ 2
          + 2 * ((κ : ℝ) * ε) ^ 2)
      = 2 * (RP A BL BR CC κ ε ω
          * (mgSum (mgX A BL BR CC κ ε) κ ω) ^ 2)
        + (2 * ((κ : ℝ) * ε) ^ 2) * RP A BL BR CC κ ε ω
      from by ring),
    Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_P_mul (RP A BL BR CC κ ε) hRPs (2 * ((κ : ℝ) * ε) ^ 2)
      (fun ω => 2 * ((κ : ℝ) * ε) ^ 2 * RP A BL BR CC κ ε ω)
      (fun ω => by ring)]
  have h2 := race_mgSum_sq A BL BR CC κ ε hε hcB
  linarith

theorem race_var4 (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {VA V VC : ℝ} (hV0 : 0 ≤ V)
    (hmean : ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i
      = ∑ r : BR.Ω, BR.P r * ∑ i, BR.size r i)
    (hVarA : ∑ a : A.Ω, A.P a * ((∑ i, A.size a i)
        - ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i) ^ 2 ≤ VA)
    (hVarL : ∑ l : BL.Ω, BL.P l * ((∑ i, BL.size l i)
        - ∑ l' : BL.Ω, BL.P l' * ∑ i, BL.size l' i) ^ 2 ≤ V)
    (hVarR : ∑ r : BR.Ω, BR.P r * ((∑ i, BR.size r i)
        - ∑ r' : BR.Ω, BR.P r' * ∑ i, BR.size r' i) ^ 2 ≤ V)
    (hVarC : ∑ cc : CC.Ω, CC.P cc * ((∑ i, CC.size cc i)
        - ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i) ^ 2 ≤ VC) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω (i : ℕ))
          - ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
              * ∑ i : Fin (mrace A BL BR CC κ),
                  rsize A BL BR CC κ ε ω' (i : ℕ)) ^ 2
      ≤ VA + 3 * V + 2 * VC + 8 * (κ : ℝ) * (cB + ε) ^ 2
        + 5 * ((κ : ℝ) * ε) ^ 2 + 10 * ((κ : ℝ) * ε / 2 + cB) ^ 2
        + 2 * cB ^ 2 := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  set mA := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * preSum A ω.1 A.m with hmA
  set mG := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * gBlock A BL BR CC κ ε ω with hmG
  set mC := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * ccPart A BL BR CC κ ω with hmC
  have hmeantot : ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω' (i : ℕ)
      = mA + mG + mC := by
    rw [hmA, hmG, hmC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    unfold gBlock
    ring
  rw [hmeantot]
  -- centering identities
  have hf0 : ∑ a : A.Ω, A.P a * (preSum A a A.m - mA) = 0 := by
    have h1 : mA = ∑ a : A.Ω, A.P a * preSum A a A.m := by
      rw [hmA]
      exact RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)
    rw [sum_mul_sub A.P (fun a => preSum A a A.m) (fun _ => mA),
      sum_P_mul A.P A.hPsum mA (fun a => A.P a * mA) (fun a => by ring),
      ← h1, sub_self]
  have hh0 : ∑ cc : CC.Ω, CC.P cc
      * ((preSum CC cc CC.m - preSum CC cc 1) - mC) = 0 := by
    have h1 : mC = ∑ cc : CC.Ω, CC.P cc
        * (preSum CC cc CC.m - preSum CC cc 1) := by
      rw [hmC]
      exact RP_margC A BL BR CC κ ε hε
        (fun cc => preSum CC cc CC.m - preSum CC cc 1)
    rw [sum_mul_sub CC.P
        (fun cc => preSum CC cc CC.m - preSum CC cc 1) (fun _ => mC),
      sum_P_mul CC.P CC.hPsum mC (fun cc => CC.P cc * mC)
        (fun cc => by ring),
      ← h1, sub_self]
  have hgcong : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc cc' : CC.Ω)
      (χ : Fin κ → Bool),
      gBlock A BL BR CC κ ε (a, l, r, cc, χ) - mG
        = gBlock A BL BR CC κ ε (a', l, r, cc', χ) - mG := by
    intro a a' l r cc cc' χ
    rw [gBlock_congr A BL BR CC κ ε a a' l r cc cc' χ]
  -- vanishing cross terms
  have hPQ : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((preSum A ω.1 A.m - mA)
        * (gBlock A BL BR CC κ ε ω - mG)) = 0 :=
    RP_cross_zero_A A BL BR CC κ ε hε
      (fun a => preSum A a A.m - mA)
      (fun ω => gBlock A BL BR CC κ ε ω - mG) hgcong hf0
  have hPR : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((preSum A ω.1 A.m - mA)
        * (ccPart A BL BR CC κ ω - mC)) = 0 :=
    RP_cross_zero_AC A BL BR CC κ ε hε
      (fun a => preSum A a A.m - mA)
      (fun cc => (preSum CC cc CC.m - preSum CC cc 1) - mC) hf0
  have hQR : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((gBlock A BL BR CC κ ε ω - mG)
        * (ccPart A BL BR CC κ ω - mC)) = 0 :=
    RP_cross_zero_C A BL BR CC κ ε hε
      (fun ω => gBlock A BL BR CC κ ε ω - mG)
      (fun cc => (preSum CC cc CC.m - preSum CC cc 1) - mC) hgcong hh0
  -- head block
  have hEA : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (preSum A ω.1 A.m - mA) ^ 2 ≤ VA := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (preSum A ω.1 A.m - mA) ^ 2
        = ∑ a : A.Ω, A.P a * (preSum A a A.m - mA) ^ 2 :=
      RP_margA A BL BR CC κ ε hε (fun a => (preSum A a A.m - mA) ^ 2)
    have hmeanA : ∑ a' : A.Ω, A.P a' * preSum A a' A.m
        = ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i :=
      Finset.sum_congr rfl fun a' _ => by rw [preSum_total]
    have h2 : mA = ∑ a' : A.Ω, A.P a' * preSum A a' A.m := by
      rw [hmA]
      exact RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)
    rw [h1]
    refine le_trans (le_of_eq ?_) hVarA
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [preSum_total, h2, hmeanA]
  -- closing block
  have hEC : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (ccPart A BL BR CC κ ω - mC) ^ 2 ≤ 2 * VC + 2 * cB ^ 2 := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (ccPart A BL BR CC κ ω - mC) ^ 2
        = ∑ cc : CC.Ω, CC.P cc
            * ((preSum CC cc CC.m - preSum CC cc 1) - mC) ^ 2 :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => ((preSum CC cc CC.m - preSum CC cc 1) - mC) ^ 2)
    have h2a : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ccPart A BL BR CC κ ω
        = ∑ cc : CC.Ω, CC.P cc
            * (preSum CC cc CC.m - preSum CC cc 1) :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => preSum CC cc CC.m - preSum CC cc 1)
    have h2 : mC = (∑ cc : CC.Ω, CC.P cc * preSum CC cc CC.m)
        - ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 := by
      rw [hmC, h2a, sum_mul_sub]
    have hp0 : ∀ cc : CC.Ω, 0 ≤ preSum CC cc 1 :=
      fun cc => preSum_nonneg CC cc 1
    have hpB : ∀ cc : CC.Ω, preSum CC cc 1 ≤ cB := by
      intro cc
      have h5 : preSum CC cc 1 = CC.sizeN 0 cc := by
        unfold preSum
        rw [Finset.sum_range_one]
      rw [h5]
      exact sizeN_le_cB CC hcB 0 cc
    have hμ0 : 0 ≤ ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 :=
      Finset.sum_nonneg fun cc _ => mul_nonneg (CC.hP cc).le (hp0 cc)
    have hμB : ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 ≤ cB := by
      refine le_trans (Finset.sum_le_sum fun cc _ =>
        mul_le_mul_of_nonneg_left (hpB cc) (CC.hP cc).le) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum cB (fun cc => CC.P cc * cB)
        (fun cc => by ring)
    have hb1 : ∀ cc : CC.Ω,
        ((preSum CC cc CC.m - preSum CC cc 1) - mC) ^ 2
          ≤ 2 * (preSum CC cc CC.m
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
            + 2 * (preSum CC cc 1
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2 := by
      intro cc
      rw [h2]
      nlinarith [sq_nonneg ((preSum CC cc CC.m
          - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m)
        + (preSum CC cc 1
          - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1))]
    rw [h1]
    refine le_trans (Finset.sum_le_sum fun cc _ =>
      mul_le_mul_of_nonneg_left (hb1 cc) (CC.hP cc).le) ?_
    have hsplit2 : ∑ cc : CC.Ω, CC.P cc
        * (2 * (preSum CC cc CC.m
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
          + 2 * (preSum CC cc 1
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
        = 2 * (∑ cc : CC.Ω, CC.P cc * (preSum CC cc CC.m
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2)
          + 2 * (∑ cc : CC.Ω, CC.P cc * (preSum CC cc 1
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2) := by
      rw [Finset.sum_congr rfl (fun cc _ =>
        show CC.P cc
            * (2 * (preSum CC cc CC.m
                - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
              + 2 * (preSum CC cc 1
                - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
          = 2 * (CC.P cc * (preSum CC cc CC.m
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2)
            + 2 * (CC.P cc * (preSum CC cc 1
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
          from by ring),
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsplit2]
    have hmeanC : ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m
        = ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i :=
      Finset.sum_congr rfl fun cc' _ => by rw [preSum_total]
    have hVt : ∑ cc : CC.Ω, CC.P cc * (preSum CC cc CC.m
        - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2 ≤ VC := by
      refine le_trans (le_of_eq ?_) hVarC
      refine Finset.sum_congr rfl fun cc _ => ?_
      rw [preSum_total, hmeanC]
    have hVp : ∑ cc : CC.Ω, CC.P cc * (preSum CC cc 1
        - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2 ≤ cB ^ 2 := by
      refine le_trans (Finset.sum_le_sum fun cc _ =>
        mul_le_mul_of_nonneg_left
          (sq_le_sq' (b := cB) (by linarith [hp0 cc, hμB])
            (by linarith [hpB cc, hμ0]))
          (CC.hP cc).le) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum (cB ^ 2)
        (fun cc => CC.P cc * cB ^ 2) (fun cc => by ring)
    linarith
  -- middle block via the martingales
  have hEG : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (gBlock A BL BR CC κ ε ω - mG) ^ 2
      ≤ 3 * V + 8 * (κ : ℝ) * (cB + ε) ^ 2 + 5 * ((κ : ℝ) * ε) ^ 2
        + 10 * ((κ : ℝ) * ε / 2 + cB) ^ 2 := by
    set μ := ∑ l : BL.Ω, BL.P l * ∑ i, BL.size l i with hμ
    have hpath2 : ∀ ω : RΩ A BL BR CC κ,
        (selTot A BL BR CC κ ω - μ) ^ 2
          ≤ (preSum BL ω.2.1 BL.m - μ) ^ 2
            + (preSum BR ω.2.2.1 BR.m - μ) ^ 2 := by
      intro ω
      unfold selTot
      split
      · nlinarith [sq_nonneg (preSum BR ω.2.2.1 BR.m - μ)]
      · nlinarith [sq_nonneg (preSum BL ω.2.1 BL.m - μ)]
    have hL : ∑ l : BL.Ω, BL.P l * (preSum BL l BL.m - μ) ^ 2 ≤ V := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
        hVarL
      rw [preSum_total]
    have hR : ∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2 ≤ V := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
        hVarR
      rw [preSum_total, hmean]
    have hsel2 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (selTot A BL BR CC κ ω - μ) ^ 2 ≤ 2 * V := by
      have h5 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (selTot A BL BR CC κ ω - μ) ^ 2
          ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * ((preSum BL ω.2.1 BL.m - μ) ^ 2
                + (preSum BR ω.2.2.1 BR.m - μ) ^ 2) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hpath2 ω) (hRP0 ω)
      have h6 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ((preSum BL ω.2.1 BL.m - μ) ^ 2
            + (preSum BR ω.2.2.1 BR.m - μ) ^ 2)
          = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
              * ((preSum BL l BL.m - μ) ^ 2
                + (preSum BR r BR.m - μ) ^ 2) :=
        RP_margLR A BL BR CC κ ε hε
          (fun l r => (preSum BL l BL.m - μ) ^ 2
            + (preSum BR r BR.m - μ) ^ 2)
      have hrow : ∀ l : BL.Ω,
          ∑ r : BR.Ω, BL.P l * BR.P r
            * ((preSum BL l BL.m - μ) ^ 2
              + (preSum BR r BR.m - μ) ^ 2)
          = BL.P l * (preSum BL l BL.m - μ) ^ 2
            + BL.P l * (∑ r : BR.Ω, BR.P r
                * (preSum BR r BR.m - μ) ^ 2) := by
        intro l
        rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) =>
          show BL.P l * BR.P r
              * ((preSum BL l BL.m - μ) ^ 2
                + (preSum BR r BR.m - μ) ^ 2)
            = BL.P l * (preSum BL l BL.m - μ) ^ 2 * BR.P r
              + BL.P l * (BR.P r * (preSum BR r BR.m - μ) ^ 2)
            from by ring),
          Finset.sum_add_distrib]
        congr 1
        · exact sum_P_mul BR.P BR.hPsum
            (BL.P l * (preSum BL l BL.m - μ) ^ 2) _ (fun r => by ring)
        · rw [Finset.mul_sum]
      have h7 : ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
          * ((preSum BL l BL.m - μ) ^ 2 + (preSum BR r BR.m - μ) ^ 2)
          = (∑ l : BL.Ω, BL.P l * (preSum BL l BL.m - μ) ^ 2)
            + ∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2 := by
        rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hrow l,
          Finset.sum_add_distrib]
        congr 1
        exact sum_P_mul BL.P BL.hPsum
          (∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2) _
          (fun l => by ring)
      calc ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (selTot A BL BR CC κ ω - μ) ^ 2
          ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * ((preSum BL ω.2.1 BL.m - μ) ^ 2
                + (preSum BR ω.2.2.1 BR.m - μ) ^ 2) := h5
        _ = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
              * ((preSum BL l BL.m - μ) ^ 2
                + (preSum BR r BR.m - μ) ^ 2) := h6
        _ = (∑ l : BL.Ω, BL.P l * (preSum BL l BL.m - μ) ^ 2)
              + ∑ r : BR.Ω, BR.P r * (preSum BR r BR.m - μ) ^ 2 := h7
        _ ≤ 2 * V := by linarith
    have hz : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (gBlock A BL BR CC κ ε ω - mG) = 0 := by
      rw [sum_mul_sub (RP A BL BR CC κ ε)
          (fun ω => gBlock A BL BR CC κ ε ω) (fun _ => mG),
        sum_P_mul (RP A BL BR CC κ ε) hRPs mG
          (fun ω => RP A BL BR CC κ ε ω * mG) (fun ω => by ring),
        ← hmG, sub_self]
    have hshift : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (gBlock A BL BR CC κ ε ω - mG) ^ 2
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (gBlock A BL BR CC κ ε ω - μ) ^ 2 := by
      have hiden : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (gBlock A BL BR CC κ ε ω - μ) ^ 2
          = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * (gBlock A BL BR CC κ ε ω - mG) ^ 2)
            + (mG - μ) ^ 2 := by
        rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ Finset.univ) =>
          show RP A BL BR CC κ ε ω * (gBlock A BL BR CC κ ε ω - μ) ^ 2
            = RP A BL BR CC κ ε ω
                * (gBlock A BL BR CC κ ε ω - mG) ^ 2
              + 2 * (mG - μ) * (RP A BL BR CC κ ε ω
                  * (gBlock A BL BR CC κ ε ω - mG))
              + (mG - μ) ^ 2 * RP A BL BR CC κ ε ω
            from by ring),
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, hz, mul_zero, add_zero, ← Finset.mul_sum,
          hRPs, mul_one]
      linarith [sq_nonneg (mG - μ)]
    refine le_trans hshift ?_
    have hpath : ∀ ω : RΩ A BL BR CC κ,
        (gBlock A BL BR CC κ ε ω - μ) ^ 2
          ≤ (10 / 7) * (selTot A BL BR CC κ ω - μ) ^ 2
            + (5 / 2) * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2
            + (5 / 2) * (mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2
            + 10 * ((κ : ℝ) * ε / 2 + cB) ^ 2 := by
      intro ω
      have hgb : gBlock A BL BR CC κ ε ω - μ
          = (selTot A BL BR CC κ ω - μ)
            + (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2
              - mgSum (sgX A BL BR CC κ ε) κ ω / 2
              + gRes A BL BR CC κ ε ω) := by
        unfold gRes
        ring
      obtain ⟨hr1, hr2⟩ := gRes_bounds A BL BR CC κ ε hε hcB ω
      have hrn : (0 : ℝ) ≤ (κ : ℝ) * ε / 2 + cB := by
        have : (0 : ℝ) ≤ (κ : ℝ) * ε :=
          mul_nonneg (Nat.cast_nonneg κ) hε.le
        linarith
      have hrsq : (gRes A BL BR CC κ ε ω) ^ 2
          ≤ ((κ : ℝ) * ε / 2 + cB) ^ 2 :=
        sq_le_sq' (by linarith) (by linarith)
      have habs2 : |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| ^ 2
          = (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2 :=
        sq_abs _
      have hb2 : (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2
            - mgSum (sgX A BL BR CC κ ε) κ ω / 2
            + gRes A BL BR CC κ ε ω) ^ 2
          ≤ 3 * ((sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2 / 4)
            + 3 * ((mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2 / 4)
            + 3 * ((κ : ℝ) * ε / 2 + cB) ^ 2 := by
        nlinarith [sq_nonneg
            (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2
              + mgSum (sgX A BL BR CC κ ε) κ ω / 2),
          sq_nonneg (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2
              - gRes A BL BR CC κ ε ω),
          sq_nonneg (mgSum (sgX A BL BR CC κ ε) κ ω / 2
              + gRes A BL BR CC κ ε ω),
          hrsq, habs2]
      have hab2 : ((selTot A BL BR CC κ ω - μ)
            + (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2
              - mgSum (sgX A BL BR CC κ ε) κ ω / 2
              + gRes A BL BR CC κ ε ω)) ^ 2
          ≤ (10 / 7) * (selTot A BL BR CC κ ω - μ) ^ 2
            + (10 / 3)
              * (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2
                - mgSum (sgX A BL BR CC κ ε) κ ω / 2
                + gRes A BL BR CC κ ε ω) ^ 2 := by
        nlinarith [sq_nonneg (3 * (selTot A BL BR CC κ ω - μ)
          - 7 * (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| / 2
              - mgSum (sgX A BL BR CC κ ε) κ ω / 2
              + gRes A BL BR CC κ ε ω))]
      rw [hgb]
      nlinarith [hab2, hb2]
    have hsum1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (gBlock A BL BR CC κ ε ω - μ) ^ 2
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * ((10 / 7) * (selTot A BL BR CC κ ω - μ) ^ 2
              + (5 / 2)
                * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2
              + (5 / 2) * (mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2
              + 10 * ((κ : ℝ) * ε / 2 + cB) ^ 2) :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hpath ω) (hRP0 ω)
    refine le_trans hsum1 ?_
    have hsplit : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((10 / 7) * (selTot A BL BR CC κ ω - μ) ^ 2
          + (5 / 2) * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2
          + (5 / 2) * (mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2
          + 10 * ((κ : ℝ) * ε / 2 + cB) ^ 2)
        = (10 / 7) * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * (selTot A BL BR CC κ ω - μ) ^ 2)
          + (5 / 2) * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2)
          + (5 / 2) * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
              * (mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2)
          + 10 * ((κ : ℝ) * ε / 2 + cB) ^ 2 := by
      rw [Finset.sum_congr rfl (fun ω (_ : ω ∈ Finset.univ) =>
        show RP A BL BR CC κ ε ω
            * ((10 / 7) * (selTot A BL BR CC κ ω - μ) ^ 2
              + (5 / 2)
                * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2
              + (5 / 2) * (mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2
              + 10 * ((κ : ℝ) * ε / 2 + cB) ^ 2)
          = (10 / 7) * (RP A BL BR CC κ ε ω
              * (selTot A BL BR CC κ ω - μ) ^ 2)
            + (5 / 2) * (RP A BL BR CC κ ε ω
                * (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω) ^ 2)
            + (5 / 2) * (RP A BL BR CC κ ε ω
                * (mgSum (sgX A BL BR CC κ ε) κ ω) ^ 2)
            + (10 * ((κ : ℝ) * ε / 2 + cB) ^ 2) * RP A BL BR CC κ ε ω
          from by ring),
        Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, hRPs, mul_one]
    rw [hsplit]
    have hY2 := race_sgSum_sq A BL BR CC κ ε hε hcB
    have hΔ2 := race_imb_sq A BL BR CC κ ε hε hcB
    have hκ0 : (0 : ℝ) ≤ (κ : ℝ) * (cB + ε) ^ 2 := by positivity
    nlinarith [hsel2, hY2, hΔ2, hV0]
  -- assemble
  have hexpand : ∀ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((∑ i : Fin (mrace A BL BR CC κ),
            rsize A BL BR CC κ ε ω (i : ℕ)) - (mA + mG + mC)) ^ 2
      = RP A BL BR CC κ ε ω * (preSum A ω.1 A.m - mA) ^ 2
        + RP A BL BR CC κ ε ω * (gBlock A BL BR CC κ ε ω - mG) ^ 2
        + RP A BL BR CC κ ε ω * (ccPart A BL BR CC κ ω - mC) ^ 2
        + 2 * (RP A BL BR CC κ ε ω * ((preSum A ω.1 A.m - mA)
            * (gBlock A BL BR CC κ ε ω - mG)))
        + 2 * (RP A BL BR CC κ ε ω * ((preSum A ω.1 A.m - mA)
            * (ccPart A BL BR CC κ ω - mC)))
        + 2 * (RP A BL BR CC κ ε ω * ((gBlock A BL BR CC κ ε ω - mG)
            * (ccPart A BL BR CC κ ω - mC))) := by
    intro ω
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    unfold gBlock
    ring
  rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => hexpand ω,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hPQ, hPR, hQR]
  linarith [hEA, hEG, hEC]

end Var4

end Race

end KServer


