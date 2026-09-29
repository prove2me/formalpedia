-- Prove2me | Definitions.Def_KServer_race_sel
-- name    : KServer_race_sel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T22:26:01.164287+00:00
-- url     : https://prove2.me/theorems/7f9d107d-b9fd-4bda-9716-9df67360e333
-- title:
--   The sturdy selection bound and variance-free race total
-- statement:
--   The survivor bit and the coin weights of the race are determined by the depth-kappa atoms of the two side systems, so each side's total enters the expected race total only through its conditional expectation at depth kappa, and the selection weight of an atom never exceeds its mass. Consequently the expected total of the surviving side is at least the common lower bound on the sides' expected totals minus the two sides' depth-kappa L1 drawdowns (race_sel_ge), and the expected race total is at least 3T + G/2 minus the drawdowns and explicit lower-order losses, with no variance term (race_total3). This replaces the earlier variance-based bound, whose -2*sqrt(V) loss structurally exceeds the provable anti-concentration gain in the level recursion.
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
import Definitions.Def_KServer_sturdy

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Sel

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- The per-step coin weight is determined by the depth-κ atoms of the
left side. -/
theorem coinW_congr_l (a : A.Ω) {l l' : BL.Ω} (r : BR.Ω)
    (hl : BL.hist κ l' = BL.hist κ l) (j : ℕ) (hj : j ≤ κ)
    (p : Fin j → Bool) (b : Bool) :
    coinW A BL BR a l' r (ε := ε) j p b
      = coinW A BL BR a l r (ε := ε) j p b := by
  unfold coinW
  have hsz : BL.sizeN (cntL (fun i : Fin j => p i) j) l'
      = BL.sizeN (cntL (fun i : Fin j => p i) j) l :=
    sizeN_congr_le BL
      (le_trans (cntL_le (fun i : Fin j => p i) (le_refl j)) hj) hl
  simp only [hsz]

/-- The per-step coin weight is determined by the depth-κ atoms of the
right side. -/
theorem coinW_congr_r (a : A.Ω) (l : BL.Ω) {r r' : BR.Ω}
    (hr : BR.hist κ r' = BR.hist κ r) (j : ℕ) (hj : j ≤ κ)
    (p : Fin j → Bool) (b : Bool) :
    coinW A BL BR a l r' (ε := ε) j p b
      = coinW A BL BR a l r (ε := ε) j p b := by
  unfold coinW
  have hsz : BR.sizeN (cntR (fun i : Fin j => p i) j) r'
      = BR.sizeN (cntR (fun i : Fin j => p i) j) r :=
    sizeN_congr_le BR
      (le_trans (cntR_le (fun i : Fin j => p i) (le_refl j)) hj) hr
  simp only [hsz]

/-- The coin-path weight is determined by the depth-κ atoms of the left
side. -/
theorem coinWt_congr_l (a : A.Ω) {l l' : BL.Ω} (r : BR.Ω)
    (χ : Fin κ → Bool) (hl : BL.hist κ l' = BL.hist κ l) :
    coinWt (coinW A BL BR a l' r (ε := ε)) χ
      = coinWt (coinW A BL BR a l r (ε := ε)) χ := by
  unfold coinWt
  refine Finset.prod_congr rfl fun j _ => ?_
  exact coinW_congr_l A BL BR κ ε a r hl (j : ℕ) (le_of_lt j.isLt) _ _

/-- The coin-path weight is determined by the depth-κ atoms of the right
side. -/
theorem coinWt_congr_r (a : A.Ω) (l : BL.Ω) {r r' : BR.Ω}
    (χ : Fin κ → Bool) (hr : BR.hist κ r' = BR.hist κ r) :
    coinWt (coinW A BL BR a l r' (ε := ε)) χ
      = coinWt (coinW A BL BR a l r (ε := ε)) χ := by
  unfold coinWt
  refine Finset.prod_congr rfl fun j _ => ?_
  exact coinW_congr_r A BL BR κ ε a l hr (j : ℕ) (le_of_lt j.isLt) _ _

/-- The consumed left mass is determined by the depth-κ atom of the left
side. -/
theorem sumL_congr_atom (a a' : A.Ω) {l l' : BL.Ω} (r : BR.Ω)
    (cc cc' : CC.Ω) (χ : Fin κ → Bool)
    (hl : BL.hist κ l' = BL.hist κ l) :
    sumL A BL BR CC κ (a', l', r, cc', χ)
      = sumL A BL BR CC κ (a, l, r, cc, χ) := by
  unfold sumL
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hb : χ j = true
  · rw [if_pos hb, if_pos hb]
    show BL.sizeN (cntL χ (j : ℕ)) l' = BL.sizeN (cntL χ (j : ℕ)) l
    exact sizeN_congr_le BL
      (le_trans (cntL_le χ (le_of_lt j.isLt)) (le_of_lt j.isLt)) hl
  · rw [if_neg hb, if_neg hb]

/-- The consumed right mass is determined by the depth-κ atom of the
right side. -/
theorem sumR_congr_atom (a a' : A.Ω) (l : BL.Ω) {r r' : BR.Ω}
    (cc cc' : CC.Ω) (χ : Fin κ → Bool)
    (hr : BR.hist κ r' = BR.hist κ r) :
    sumR A BL BR CC κ (a', l, r', cc', χ)
      = sumR A BL BR CC κ (a, l, r, cc, χ) := by
  unfold sumR
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hb : χ j = true
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb]
    show BR.sizeN (cntR χ (j : ℕ)) r' = BR.sizeN (cntR χ (j : ℕ)) r
    exact sizeN_congr_le BR
      (le_trans (cntR_le χ (le_of_lt j.isLt)) (le_of_lt j.isLt)) hr

/-- The survivor bit is determined by the depth-κ atom of the left
side. -/
theorem survL_congr_l (a a' : A.Ω) {l l' : BL.Ω} (r : BR.Ω)
    (cc cc' : CC.Ω) (χ : Fin κ → Bool)
    (hl : BL.hist κ l' = BL.hist κ l) :
    survL A BL BR CC κ (a', l', r, cc', χ)
      = survL A BL BR CC κ (a, l, r, cc, χ) := by
  unfold survL
  rw [sumL_congr_atom A BL BR CC κ a a' r cc cc' χ hl,
    show sumR A BL BR CC κ (a', l', r, cc', χ)
      = sumR A BL BR CC κ (a, l, r, cc, χ) from rfl]

/-- The survivor bit is determined by the depth-κ atom of the right
side. -/
theorem survL_congr_r (a a' : A.Ω) (l : BL.Ω) {r r' : BR.Ω}
    (cc cc' : CC.Ω) (χ : Fin κ → Bool)
    (hr : BR.hist κ r' = BR.hist κ r) :
    survL A BL BR CC κ (a', l, r', cc', χ)
      = survL A BL BR CC κ (a, l, r, cc, χ) := by
  unfold survL
  rw [sumR_congr_atom A BL BR CC κ a a' l cc cc' χ hr,
    show sumL A BL BR CC κ (a', l, r', cc', χ)
      = sumL A BL BR CC κ (a, l, r, cc, χ) from rfl]

/-- Reduction of a race expectation of a coin/side function to the
product of the side measures with the coin-tree weights. -/
theorem RP_reduce (hε : 0 < ε) (a₀ : A.Ω) (c₀ : CC.Ω)
    (g : RΩ A BL BR CC κ → ℝ)
    (hg : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc cc' : CC.Ω)
      (χ : Fin κ → Bool), g (a, l, r, cc, χ) = g (a', l, r, cc', χ)) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω
      = ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
          BL.P l * (BR.P r
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * g (a₀, l, r, c₀, χ) := by
  have hpt : ∀ (a : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω)
      (c : Fin κ → Bool),
      RP A BL BR CC κ ε (a, l, r, cc, c) * g (a, l, r, cc, c)
      = (CC.P cc) * (A.P a * (BL.P l * (BR.P r
          * coinWt (coinW A BL BR a₀ l r (ε := ε)) c)
          * g (a₀, l, r, c₀, c))) := by
    intro a l r cc c
    rw [hg a a₀ l r cc c₀ c]
    show A.P a * (BL.P l * (BR.P r * (CC.P cc
        * coinWt (coinW A BL BR a l r (ε := ε)) c)))
        * g (a₀, l, r, c₀, c) = _
    rw [coinW_indep A BL BR ε a a₀ l r]
    ring
  have hslice : ∀ a : A.Ω,
      (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
        RP A BL BR CC κ ε (a, l, r, cc, c) * g (a, l, r, cc, c))
      = A.P a * ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
          BL.P l * (BR.P r
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * g (a₀, l, r, c₀, χ) := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    calc ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
          RP A BL BR CC κ ε (a, l, r, cc, c) * g (a, l, r, cc, c)
        = ∑ cc : CC.Ω, ∑ c : Fin κ → Bool, (CC.P cc)
            * (A.P a * (BL.P l * (BR.P r
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) c)
                * g (a₀, l, r, c₀, c))) :=
          Finset.sum_congr rfl fun cc _ =>
            Finset.sum_congr rfl fun c _ => hpt a l r cc c
      _ = ∑ cc : CC.Ω, (CC.P cc)
            * ∑ c : Fin κ → Bool, A.P a * (BL.P l * (BR.P r
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) c)
                * g (a₀, l, r, c₀, c)) :=
          Finset.sum_congr rfl fun cc _ => (Finset.mul_sum _ _ _).symm
      _ = (∑ cc : CC.Ω, CC.P cc)
            * ∑ c : Fin κ → Bool, A.P a * (BL.P l * (BR.P r
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) c)
                * g (a₀, l, r, c₀, c)) :=
          (Finset.sum_mul _ _ _).symm
      _ = A.P a * ∑ χ : Fin κ → Bool,
            BL.P l * (BR.P r
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * g (a₀, l, r, c₀, χ) := by
          rw [CC.hPsum, one_mul, Finset.mul_sum]
  calc ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω
      = ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
          ∑ c : Fin κ → Bool,
          RP A BL BR CC κ ε (a, l, r, cc, c) * g (a, l, r, cc, c) :=
        sum_RΩ_expand A BL BR CC κ
          (fun ω => RP A BL BR CC κ ε ω * g ω)
    _ = ∑ a : A.Ω, A.P a * ∑ l : BL.Ω, ∑ r : BR.Ω,
          ∑ χ : Fin κ → Bool,
          BL.P l * (BR.P r
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * g (a₀, l, r, c₀, χ) :=
        Finset.sum_congr rfl fun a _ => hslice a
    _ = ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
          BL.P l * (BR.P r
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * g (a₀, l, r, c₀, χ) := by
        rw [← Finset.sum_mul, A.hPsum, one_mul]

/-- The coin-path weights over one left outcome sum to one. -/
theorem coin_mass_one_l (hε : 0 < ε) (a₀ : A.Ω) (l : BL.Ω) :
    ∑ r : BR.Ω, BR.P r * ∑ χ : Fin κ → Bool,
        coinWt (coinW A BL BR a₀ l r (ε := ε)) χ = 1 := by
  have hin : ∀ r : BR.Ω, ∑ χ : Fin κ → Bool,
      coinWt (coinW A BL BR a₀ l r (ε := ε)) χ = 1 := by
    intro r
    refine sum_coinWt fun j p => ?_
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  rw [Finset.sum_congr rfl fun r _ => by rw [hin r]]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => mul_one (BR.P r)]
  exact BR.hPsum

/-- The coin-path weights over one right outcome sum to one. -/
theorem coin_mass_one_r (hε : 0 < ε) (a₀ : A.Ω) (r : BR.Ω) :
    ∑ l : BL.Ω, BL.P l * ∑ χ : Fin κ → Bool,
        coinWt (coinW A BL BR a₀ l r (ε := ε)) χ = 1 := by
  have hin : ∀ l : BL.Ω, ∑ χ : Fin κ → Bool,
      coinWt (coinW A BL BR a₀ l r (ε := ε)) χ = 1 := by
    intro l
    refine sum_coinWt fun j p => ?_
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  rw [Finset.sum_congr rfl fun l _ => by rw [hin l]]
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => mul_one (BL.P l)]
  exact BL.hPsum

open Classical in
/-- **The sturdy selection bound**: the expected total of the surviving
side is at least the common lower bound on the sides' expected totals,
minus the two sides' depth-κ L¹ drawdowns.  The survivor bit and the
coin weights are determined by the depth-κ atoms of the sides, so each
side's total enters only through its conditional expectation at depth κ,
and the selection weight of an atom never exceeds its mass. -/
theorem race_sel_ge (hε : 0 < ε) {DL DR E' : ℝ}
    (hL1 : ∑ l : BL.Ω, BL.P l
      * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0 ≤ DL)
    (hR1 : ∑ r : BR.Ω, BR.P r
      * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0 ≤ DR)
    (hEL : E' ≤ BL.expTotal) (hER : E' ≤ BR.expTotal) :
    E' - DL - DR ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * selTot A BL BR CC κ ω := by
  obtain ⟨a₀⟩ := omega_nonempty A
  obtain ⟨c₀⟩ := omega_nonempty CC
  have hW0 : ∀ (l : BL.Ω) (r : BR.Ω) (χ : Fin κ → Bool),
      0 ≤ coinWt (coinW A BL BR a₀ l r (ε := ε)) χ := by
    intro l r χ
    refine le_of_lt (coinWt_pos (fun j p b => ?_) χ)
    unfold coinW
    dsimp only
    split
    · exact probL_pos hε
    · exact probL_pos hε
  -- reduce the race expectation to the side/coin measure
  rw [RP_reduce A BL BR CC κ ε hε a₀ c₀ (selTot A BL BR CC κ)
    (fun a a' l r cc cc' χ => rfl)]
  -- split into the two survivor branches, in weight-times-total form
  have hsplit : ∀ (l : BL.Ω) (r : BR.Ω) (χ : Fin κ → Bool),
      BL.P l * (BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
        * selTot A BL BR CC κ (a₀, l, r, c₀, χ)
      = BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (1 : ℝ) else 0)) * BL.totalSize l)
        + BR.P r * ((BL.P l
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (0 : ℝ) else 1)) * BR.totalSize r) := by
    intro l r χ
    show BL.P l * (BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
        * (if survL A BL BR CC κ (a₀, l, r, c₀, χ)
           then preSum BL l BL.m else preSum BR r BR.m) = _
    by_cases hs : survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
    · rw [if_pos hs, if_pos hs, if_pos hs,
        show preSum BL l BL.m = BL.totalSize l from preSum_total BL l]
      ring
    · rw [if_neg hs, if_neg hs, if_neg hs,
        show preSum BR r BR.m = BR.totalSize r from preSum_total BR r]
      ring
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
    Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) =>
      Finset.sum_congr rfl fun χ (_ : χ ∈ Finset.univ) => hsplit l r χ]
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
    Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) =>
      Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
    Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  -- name the two branch sums
  set SL := ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
    BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
        * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
           then (1 : ℝ) else 0)) * BL.totalSize l) with hSL
  set SR := ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
    BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
        * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
           then (0 : ℝ) else 1)) * BR.totalSize r) with hSR
  -- selection masses
  set PL := ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
    BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
        * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
           then (1 : ℝ) else 0))) with hPL
  set PR := ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
    BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
        * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
           then (0 : ℝ) else 1))) with hPR
  have hPL0 : 0 ≤ PL := by
    rw [hPL]
    refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ =>
      Finset.sum_nonneg fun χ _ => ?_
    have h1 : (0 : ℝ) ≤ (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
        then (1 : ℝ) else 0) := by positivity
    have h2 := hW0 l r χ
    have h3 := (BL.hP l).le
    have h4 := (BR.hP r).le
    positivity
  have hPR0 : 0 ≤ PR := by
    rw [hPR]
    refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ =>
      Finset.sum_nonneg fun χ _ => ?_
    have h1 : (0 : ℝ) ≤ (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
        then (0 : ℝ) else 1) := by positivity
    have h2 := hW0 l r χ
    have h3 := (BL.hP l).le
    have h4 := (BR.hP r).le
    positivity
  have hPsum1 : PL + PR = 1 := by
    rw [hPL, hPR, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
      (Finset.sum_add_distrib).symm]
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
      Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) =>
        (Finset.sum_add_distrib).symm]
    have hpt : ∀ (l : BL.Ω) (r : BR.Ω) (χ : Fin κ → Bool),
        BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (1 : ℝ) else 0)))
          + BR.P r * ((BL.P l
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (0 : ℝ) else 1)))
        = BL.P l * (BR.P r
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ) * 1 := by
      intro l r χ
      by_cases hs : survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
      · rw [if_pos hs, if_pos hs]
        ring
      · rw [if_neg hs, if_neg hs]
        ring
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
      Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) =>
        Finset.sum_congr rfl fun χ (_ : χ ∈ Finset.univ) => hpt l r χ]
    rw [← RP_reduce A BL BR CC κ ε hε a₀ c₀ (fun _ => (1 : ℝ))
      (fun _ _ _ _ _ _ _ => rfl)]
    rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) =>
      mul_one (RP A BL BR CC κ ε ω)]
    exact RP_sum A BL BR CC κ ε hε
  -- rotation helper
  have sum3_rot : ∀ {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
      (f : α → β → γ → ℝ),
      (∑ x : α, ∑ y : β, ∑ z : γ, f x y z)
        = ∑ y : β, ∑ z : γ, ∑ x : α, f x y z := by
    intro α β γ _ _ _ f
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
  -- the left branch
  have hSLb : BL.expTotal * PL - DL ≤ SL := by
    have hproj : ∀ (r : BR.Ω) (χ : Fin κ → Bool),
        (∑ l : BL.Ω, BL.P l
          * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (1 : ℝ) else 0)) * BL.totalSize l))
        = ∑ l : BL.Ω, BL.P l
          * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (1 : ℝ) else 0))
            * BL.condExp BL.totalSize κ l) := by
      intro r χ
      refine ChunkSystemB.sum_P_mul_condExp κ
        (fun l => BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
          * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
             then (1 : ℝ) else 0))
        BL.totalSize (fun l l' hll' => ?_)
      show BR.P r * coinWt (coinW A BL BR a₀ l' r (ε := ε)) χ
          * (if survL A BL BR CC κ (a₀, l', r, c₀, χ) = true
             then (1 : ℝ) else 0)
        = BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
          * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
             then (1 : ℝ) else 0)
      rw [coinWt_congr_l A BL BR κ ε a₀ r χ hll',
        survL_congr_l A BL BR CC κ a₀ a₀ r c₀ c₀ χ hll']
    have hlow : ∀ (r : BR.Ω) (χ : Fin κ → Bool) (l : BL.Ω),
        BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (1 : ℝ) else 0)) * BL.expTotal)
          - BL.P l * ((BR.P r
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0)
        ≤ BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (1 : ℝ) else 0))
          * BL.condExp BL.totalSize κ l) := by
      intro r χ l
      have hP := (BL.hP l).le
      have hQ := mul_nonneg (BR.hP r).le (hW0 l r χ)
      have hdd : BL.expTotal - BL.condExp BL.totalSize κ l
          ≤ max (BL.expTotal - BL.condExp BL.totalSize κ l) 0 :=
        le_max_left _ _
      have hdd0 : (0 : ℝ)
          ≤ max (BL.expTotal - BL.condExp BL.totalSize κ l) 0 :=
        le_max_right _ _
      by_cases hs : survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
      · rw [if_pos hs]
        have h1 : BL.expTotal
            - max (BL.expTotal - BL.condExp BL.totalSize κ l) 0
            ≤ BL.condExp BL.totalSize κ l := by linarith
        have h2 := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 hQ) hP
        nlinarith [h2]
      · rw [if_neg hs]
        have h2 : 0 ≤ BL.P l * ((BR.P r
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0) :=
          mul_nonneg hP (mul_nonneg hQ hdd0)
        nlinarith [h2]
    have hdrawL : ∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
        BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0)
        ≤ DL := by
      have hback : (∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
          BL.P l * ((BR.P r
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0))
          = ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
            BL.P l * ((BR.P r
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
              * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0) := by
        rw [sum3_rot (fun l r χ =>
          BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0))]
      rw [hback]
      have hfac : ∀ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
          BL.P l * ((BR.P r
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0)
          = (BL.P l
              * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0)
            * ∑ r : BR.Ω, BR.P r * ∑ χ : Fin κ → Bool,
                coinWt (coinW A BL BR a₀ l r (ε := ε)) χ := by
        intro l
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [show (BL.P l
              * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0)
            * (BR.P r * ∑ χ : Fin κ → Bool,
                coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          = (BL.P l
              * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0
              * BR.P r)
            * ∑ χ : Fin κ → Bool,
                coinWt (coinW A BL BR a₀ l r (ε := ε)) χ from by ring,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ => by ring
      rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hfac l]
      rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by
        rw [coin_mass_one_l A BL BR κ ε hε a₀ l, mul_one]]
      exact hL1
    have hmain : ∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
        BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (1 : ℝ) else 0)) * BL.expTotal)
        = BL.expTotal * PL := by
      have hback : (∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
          BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (1 : ℝ) else 0)) * BL.expTotal))
          = ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
            BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (1 : ℝ) else 0)) * BL.expTotal) := by
        rw [sum3_rot (fun l r χ =>
          BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (1 : ℝ) else 0)) * BL.expTotal))]
      rw [hback, hPL, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    have hcomm : SL = ∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
        BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (1 : ℝ) else 0)) * BL.totalSize l) := by
      rw [hSL]
      exact sum3_rot (fun l r χ =>
        BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (1 : ℝ) else 0)) * BL.totalSize l))
    calc BL.expTotal * PL - DL
        ≤ (∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
            BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (1 : ℝ) else 0)) * BL.expTotal))
          - ∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
              BL.P l * ((BR.P r
                  * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
                * max (BL.expTotal
                    - BL.condExp BL.totalSize κ l) 0) := by
          rw [hmain]
          linarith [hdrawL]
      _ = ∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
            (BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (1 : ℝ) else 0)) * BL.expTotal)
              - BL.P l * ((BR.P r
                  * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
                * max (BL.expTotal
                    - BL.condExp BL.totalSize κ l) 0)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ r : BR.Ω, ∑ χ : Fin κ → Bool, ∑ l : BL.Ω,
            BL.P l * ((BR.P r * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (1 : ℝ) else 0))
              * BL.condExp BL.totalSize κ l) :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun χ _ =>
            Finset.sum_le_sum fun l _ => hlow r χ l
      _ = SL := by
          rw [hcomm]
          exact (Finset.sum_congr rfl fun r _ =>
            Finset.sum_congr rfl fun χ _ => (hproj r χ).symm)
  -- the right branch
  have hSRb : BR.expTotal * PR - DR ≤ SR := by
    have hproj : ∀ (l : BL.Ω) (χ : Fin κ → Bool),
        (∑ r : BR.Ω, BR.P r
          * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (0 : ℝ) else 1)) * BR.totalSize r))
        = ∑ r : BR.Ω, BR.P r
          * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (0 : ℝ) else 1))
            * BR.condExp BR.totalSize κ r) := by
      intro l χ
      refine ChunkSystemB.sum_P_mul_condExp κ
        (fun r => BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
          * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
             then (0 : ℝ) else 1))
        BR.totalSize (fun r r' hrr' => ?_)
      show BL.P l * coinWt (coinW A BL BR a₀ l r' (ε := ε)) χ
          * (if survL A BL BR CC κ (a₀, l, r', c₀, χ) = true
             then (0 : ℝ) else 1)
        = BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
          * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
             then (0 : ℝ) else 1)
      rw [coinWt_congr_r A BL BR κ ε a₀ l χ hrr',
        survL_congr_r A BL BR CC κ a₀ a₀ l c₀ c₀ χ hrr']
    have hlow : ∀ (l : BL.Ω) (χ : Fin κ → Bool) (r : BR.Ω),
        BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (0 : ℝ) else 1)) * BR.expTotal)
          - BR.P r * ((BL.P l
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0)
        ≤ BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (0 : ℝ) else 1))
          * BR.condExp BR.totalSize κ r) := by
      intro l χ r
      have hP := (BR.hP r).le
      have hQ := mul_nonneg (BL.hP l).le (hW0 l r χ)
      have hdd : BR.expTotal - BR.condExp BR.totalSize κ r
          ≤ max (BR.expTotal - BR.condExp BR.totalSize κ r) 0 :=
        le_max_left _ _
      have hdd0 : (0 : ℝ)
          ≤ max (BR.expTotal - BR.condExp BR.totalSize κ r) 0 :=
        le_max_right _ _
      by_cases hs : survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
      · rw [if_pos hs]
        have h2 : 0 ≤ BR.P r * ((BL.P l
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0) :=
          mul_nonneg hP (mul_nonneg hQ hdd0)
        nlinarith [h2]
      · rw [if_neg hs]
        have h1 : BR.expTotal
            - max (BR.expTotal - BR.condExp BR.totalSize κ r) 0
            ≤ BR.condExp BR.totalSize κ r := by linarith
        have h2 := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 hQ) hP
        nlinarith [h2]
    have hdrawR : ∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
        BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0)
        ≤ DR := by
      have hback : (∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
          BR.P r * ((BL.P l
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0))
          = ∑ r : BR.Ω, ∑ l : BL.Ω, ∑ χ : Fin κ → Bool,
            BR.P r * ((BL.P l
                * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
              * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0) := by
        rw [sum3_rot (fun l χ r =>
          BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0))]
        exact sum3_rot (fun χ r l =>
          BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0))
      rw [hback]
      have hfac : ∀ r : BR.Ω, ∑ l : BL.Ω, ∑ χ : Fin κ → Bool,
          BR.P r * ((BL.P l
              * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
            * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0)
          = (BR.P r
              * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0)
            * ∑ l : BL.Ω, BL.P l * ∑ χ : Fin κ → Bool,
                coinWt (coinW A BL BR a₀ l r (ε := ε)) χ := by
        intro r
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show (BR.P r
              * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0)
            * (BL.P l * ∑ χ : Fin κ → Bool,
                coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
          = (BR.P r
              * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0
              * BL.P l)
            * ∑ χ : Fin κ → Bool,
                coinWt (coinW A BL BR a₀ l r (ε := ε)) χ from by ring,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ => by ring
      rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => hfac r]
      rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => by
        rw [coin_mass_one_r A BL BR κ ε hε a₀ r, mul_one]]
      exact hR1
    have hmain : ∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
        BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (0 : ℝ) else 1)) * BR.expTotal)
        = BR.expTotal * PR := by
      have hback : (∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
          BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
              * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                 then (0 : ℝ) else 1)) * BR.expTotal))
          = ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ χ : Fin κ → Bool,
            BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (0 : ℝ) else 1)) * BR.expTotal) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
      rw [hback, hPR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    have hcomm : SR = ∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
        BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
            * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
               then (0 : ℝ) else 1)) * BR.totalSize r) := by
      rw [hSR]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    calc BR.expTotal * PR - DR
        ≤ (∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
            BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (0 : ℝ) else 1)) * BR.expTotal))
          - ∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
              BR.P r * ((BL.P l
                  * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
                * max (BR.expTotal
                    - BR.condExp BR.totalSize κ r) 0) := by
          rw [hmain]
          linarith [hdrawR]
      _ = ∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
            (BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (0 : ℝ) else 1)) * BR.expTotal)
              - BR.P r * ((BL.P l
                  * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ)
                * max (BR.expTotal
                    - BR.condExp BR.totalSize κ r) 0)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ l : BL.Ω, ∑ χ : Fin κ → Bool, ∑ r : BR.Ω,
            BR.P r * ((BL.P l * coinWt (coinW A BL BR a₀ l r (ε := ε)) χ
                * (if survL A BL BR CC κ (a₀, l, r, c₀, χ) = true
                   then (0 : ℝ) else 1))
              * BR.condExp BR.totalSize κ r) :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun χ _ =>
            Finset.sum_le_sum fun r _ => hlow l χ r
      _ = SR := by
          rw [hcomm]
          exact (Finset.sum_congr rfl fun l _ =>
            Finset.sum_congr rfl fun χ _ => (hproj l χ).symm)
  -- assemble
  have hE'PL := mul_le_mul_of_nonneg_right hEL hPL0
  have hE'PR := mul_le_mul_of_nonneg_right hER hPR0
  have hE1 : E' * PL + E' * PR = E' := by
    rw [← mul_add, hPsum1, mul_one]
  linarith [hSLb, hSRb, hE'PL, hE'PR]

/-- The survivor tail dominates the selected total minus the consumed
minimum and one sacrificed chunk. -/
theorem survPart_ge2 (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    selTot A BL BR CC κ ω
      - min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω) - cB
      ≤ survPart A BL BR CC κ ω := by
  cases hs : survL A BL BR CC κ ω with
  | true =>
    have hle := (survL_true_iff A BL BR CC κ ω).mp hs
    unfold selTot survPart
    rw [if_pos hs, if_pos hs, preSum_succ,
      ← sumL_eq_preSum κ A BL BR CC ω]
    linarith [min_eq_left hle,
      sizeN_le_cB BL hcB (cntL ω.2.2.2.2 κ) ω.2.1]
  | false =>
    have hle := survL_false_le A BL BR CC κ ω hs
    unfold selTot survPart
    rw [if_neg (by simp [hs]), if_neg (by simp [hs]), preSum_succ,
      ← sumR_eq_preSum κ A BL BR CC ω]
    linarith [min_eq_right hle,
      sizeN_le_cB BR hcB (cntR ω.2.2.2.2 κ) ω.2.2.1]

open Classical in
/-- **The race total, sturdy form**: the expected total of the race is at
least `3T + G/2` minus the sides' depth-κ L¹ drawdowns and explicit
lower-order losses — with no variance term.  The survivor's total enters
through the sturdy selection bound. -/
theorem race_total3 (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {DL DR G : ℝ}
    (hL1 : ∑ l : BL.Ω, BL.P l
      * max (BL.expTotal - BL.condExp BL.totalSize κ l) 0 ≤ DL)
    (hR1 : ∑ r : BR.Ω, BR.P r
      * max (BR.expTotal - BR.condExp BR.totalSize κ r) 0 ≤ DR)
    (hG : G ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|) :
    3 * T + G / 2 - DL - DR - (κ : ℝ) * ε / 2 - 2 * cB
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω (i : ℕ) := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  have hdec : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω (i : ℕ)
    = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * preSum A ω.1 A.m)
      + (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
      + (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * survPart A BL BR CC κ ω)
      + (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ccPart A BL BR CC κ ω) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    ring
  rw [hdec]
  have hEA : T ≤ ∑ ω : RΩ A BL BR CC κ,
      RP A BL BR CC κ ε ω * preSum A ω.1 A.m := by
    have h1 : ∑ ω : RΩ A BL BR CC κ,
        RP A BL BR CC κ ε ω * preSum A ω.1 A.m
        = ∑ a : A.Ω, A.P a * preSum A a A.m :=
      RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)
    rw [h1]
    refine le_trans A.htotal (le_of_eq ?_)
    exact Finset.sum_congr rfl fun a _ => by rw [preSum_total]
  have hEcc : T - cB ≤ ∑ ω : RΩ A BL BR CC κ,
      RP A BL BR CC κ ε ω * ccPart A BL BR CC κ ω := by
    have h1 : ∑ ω : RΩ A BL BR CC κ,
        RP A BL BR CC κ ε ω * ccPart A BL BR CC κ ω
        = ∑ cc : CC.Ω, CC.P cc
            * (preSum CC cc CC.m - preSum CC cc 1) :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => preSum CC cc CC.m - preSum CC cc 1)
    rw [h1, sum_mul_sub]
    have h2 : T ≤ ∑ cc : CC.Ω, CC.P cc * preSum CC cc CC.m := by
      refine le_trans CC.htotal (le_of_eq ?_)
      exact Finset.sum_congr rfl fun cc _ => by rw [preSum_total]
    have h3 : ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 ≤ cB := by
      have h4 : ∀ cc : CC.Ω, CC.P cc * preSum CC cc 1
          ≤ CC.P cc * cB := by
        intro cc
        refine mul_le_mul_of_nonneg_left ?_ (CC.hP cc).le
        have h5 : preSum CC cc 1 = CC.sizeN 0 cc := by
          unfold preSum
          rw [Finset.sum_range_one]
        rw [h5]
        exact sizeN_le_cB CC hcB 0 cc
      refine le_trans (Finset.sum_le_sum fun cc _ => h4 cc) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum cB (fun cc => CC.P cc * cB)
        (fun cc => by ring)
    linarith
  -- the sturdy selection bound
  have hEsel : T - DL - DR ≤ ∑ ω : RΩ A BL BR CC κ,
      RP A BL BR CC κ ε ω * selTot A BL BR CC κ ω := by
    refine race_sel_ge A BL BR CC κ ε hε hL1 hR1 ?_ ?_
    · exact BL.htotal
    · exact BR.htotal
  have hEsurv : (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * selTot A BL BR CC κ ω)
      - (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω)) - cB
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * survPart A BL BR CC κ ω := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (selTot A BL BR CC κ ω
            - min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω) - cB)
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * survPart A BL BR CC κ ω :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
        (survPart_ge2 A BL BR CC κ hcB ω) (hRP0 ω)
    refine le_trans (le_of_eq ?_) h1
    exact (sum_mul_sub_sub (RP A BL BR CC κ ε)
      (fun ω => selTot A BL BR CC κ ω)
      (fun ω => min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω))
      cB hRPs).symm
  have hEm2 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω)
      = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (sumL A BL BR CC κ ω + sumR A BL BR CC κ ω)) / 2
        - (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|) / 2 :=
    sum_mul_min (RP A BL BR CC κ ε) (fun ω => sumL A BL BR CC κ ω)
      (fun ω => sumR A BL BR CC κ ω)
  have hEcoin : (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (sumL A BL BR CC κ ω + sumR A BL BR CC κ ω)) / 2
        - (κ : ℝ) * ε / 2
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j := by
    have hcoinpath : ∀ ω : RΩ A BL BR CC κ,
        (∑ j ∈ Finset.range κ,
            (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
                * nextL A BL BR CC κ ω j
              + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
                * nextR A BL BR CC κ ω j)) / 2 - (κ : ℝ) * ε / 2
          ≤ ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j := by
      intro ω
      have h1 : ∀ j ∈ Finset.range κ,
          (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
              * nextL A BL BR CC κ ω j
            + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
              * nextR A BL BR CC κ ω j) / 2 - ε / 2
            ≤ coinTerm A BL BR CC κ ε ω j :=
        fun j _ => coinTerm_ge A BL BR CC κ ε hε ω j
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum h1)
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    have h2 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((∑ j ∈ Finset.range κ,
            (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
                * nextL A BL BR CC κ ω j
              + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
                * nextR A BL BR CC κ ω j)) / 2 - (κ : ℝ) * ε / 2)
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
        (hcoinpath ω) (hRP0 ω)
    refine le_trans (le_of_eq ?_) h2
    rw [sum_mul_div_sub (RP A BL BR CC κ ε)
      (fun ω => ∑ j ∈ Finset.range κ,
        (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
            * nextL A BL BR CC κ ω j
          + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
            * nextR A BL BR CC κ ω j))
      ((κ : ℝ) * ε / 2) hRPs, ← sum_consumed A BL BR CC κ ε hε]
  linarith

end Sel

end Race

end KServer


