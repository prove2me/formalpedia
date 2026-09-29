-- Prove2me | Definitions.Def_KServer_race_gain
-- name    : KServer_race_gain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T19:05:29.805915+00:00
-- url     : https://prove2.me/theorems/c777978b-b38f-4144-80fa-f3f633cfc82a
-- title:
--   The race imbalance martingale
-- statement:
--   The imbalance martingale of the race. For the race chunk system with clamped coin probabilities, the centered increments
--   $$X_j = \big(\mathbf{1}_{\text{coin}_j = L}\, n_L^{(j)} - \mathbf{1}_{\text{coin}_j = R}\, n_R^{(j)}\big) - d_j, \qquad d_j = p_L^{(j)} n_L^{(j)} - p_R^{(j)} n_R^{(j)},$$
--   form a discrete martingale difference sequence for the full-reveal filtration (all four component outcomes plus the coin prefix), with explicit conditional second moments $v_j$. The one-step conditional identities are proved from a single conditional-expectation lemma for the path-dependent coin tree. The increments satisfy $|X_j| \le c_B + \varepsilon$ and the drift satisfies $|d_j| \le \varepsilon$; the conditional variances satisfy $v_j \le (c_B+\varepsilon)^2$ always, and $v_j = n_L^{(j)} n_R^{(j)} \ge c_{Lo}'^2$ whenever both sides carry a size window $c_{Lo}' \ge \varepsilon$ below their sizes. Consequently the total conditional variance lies pathwise in the window $[\kappa\, c_{Lo}'^2, \kappa (c_B+\varepsilon)^2]$. Finally, the martingale sum equals the consumed imbalance $S_L - S_R$ up to accumulated drift at most $\kappa\varepsilon$, so its expected magnitude is dominated by $\mathbb{E}|S_L - S_R| + \kappa\varepsilon$. Together with an anti-concentration inequality for discrete martingales this lower-bounds the expected imbalance of the race.
--
--   Formalization note: the filtration is encoded by iterated pairings of finite-type indices with the coin-prefix code.
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
import Definitions.Def_KServer_discrete_martingale

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Cond

/-- One-step conditional expectation over the coin tree: summing a
function of the step-`j` coin over all strings extending a fixed
`j`-prefix. -/
theorem coinWt_cond_step {κ : ℕ} {W : (j' : ℕ) → (Fin j' → Bool) → Bool → ℝ}
    (hsum : ∀ (j' : ℕ) (p : Fin j' → Bool), W j' p true + W j' p false = 1)
    {j : ℕ} (hj : j < κ) (c₀ : Fin κ → Bool) (x y : ℝ) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
        ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i),
        coinWt W c * (if c ⟨j, hj⟩ then x else y)
      = coinWt W (restrict c₀ j (le_of_lt hj))
          * (W j (restrict c₀ j (le_of_lt hj)) true * x
            + W j (restrict c₀ j (le_of_lt hj)) false * y) := by
  have hj1 : j + 1 ≤ κ := hj
  have hsplitset : ∀ b : Bool,
      (Finset.univ.filter (fun c : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
        (fun c => c ⟨j, hj⟩ = b)
      = Finset.univ.filter (fun c : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j + 1
            → c i = Function.update c₀ ⟨j, hj⟩ b i) := by
    intro b
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hpre, hcj⟩ i hi
      rw [Function.update_apply]
      by_cases hij : i = ⟨j, hj⟩
      · rw [if_pos hij, hij]
        exact hcj
      · have hij' : (i : ℕ) < j := by
          rcases Nat.lt_or_ge (i : ℕ) j with h | h
          · exact h
          · exact absurd (Fin.ext (by omega : (i : ℕ) = j)) hij
        rw [if_neg hij]
        exact hpre i hij'
    · intro hall
      constructor
      · intro i hi
        have h1 := hall i (by omega)
        rw [Function.update_apply, if_neg
          (fun hcon => by
            have h2 := congrArg Fin.val hcon
            simp only [] at h2
            omega)] at h1
        exact h1
      · have h1 := hall ⟨j, hj⟩ (Nat.lt_succ_self j)
        rw [Function.update_apply, if_pos rfl] at h1
        exact h1
  have hwt : ∀ b : Bool,
      coinWt W (restrict (Function.update c₀ ⟨j, hj⟩ b) (j + 1) hj1)
        = coinWt W (restrict c₀ j (le_of_lt hj))
            * W j (restrict c₀ j (le_of_lt hj)) b := by
    intro b
    rw [coinWt_split_last]
    have h1 : (fun i : Fin j =>
        restrict (Function.update c₀ ⟨j, hj⟩ b) (j + 1) hj1 i.castSucc)
        = restrict c₀ j (le_of_lt hj) := by
      funext i
      show Function.update c₀ ⟨j, hj⟩ b ⟨(i : ℕ), by omega⟩
        = c₀ ⟨(i : ℕ), by omega⟩
      rw [Function.update_apply, if_neg (fun hcon => by
        have := congrArg Fin.val hcon
        simp at this
        omega)]
    have h2 : restrict (Function.update c₀ ⟨j, hj⟩ b) (j + 1) hj1
        (Fin.last j) = b := by
      show Function.update c₀ ⟨j, hj⟩ b ⟨j, hj⟩ = b
      rw [Function.update_apply, if_pos rfl]
    rw [h1, h2]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun c : Fin κ → Bool =>
      ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i))
    (fun c => c ⟨j, hj⟩ = true)]
  have htrue : ∑ c ∈ (Finset.univ.filter (fun c : Fin κ → Bool =>
      ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
        (fun c => c ⟨j, hj⟩ = true),
      coinWt W c * (if c ⟨j, hj⟩ then x else y)
      = coinWt W (restrict c₀ j (le_of_lt hj))
          * W j (restrict c₀ j (le_of_lt hj)) true * x := by
    calc ∑ c ∈ (Finset.univ.filter (fun c : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
            (fun c => c ⟨j, hj⟩ = true),
          coinWt W c * (if c ⟨j, hj⟩ then x else y)
        = ∑ c ∈ (Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
              (fun c => c ⟨j, hj⟩ = true),
            coinWt W c * x := by
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [Finset.mem_filter] at hc
          rw [if_pos hc.2]
      _ = ∑ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j + 1
              → c i = Function.update c₀ ⟨j, hj⟩ true i),
            coinWt W c * x := by rw [hsplitset true]
      _ = (∑ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j + 1
              → c i = Function.update c₀ ⟨j, hj⟩ true i),
            coinWt W c) * x := by rw [← Finset.sum_mul]
      _ = coinWt W (restrict (Function.update c₀ ⟨j, hj⟩ true)
            (j + 1) hj1) * x := by
          rw [sum_coinWt_restrict hsum hj1
            (Function.update c₀ ⟨j, hj⟩ true)]
      _ = coinWt W (restrict c₀ j (le_of_lt hj))
            * W j (restrict c₀ j (le_of_lt hj)) true * x := by
          rw [hwt true]
  have hfalse : ∑ c ∈ (Finset.univ.filter (fun c : Fin κ → Bool =>
      ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
        (fun c => ¬(c ⟨j, hj⟩ = true)),
      coinWt W c * (if c ⟨j, hj⟩ then x else y)
      = coinWt W (restrict c₀ j (le_of_lt hj))
          * W j (restrict c₀ j (le_of_lt hj)) false * y := by
    have hnf : (Finset.univ.filter (fun c : Fin κ → Bool =>
        ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
          (fun c => ¬(c ⟨j, hj⟩ = true))
        = (Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
          (fun c => c ⟨j, hj⟩ = false) := by
      ext c
      simp only [Finset.mem_filter, Bool.not_eq_true]
    calc ∑ c ∈ (Finset.univ.filter (fun c : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
            (fun c => ¬(c ⟨j, hj⟩ = true)),
          coinWt W c * (if c ⟨j, hj⟩ then x else y)
        = ∑ c ∈ (Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i)).filter
              (fun c => c ⟨j, hj⟩ = false),
            coinWt W c * y := by
          rw [hnf]
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [Finset.mem_filter] at hc
          rw [if_neg (by rw [hc.2]; exact Bool.false_ne_true)]
      _ = ∑ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j + 1
              → c i = Function.update c₀ ⟨j, hj⟩ false i),
            coinWt W c * y := by rw [hsplitset false]
      _ = (∑ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j + 1
              → c i = Function.update c₀ ⟨j, hj⟩ false i),
            coinWt W c) * y := by rw [← Finset.sum_mul]
      _ = coinWt W (restrict (Function.update c₀ ⟨j, hj⟩ false)
            (j + 1) hj1) * y := by
          rw [sum_coinWt_restrict hsum hj1
            (Function.update c₀ ⟨j, hj⟩ false)]
      _ = coinWt W (restrict c₀ j (le_of_lt hj))
            * W j (restrict c₀ j (le_of_lt hj)) false * y := by
          rw [hwt false]
  rw [htrue, hfalse]
  ring

end Cond

section GainSetup

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- The full-reveal filtration for the imbalance martingale: all four
component outcomes plus the coin prefix. -/
noncomputable def ghist (j : ℕ) (ω : RΩ A BL BR CC κ) : ℕ :=
  Nat.pair ((Fintype.equivFin A.Ω ω.1) : ℕ)
    (Nat.pair ((Fintype.equivFin BL.Ω ω.2.1) : ℕ)
      (Nat.pair ((Fintype.equivFin BR.Ω ω.2.2.1) : ℕ)
        (Nat.pair ((Fintype.equivFin CC.Ω ω.2.2.2.1) : ℕ)
          (coinCode κ ω.2.2.2.2 (min j κ)))))

theorem ghist_iff (j : ℕ) (ω ω' : RΩ A BL BR CC κ) :
    ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω'
      ↔ ω.1 = ω'.1 ∧ ω.2.1 = ω'.2.1 ∧ ω.2.2.1 = ω'.2.2.1
        ∧ ω.2.2.2.1 = ω'.2.2.2.1
        ∧ coinCode κ ω.2.2.2.2 (min j κ)
            = coinCode κ ω'.2.2.2.2 (min j κ) := by
  unfold ghist
  rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair,
    Nat.pair_eq_pair]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(Fintype.equivFin A.Ω).injective (Fin.val_injective h1),
      (Fintype.equivFin BL.Ω).injective (Fin.val_injective h2),
      (Fintype.equivFin BR.Ω).injective (Fin.val_injective h3),
      (Fintype.equivFin CC.Ω).injective (Fin.val_injective h4), h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [h1, h2, h3, h4, h5]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The one-step conditional drift of the imbalance. -/
noncomputable def gdrift (ω : RΩ A BL BR CC κ) (j : ℕ) : ℝ :=
  probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
      * nextL A BL BR CC κ ω j
    - probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
      * nextR A BL BR CC κ ω j

/-- The centered imbalance increments. -/
noncomputable def mgX (j : ℕ) (ω : RΩ A BL BR CC κ) : ℝ :=
  if h : j < κ then
    (if ω.2.2.2.2 ⟨j, h⟩ then nextL A BL BR CC κ ω j
     else -nextR A BL BR CC κ ω j) - gdrift A BL BR CC κ ε ω j
  else 0

/-- The conditional second moments of the increments. -/
noncomputable def mgV (j : ℕ) (ω : RΩ A BL BR CC κ) : ℝ :=
  if j < κ then
    probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
        * (nextL A BL BR CC κ ω j - gdrift A BL BR CC κ ε ω j) ^ 2
      + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
        * (-nextR A BL BR CC κ ω j - gdrift A BL BR CC κ ε ω j) ^ 2
  else 0

theorem nextL_congr (ω ω' : RΩ A BL BR CC κ) {j : ℕ}
    (hl : ω.2.1 = ω'.2.1)
    (hc : ∀ i : Fin κ, (i : ℕ) < j → ω.2.2.2.2 i = ω'.2.2.2.2 i) :
    nextL A BL BR CC κ ω j = nextL A BL BR CC κ ω' j := by
  unfold nextL
  rw [hl, cntL_congr hc]

theorem nextR_congr (ω ω' : RΩ A BL BR CC κ) {j : ℕ}
    (hr : ω.2.2.1 = ω'.2.2.1)
    (hc : ∀ i : Fin κ, (i : ℕ) < j → ω.2.2.2.2 i = ω'.2.2.2.2 i) :
    nextR A BL BR CC κ ω j = nextR A BL BR CC κ ω' j := by
  unfold nextR
  rw [hr, cntR_congr hc]

theorem gdrift_congr (ω ω' : RΩ A BL BR CC κ) {j : ℕ}
    (hl : ω.2.1 = ω'.2.1) (hr : ω.2.2.1 = ω'.2.2.1)
    (hc : ∀ i : Fin κ, (i : ℕ) < j → ω.2.2.2.2 i = ω'.2.2.2.2 i) :
    gdrift A BL BR CC κ ε ω j = gdrift A BL BR CC κ ε ω' j := by
  unfold gdrift
  rw [nextL_congr A BL BR CC κ ω ω' hl hc,
    nextR_congr A BL BR CC κ ω ω' hr hc]

/-- Summing over a `ghist`-atom collapses to a coin-prefix sum. -/
theorem sum_ghist_atom (g : RΩ A BL BR CC κ → ℝ) {j : ℕ} (hjκ : j ≤ κ)
    (ω₀ : RΩ A BL BR CC κ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀), g ω
      = ∑ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j → c i = ω₀.2.2.2.2 i),
          g (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) := by
  have hmin : min j κ = j := min_eq_left hjκ
  have hset : Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀)
      = Finset.image
          (fun c : Fin κ → Bool => (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c))
          (Finset.univ.filter (fun c : Fin κ → Bool =>
            ∀ i : Fin κ, (i : ℕ) < j → c i = ω₀.2.2.2.2 i)) := by
    ext ω
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hg⟩
      rw [ghist_iff] at hg
      obtain ⟨h1, h2, h3, h4, h5⟩ := hg
      rw [hmin] at h5
      refine ⟨ω.2.2.2.2, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun i hi => coinCode_inj h5 i hi⟩
      · rw [← h1, ← h2, ← h3, ← h4]
    · rintro ⟨c, hc, rfl⟩
      rw [Finset.mem_filter] at hc
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ghist_iff]
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      rw [hmin]
      exact coinCode_congr fun i hi => hc.2 i hi
  rw [hset, Finset.sum_image]
  intro c₁ _ c₂ _ h
  exact congrArg (fun ω : RΩ A BL BR CC κ => ω.2.2.2.2) h

/-- Conditional mean zero of the centered increments on every atom. -/
theorem race_hmart (hε : 0 < ε) {j : ℕ} (hj : j < κ)
    (ω₀ : RΩ A BL BR CC κ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀),
      RP A BL BR CC κ ε ω * mgX A BL BR CC κ ε j ω = 0 := by
  have hsum : ∀ (j' : ℕ) (p : Fin j' → Bool),
      coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j' p true
        + coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j' p false = 1 := by
    intro j' p
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  rw [sum_ghist_atom A BL BR CC κ
    (fun ω => RP A BL BR CC κ ε ω * mgX A BL BR CC κ ε j ω)
    (le_of_lt hj) ω₀]
  have hterm : ∀ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
      ∀ i : Fin κ, (i : ℕ) < j → c i = ω₀.2.2.2.2 i),
      RP A BL BR CC κ ε (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
        * mgX A BL BR CC κ ε j (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
      = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
        * (coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c
          * (if c ⟨j, hj⟩ then
              nextL A BL BR CC κ ω₀ j - gdrift A BL BR CC κ ε ω₀ j
             else
              -nextR A BL BR CC κ ω₀ j - gdrift A BL BR CC κ ε ω₀ j)) := by
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
    have hd : gdrift A BL BR CC κ ε
        (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
        = gdrift A BL BR CC κ ε ω₀ j :=
      gdrift_congr A BL BR CC κ ε _ ω₀ rfl rfl hc.2
    have hmgx : mgX A BL BR CC κ ε j
        (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
        = (if c ⟨j, hj⟩ then nextL A BL BR CC κ ω₀ j
           else -nextR A BL BR CC κ ω₀ j)
          - gdrift A BL BR CC κ ε ω₀ j := by
      unfold mgX
      rw [dif_pos hj]
      show (if c ⟨j, hj⟩ then
          nextL A BL BR CC κ (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
        else
          -nextR A BL BR CC κ (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j)
          - gdrift A BL BR CC κ ε
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j = _
      rw [hnl, hnr, hd]
    show A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * (CC.P ω₀.2.2.2.1
        * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c)))
        * mgX A BL BR CC κ ε j
            (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) = _
    rw [hmgx]
    by_cases hb : c ⟨j, hj⟩
    · rw [if_pos hb, if_pos hb]
      ring
    · rw [if_neg hb, if_neg hb]
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    coinWt_cond_step hsum hj ω₀.2.2.2.2
      (nextL A BL BR CC κ ω₀ j - gdrift A BL BR CC κ ε ω₀ j)
      (-nextR A BL BR CC κ ω₀ j - gdrift A BL BR CC κ ε ω₀ j)]
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
      - probL (nextR A BL BR CC κ ω₀ j) (nextL A BL BR CC κ ω₀ j) ε
        * nextR A BL BR CC κ ω₀ j
      = gdrift A BL BR CC κ ε ω₀ j := rfl
  linear_combination
    ((A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
      * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
          (restrict ω₀.2.2.2.2 j (le_of_lt hj))) * hD
    + (-((A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
        * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
            (restrict ω₀.2.2.2.2 j (le_of_lt hj))
        * gdrift A BL BR CC κ ε ω₀ j)) * hprob

/-- Conditional second-moment identity on every atom. -/
theorem race_hvar (hε : 0 < ε) {j : ℕ} (hj : j < κ)
    (ω₀ : RΩ A BL BR CC κ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω₀),
      RP A BL BR CC κ ε ω * (mgX A BL BR CC κ ε j ω) ^ 2
      = mgV A BL BR CC κ ε j ω₀
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
      RP A BL BR CC κ ε ω * (mgX A BL BR CC κ ε j ω) ^ 2
      = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
        * (coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
            (restrict ω₀.2.2.2.2 j (le_of_lt hj))
          * (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
                (restrict ω₀.2.2.2.2 j (le_of_lt hj)) true
              * (nextL A BL BR CC κ ω₀ j
                  - gdrift A BL BR CC κ ε ω₀ j) ^ 2
            + coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε) j
                (restrict ω₀.2.2.2.2 j (le_of_lt hj)) false
              * (-nextR A BL BR CC κ ω₀ j
                  - gdrift A BL BR CC κ ε ω₀ j) ^ 2)) := by
    rw [sum_ghist_atom A BL BR CC κ
      (fun ω => RP A BL BR CC κ ε ω * (mgX A BL BR CC κ ε j ω) ^ 2)
      (le_of_lt hj) ω₀]
    have hterm : ∀ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
        ∀ i : Fin κ, (i : ℕ) < j → c i = ω₀.2.2.2.2 i),
        RP A BL BR CC κ ε (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
          * (mgX A BL BR CC κ ε j
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)) ^ 2
        = (A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * CC.P ω₀.2.2.2.1)))
          * (coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c
            * (if c ⟨j, hj⟩ then
                (nextL A BL BR CC κ ω₀ j
                  - gdrift A BL BR CC κ ε ω₀ j) ^ 2
               else
                (-nextR A BL BR CC κ ω₀ j
                  - gdrift A BL BR CC κ ε ω₀ j) ^ 2)) := by
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
      have hd : gdrift A BL BR CC κ ε
          (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
          = gdrift A BL BR CC κ ε ω₀ j :=
        gdrift_congr A BL BR CC κ ε _ ω₀ rfl rfl hc.2
      have hmgx : mgX A BL BR CC κ ε j
          (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)
          = (if c ⟨j, hj⟩ then nextL A BL BR CC κ ω₀ j
             else -nextR A BL BR CC κ ω₀ j)
            - gdrift A BL BR CC κ ε ω₀ j := by
        unfold mgX
        rw [dif_pos hj]
        show (if c ⟨j, hj⟩ then
            nextL A BL BR CC κ (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j
          else
            -nextR A BL BR CC κ
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j)
            - gdrift A BL BR CC κ ε
                (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c) j = _
        rw [hnl, hnr, hd]
      show A.P ω₀.1 * (BL.P ω₀.2.1 * (BR.P ω₀.2.2.1 * (CC.P ω₀.2.2.2.1
          * coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c)))
          * (mgX A BL BR CC κ ε j
              (ω₀.1, ω₀.2.1, ω₀.2.2.1, ω₀.2.2.2.1, c)) ^ 2 = _
      rw [hmgx]
      by_cases hb : c ⟨j, hj⟩
      · rw [if_pos hb, if_pos hb]
        ring
      · rw [if_neg hb, if_neg hb]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      coinWt_cond_step hsum hj ω₀.2.2.2.2
        ((nextL A BL BR CC κ ω₀ j - gdrift A BL BR CC κ ε ω₀ j) ^ 2)
        ((-nextR A BL BR CC κ ω₀ j - gdrift A BL BR CC κ ε ω₀ j) ^ 2)]
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
  unfold mgV
  rw [if_pos hj, hWt, hWf]
  ring

/-- The imbalance increments form a discrete martingale for the
full-reveal filtration, with conditional second moments `mgV`. -/
theorem race_martingale (hε : 0 < ε) :
    IsDiscreteMartingale (RP A BL BR CC κ ε) κ (ghist A BL BR CC κ)
      (mgX A BL BR CC κ ε) (mgV A BL BR CC κ ε) := by
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
    unfold mgX
    rw [dif_pos hjN, dif_pos hjN,
      nextL_congr A BL BR CC κ ω ω' h2 (fun i hi => hcoins i (by omega)),
      nextR_congr A BL BR CC κ ω ω' h3 (fun i hi => hcoins i (by omega)),
      gdrift_congr A BL BR CC κ ε ω ω' h2 h3
        (fun i hi => hcoins i (by omega)),
      hcoins ⟨j, hjN⟩ (Nat.lt_succ_self j)]
  · intro j hjN ω ω' h
    rw [ghist_iff] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [min_eq_left (by omega : j ≤ κ)] at h5
    have hcoins : ∀ i : Fin κ, (i : ℕ) < j
        → ω.2.2.2.2 i = ω'.2.2.2.2 i := coinCode_inj h5
    unfold mgV
    rw [if_pos hjN, if_pos hjN,
      nextL_congr A BL BR CC κ ω ω' h2 hcoins,
      nextR_congr A BL BR CC κ ω ω' h3 hcoins,
      gdrift_congr A BL BR CC κ ε ω ω' h2 h3 hcoins]
  · exact fun j hjN ω₀ => race_hmart A BL BR CC κ ε hε hjN ω₀
  · exact fun j hjN ω₀ => race_hvar A BL BR CC κ ε hε hjN ω₀

theorem gdrift_abs_le (hε : 0 < ε) (ω : RΩ A BL BR CC κ) (j : ℕ) :
    |gdrift A BL BR CC κ ε ω j| ≤ ε := by
  unfold gdrift
  exact probL_mul_abs_le ε hε (BL.sizeN_nonneg (le_refl 0) _ _)
    (BR.sizeN_nonneg (le_refl 0) _ _)

theorem mgX_abs_le (hε : 0 < ε) (hcB : 0 ≤ cB) (j : ℕ)
    (ω : RΩ A BL BR CC κ) :
    |mgX A BL BR CC κ ε j ω| ≤ cB + ε := by
  unfold mgX
  by_cases hj : j < κ
  · rw [dif_pos hj]
    have hd := gdrift_abs_le A BL BR CC κ ε hε ω j
    rw [abs_le] at hd
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
      constructor <;> linarith
    · rw [if_neg hb, abs_le]
      constructor <;> linarith
  · rw [dif_neg hj, abs_zero]
    linarith [hε.le]

theorem mgV_nonneg (hε : 0 < ε) (j : ℕ) (ω : RΩ A BL BR CC κ) :
    0 ≤ mgV A BL BR CC κ ε j ω := by
  unfold mgV
  by_cases hj : j < κ
  · rw [if_pos hj]
    exact add_nonneg (mul_nonneg (probL_pos hε).le (sq_nonneg _))
      (mul_nonneg (probL_pos hε).le (sq_nonneg _))
  · rw [if_neg hj]

theorem mgV_le (hε : 0 < ε) (hcB : 0 ≤ cB) (j : ℕ)
    (ω : RΩ A BL BR CC κ) :
    mgV A BL BR CC κ ε j ω ≤ (cB + ε) ^ 2 := by
  unfold mgV
  by_cases hj : j < κ
  · rw [if_pos hj]
    have hd := gdrift_abs_le A BL BR CC κ ε hε ω j
    rw [abs_le] at hd
    have hnl0 : (0 : ℝ) ≤ nextL A BL BR CC κ ω j :=
      BL.sizeN_nonneg (le_refl 0) _ _
    have hnlB : nextL A BL BR CC κ ω j ≤ cB :=
      sizeN_le_cB BL hcB (cntL ω.2.2.2.2 j) ω.2.1
    have hnr0 : (0 : ℝ) ≤ nextR A BL BR CC κ ω j :=
      BR.sizeN_nonneg (le_refl 0) _ _
    have hnrB : nextR A BL BR CC κ ω j ≤ cB :=
      sizeN_le_cB BR hcB (cntR ω.2.2.2.2 j) ω.2.2.1
    have h1 : (nextL A BL BR CC κ ω j - gdrift A BL BR CC κ ε ω j) ^ 2
        ≤ (cB + ε) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    have h2 : (-nextR A BL BR CC κ ω j - gdrift A BL BR CC κ ε ω j) ^ 2
        ≤ (cB + ε) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    have hp := probL_add_probR (nextL A BL BR CC κ ω j)
      (nextR A BL BR CC κ ω j) ε hε
    calc probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
          * (nextL A BL BR CC κ ω j - gdrift A BL BR CC κ ε ω j) ^ 2
        + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
          * (-nextR A BL BR CC κ ω j - gdrift A BL BR CC κ ε ω j) ^ 2
        ≤ probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
            * (cB + ε) ^ 2
          + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
            * (cB + ε) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (probL_pos hε).le)
            (mul_le_mul_of_nonneg_left h2 (probL_pos hε).le)
      _ = (cB + ε) ^ 2 := by rw [← add_mul, hp, one_mul]
  · rw [if_neg hj]
    positivity

/-- The per-step conditional variance is at least `cLo'²` when both sides
carry a size window above the clamp `ε`. -/
theorem mgV_ge_window (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {cLo' : ℝ} (hεLo : ε ≤ cLo')
    (hLoL : ∀ (l : BL.Ω) (i : Fin BL.m), cLo' ≤ BL.size l i)
    (hLoR : ∀ (r : BR.Ω) (i : Fin BR.m), cLo' ≤ BR.size r i)
    {j : ℕ} (hj : j < κ) (ω : RΩ A BL BR CC κ) :
    cLo' ^ 2 ≤ mgV A BL BR CC κ ε j ω := by
  have hidxL : cntL ω.2.2.2.2 j < BL.m :=
    lt_of_le_of_lt (cntL_le ω.2.2.2.2 (le_of_lt hj))
      (lt_of_lt_of_le hj hκL)
  have hidxR : cntR ω.2.2.2.2 j < BR.m :=
    lt_of_le_of_lt (cntR_le ω.2.2.2.2 (le_of_lt hj))
      (lt_of_lt_of_le hj hκR)
  have hnl : cLo' ≤ nextL A BL BR CC κ ω j := by
    show cLo' ≤ BL.sizeN (cntL ω.2.2.2.2 j) ω.2.1
    unfold ChunkSystemB.sizeN
    rw [dif_pos hidxL]
    exact hLoL ω.2.1 ⟨_, hidxL⟩
  have hnr : cLo' ≤ nextR A BL BR CC κ ω j := by
    show cLo' ≤ BR.sizeN (cntR ω.2.2.2.2 j) ω.2.2.1
    unfold ChunkSystemB.sizeN
    rw [dif_pos hidxR]
    exact hLoR ω.2.2.1 ⟨_, hidxR⟩
  have hεnl : ε ≤ nextL A BL BR CC κ ω j := le_trans hεLo hnl
  have hεnr : ε ≤ nextR A BL BR CC κ ω j := le_trans hεLo hnr
  have hab : nextL A BL BR CC κ ω j + nextR A BL BR CC κ ω j ≠ 0 := by
    have := hε
    intro hcon
    nlinarith
  have hab' : nextR A BL BR CC κ ω j + nextL A BL BR CC κ ω j ≠ 0 := by
    have := hε
    intro hcon
    nlinarith
  have hd0 : gdrift A BL BR CC κ ε ω j = 0 := by
    unfold gdrift probL
    rw [max_eq_left hεnl, max_eq_left hεnr]
    field_simp
    ring
  have key : probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
        * (nextL A BL BR CC κ ω j - 0) ^ 2
      + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
        * (-nextR A BL BR CC κ ω j - 0) ^ 2
      = nextL A BL BR CC κ ω j * nextR A BL BR CC κ ω j := by
    unfold probL
    rw [max_eq_left hεnl, max_eq_left hεnr]
    field_simp
    ring
  unfold mgV
  rw [if_pos hj, hd0, key]
  have hc0 : (0 : ℝ) ≤ cLo' := le_trans hε.le hεLo
  nlinarith

/-- Total conditional variance bounds. -/
theorem mgV_total_le (hε : 0 < ε) (hcB : 0 ≤ cB) (ω : RΩ A BL BR CC κ) :
    ∑ j ∈ Finset.range κ, mgV A BL BR CC κ ε j ω
      ≤ (κ : ℝ) * (cB + ε) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun j _ =>
    mgV_le A BL BR CC κ ε hε hcB j ω) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem mgV_total_ge (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {cLo' : ℝ} (hεLo : ε ≤ cLo')
    (hLoL : ∀ (l : BL.Ω) (i : Fin BL.m), cLo' ≤ BL.size l i)
    (hLoR : ∀ (r : BR.Ω) (i : Fin BR.m), cLo' ≤ BR.size r i)
    (ω : RΩ A BL BR CC κ) :
    (κ : ℝ) * cLo' ^ 2 ≤ ∑ j ∈ Finset.range κ, mgV A BL BR CC κ ε j ω := by
  calc (κ : ℝ) * cLo' ^ 2 = ∑ _j ∈ Finset.range κ, cLo' ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range κ, mgV A BL BR CC κ ε j ω := by
        refine Finset.sum_le_sum fun j hjm => ?_
        rw [Finset.mem_range] at hjm
        exact mgV_ge_window A BL BR CC κ ε hε hκL hκR hεLo hLoL hLoR hjm ω

/-- The martingale sum is the imbalance minus the accumulated drift. -/
theorem race_mgSum_eq (ω : RΩ A BL BR CC κ) :
    mgSum (mgX A BL BR CC κ ε) κ ω
      = (sumL A BL BR CC κ ω - sumR A BL BR CC κ ω)
        - ∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j := by
  unfold mgSum
  have h1 : ∀ j : Fin κ, mgX A BL BR CC κ ε (j : ℕ) ω
      = (if ω.2.2.2.2 j then nextL A BL BR CC κ ω (j : ℕ)
         else -nextR A BL BR CC κ ω (j : ℕ))
        - gdrift A BL BR CC κ ε ω (j : ℕ) := by
    intro j
    unfold mgX
    rw [dif_pos j.isLt]
  rw [← Fin.sum_univ_eq_sum_range (fun j => mgX A BL BR CC κ ε j ω) κ,
    Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib]
  congr 1
  · unfold sumL sumR
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hb : ω.2.2.2.2 j
    · rw [if_pos hb, if_pos hb, if_pos hb]
      ring
    · rw [if_neg hb, if_neg hb, if_neg hb]
      ring
  · exact Fin.sum_univ_eq_sum_range
      (fun j => gdrift A BL BR CC κ ε ω j) κ

theorem race_mgSum_abs (hε : 0 < ε) (ω : RΩ A BL BR CC κ) :
    |mgSum (mgX A BL BR CC κ ε) κ ω|
      ≤ |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| + (κ : ℝ) * ε := by
  rw [race_mgSum_eq]
  have hdr : |∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j|
      ≤ (κ : ℝ) * ε := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun j _ =>
      gdrift_abs_le A BL BR CC κ ε hε ω j) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc |(sumL A BL BR CC κ ω - sumR A BL BR CC κ ω)
        - ∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j|
      ≤ |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|
        + |∑ j ∈ Finset.range κ, gdrift A BL BR CC κ ε ω j| :=
        abs_sub _ _
    _ ≤ |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| + (κ : ℝ) * ε := by
        linarith

/-- The expected martingale magnitude is dominated by the expected
imbalance plus the drift clamp. -/
theorem race_gain_reduce (hε : 0 < ε) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |mgSum (mgX A BL BR CC κ ε) κ ω|
      ≤ (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
        + (κ : ℝ) * ε := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * |mgSum (mgX A BL BR CC κ ε) κ ω|
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|
            + (κ : ℝ) * ε) :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
      (race_mgSum_abs A BL BR CC κ ε hε ω)
      (RP_pos A BL BR CC κ ε hε ω).le
  refine le_trans h1 (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun ω _ =>
    show RP A BL BR CC κ ε ω
        * (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| + (κ : ℝ) * ε)
      = RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|
        + RP A BL BR CC κ ε ω * ((κ : ℝ) * ε) from by ring),
    Finset.sum_add_distrib,
    sum_P_mul (RP A BL BR CC κ ε) hRPs ((κ : ℝ) * ε)
      (fun ω => RP A BL BR CC κ ε ω * ((κ : ℝ) * ε))
      (fun ω => by ring)]

end GainSetup

end Race

end KServer


