-- Prove2me | Definitions.Def_KServer_race_pad
-- name    : KServer_race_pad
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T20:01:13.378971+00:00
-- url     : https://prove2.me/theorems/b0e30588-95b6-4910-9be2-951dee925862
-- title:
--   The padded imbalance martingale
-- statement:
--   The padded imbalance martingale of the coin race. The race space is extended by $\kappa$ auxiliary fair coins; on steps where both sides' next chunk sizes carry the floor $c_{Lo}'$ (the in-window steps) the padded increment is the real centered imbalance increment, and on out-of-window steps it is a synthetic $\pm c_{Lo}'$ fair coin. The padded increments form a discrete martingale for the extended full-reveal filtration, with conditional second moments equal to the real ones in-window and exactly $c_{Lo}'^2$ off-window; hence the total conditional variance lies pathwise in $[\kappa c_{Lo}'^2, \kappa(c_B+\varepsilon)^2]$ with NO window hypothesis on the systems. The padded martingale sum differs from the real imbalance-minus-drift only on out-of-window steps:
--   $$\big|S^{pad}_\kappa - S^{mg}_\kappa\big| \le (c_B+\varepsilon+c_{Lo}')\, N_{bad},$$
--   where $N_{bad}$ counts the out-of-window coin steps. Consequently the padded expected magnitude is dominated by $\mathbb{E}|S_L - S_R| + \kappa\varepsilon + (c_B+\varepsilon+c_{Lo}')\,\mathbb{E}[N_{bad}]$. Combined with the anti-concentration inequality this lower-bounds the expected race imbalance assuming only a bound on the expected number of bad steps — which the grid-regridded systems supply via Chebyshev — rather than a pointwise size window.
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
import Definitions.Def_KServer_discrete_martingale

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section PadSpace

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ) (cLo' : ℝ)

open Classical

/-- The padded race space: the race outcomes together with `κ` auxiliary
fair coins. -/
abbrev PΩ : Type _ := RΩ A BL BR CC κ × (Fin κ → Bool)

/-- The padded measure: product with fair coins. -/
noncomputable def PP (p : PΩ A BL BR CC κ) : ℝ :=
  RP A BL BR CC κ ε p.1 * ((1 : ℝ) / 2) ^ κ

theorem PP_pos (hε : 0 < ε) (p : PΩ A BL BR CC κ) :
    0 < PP A BL BR CC κ ε p :=
  mul_pos (RP_pos A BL BR CC κ ε hε p.1) (by positivity)

theorem PP_sum (hε : 0 < ε) :
    ∑ p : PΩ A BL BR CC κ, PP A BL BR CC κ ε p = 1 := by
  show ∑ p : RΩ A BL BR CC κ × (Fin κ → Bool),
    RP A BL BR CC κ ε p.1 * ((1 : ℝ) / 2) ^ κ = 1
  rw [Fintype.sum_prod_type]
  have h1 : ∀ ω : RΩ A BL BR CC κ,
      ∑ _b : Fin κ → Bool, RP A BL BR CC κ ε ω * ((1 : ℝ) / 2) ^ κ
        = RP A BL BR CC κ ε ω := by
    intro ω
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← mul_assoc, mul_comm ((2 : ℝ) ^ κ), mul_assoc,
      div_pow, one_pow, mul_one_div, div_self (by positivity), mul_one]
  rw [Finset.sum_congr rfl fun ω _ => h1 ω]
  exact RP_sum A BL BR CC κ ε hε

open Classical in
/-- The in-window predicate: both sides' next sizes carry the floor. -/
noncomputable def windowAt (ω : RΩ A BL BR CC κ) (j : ℕ) : Prop :=
  cLo' ≤ nextL A BL BR CC κ ω j ∧ cLo' ≤ nextR A BL BR CC κ ω j

theorem windowAt_congr (ω ω' : RΩ A BL BR CC κ) {j : ℕ}
    (hl : ω.2.1 = ω'.2.1) (hr : ω.2.2.1 = ω'.2.2.1)
    (hc : ∀ i : Fin κ, (i : ℕ) < j → ω.2.2.2.2 i = ω'.2.2.2.2 i) :
    windowAt A BL BR CC κ cLo' ω j ↔ windowAt A BL BR CC κ cLo' ω' j := by
  unfold windowAt
  rw [nextL_congr A BL BR CC κ ω ω' hl hc,
    nextR_congr A BL BR CC κ ω ω' hr hc]

/-- The padded filtration. -/
noncomputable def phist (j : ℕ) (p : PΩ A BL BR CC κ) : ℕ :=
  Nat.pair (ghist A BL BR CC κ j p.1) (coinCode κ p.2 (min j κ))

theorem phist_iff (j : ℕ) (p p' : PΩ A BL BR CC κ) :
    phist A BL BR CC κ j p = phist A BL BR CC κ j p'
      ↔ ghist A BL BR CC κ j p.1 = ghist A BL BR CC κ j p'.1
        ∧ coinCode κ p.2 (min j κ) = coinCode κ p'.2 (min j κ) := by
  unfold phist
  rw [Nat.pair_eq_pair]

open Classical in
/-- The padded increments: real centered increments in-window, synthetic
`±cLo'` fair coins out of window. -/
noncomputable def pX (j : ℕ) (p : PΩ A BL BR CC κ) : ℝ :=
  if h : j < κ then
    (if windowAt A BL BR CC κ cLo' p.1 j then mgX A BL BR CC κ ε j p.1
     else (if p.2 ⟨j, h⟩ then cLo' else -cLo'))
  else 0

open Classical in
/-- The padded conditional second moments. -/
noncomputable def pV (j : ℕ) (p : PΩ A BL BR CC κ) : ℝ :=
  if j < κ then
    (if windowAt A BL BR CC κ cLo' p.1 j then mgV A BL BR CC κ ε j p.1
     else cLo' ^ 2)
  else 0

/-- Atom collapse: a `phist`-atom is the product of a `ghist`-atom and a
coin-prefix atom. -/
theorem sum_phist_atom (g : PΩ A BL BR CC κ → ℝ) {j : ℕ}
    (p₀ : PΩ A BL BR CC κ) :
    ∑ p ∈ Finset.univ.filter (fun p : PΩ A BL BR CC κ =>
        phist A BL BR CC κ j p = phist A BL BR CC κ j p₀), g p
      = ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
          ∑ b ∈ Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ)),
            g (ω, b) := by
  have hset : Finset.univ.filter (fun p : PΩ A BL BR CC κ =>
      phist A BL BR CC κ j p = phist A BL BR CC κ j p₀)
      = (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1)) ×ˢ
        (Finset.univ.filter (fun b : Fin κ → Bool =>
          coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and, phist_iff]
  rw [hset, Finset.sum_product]

theorem windowAt_of_ghist {j : ℕ} (hj : j ≤ κ) (ω ω' : RΩ A BL BR CC κ)
    (h : ghist A BL BR CC κ j ω = ghist A BL BR CC κ j ω') :
    windowAt A BL BR CC κ cLo' ω j ↔ windowAt A BL BR CC κ cLo' ω' j := by
  rw [ghist_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [min_eq_left hj] at h5
  exact windowAt_congr A BL BR CC κ cLo' ω ω' h2 h3 (coinCode_inj h5)

/-- Conditional mean zero of the padded increments. -/
theorem pad_hmart (hε : 0 < ε) {j : ℕ} (hj : j < κ)
    (p₀ : PΩ A BL BR CC κ) :
    ∑ p ∈ Finset.univ.filter (fun p : PΩ A BL BR CC κ =>
        phist A BL BR CC κ j p = phist A BL BR CC κ j p₀),
      PP A BL BR CC κ ε p * pX A BL BR CC κ ε cLo' j p = 0 := by
  rw [sum_phist_atom A BL BR CC κ
    (fun p => PP A BL BR CC κ ε p * pX A BL BR CC κ ε cLo' j p) p₀]
  by_cases hw : windowAt A BL BR CC κ cLo' p₀.1 j
  · have hterm : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
        (∑ b ∈ Finset.univ.filter (fun b : Fin κ → Bool =>
          coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ)),
          PP A BL BR CC κ ε (ω, b) * pX A BL BR CC κ ε cLo' j (ω, b))
        = ((Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
          * ((1 : ℝ) / 2) ^ κ
          * (RP A BL BR CC κ ε ω * mgX A BL BR CC κ ε j ω) := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      have hwω : windowAt A BL BR CC κ cLo' ω j :=
        (windowAt_of_ghist A BL BR CC κ cLo' (le_of_lt hj) ω p₀.1
          hω.2).mpr hw
      have hval : ∀ b : Fin κ → Bool,
          PP A BL BR CC κ ε (ω, b) * pX A BL BR CC κ ε cLo' j (ω, b)
          = RP A BL BR CC κ ε ω * ((1 : ℝ) / 2) ^ κ
            * mgX A BL BR CC κ ε j ω := by
        intro b
        unfold PP pX
        rw [dif_pos hj, if_pos hwω]
      rw [Finset.sum_congr rfl fun b _ => hval b, Finset.sum_const,
        nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hterm]
    have hfin : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
        ((Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
          * ((1 : ℝ) / 2) ^ κ
          * (RP A BL BR CC κ ε ω * mgX A BL BR CC κ ε j ω)
        = ((Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
          * ((1 : ℝ) / 2) ^ κ
          * ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
              ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
              RP A BL BR CC κ ε ω * mgX A BL BR CC κ ε j ω := by
      rw [Finset.mul_sum]
    rw [hfin, race_hmart A BL BR CC κ ε hε hj p₀.1, mul_zero]
  · -- out of window: the synthetic fair coin integrates to zero
    have hmin : min j κ = j := min_eq_left (le_of_lt hj)
    have hfilter : (Finset.univ.filter (fun b : Fin κ → Bool =>
        coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ)))
        = Finset.univ.filter (fun b : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j → b i = p₀.2 i) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmin]
      exact ⟨fun h => coinCode_inj h, fun h => coinCode_congr h⟩
    have hWhalf : ∀ b : Fin κ → Bool,
        coinWt (fun (_ : ℕ) (_ : Fin _ → Bool) (_ : Bool) => (1 : ℝ) / 2) b
          = ((1 : ℝ) / 2) ^ κ := by
      intro b
      unfold coinWt
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine Finset.sum_eq_zero fun ω hω => ?_
    rw [Finset.mem_filter] at hω
    have hwω : ¬ windowAt A BL BR CC κ cLo' ω j := fun hc =>
      hw ((windowAt_of_ghist A BL BR CC κ cLo' (le_of_lt hj) ω p₀.1
        hω.2).mp hc)
    have hterm2 : ∀ b ∈ (Finset.univ.filter (fun b : Fin κ → Bool =>
        coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))),
        PP A BL BR CC κ ε (ω, b) * pX A BL BR CC κ ε cLo' j (ω, b)
        = RP A BL BR CC κ ε ω
          * (coinWt (fun (_ : ℕ) (_ : Fin _ → Bool) (_ : Bool) =>
              (1 : ℝ) / 2) b
            * (if b ⟨j, hj⟩ then cLo' else -cLo')) := by
      intro b _
      unfold PP pX
      rw [dif_pos hj, if_neg hwω, hWhalf b]
      ring
    rw [Finset.sum_congr rfl hterm2, ← Finset.mul_sum, hfilter,
      coinWt_cond_step (fun _ _ => by norm_num) hj p₀.2 cLo' (-cLo')]
    norm_num

/-- Conditional second-moment identity of the padded increments. -/
theorem pad_hvar (hε : 0 < ε) {j : ℕ} (hj : j < κ)
    (p₀ : PΩ A BL BR CC κ) :
    ∑ p ∈ Finset.univ.filter (fun p : PΩ A BL BR CC κ =>
        phist A BL BR CC κ j p = phist A BL BR CC κ j p₀),
      PP A BL BR CC κ ε p * (pX A BL BR CC κ ε cLo' j p) ^ 2
      = pV A BL BR CC κ ε cLo' j p₀
        * ∑ p ∈ Finset.univ.filter (fun p : PΩ A BL BR CC κ =>
            phist A BL BR CC κ j p = phist A BL BR CC κ j p₀),
          PP A BL BR CC κ ε p := by
  rw [sum_phist_atom A BL BR CC κ
    (fun p => PP A BL BR CC κ ε p * (pX A BL BR CC κ ε cLo' j p) ^ 2) p₀,
    sum_phist_atom A BL BR CC κ (fun p => PP A BL BR CC κ ε p) p₀]
  have hPPval : ∀ (ω : RΩ A BL BR CC κ) (b : Fin κ → Bool),
      PP A BL BR CC κ ε (ω, b)
      = RP A BL BR CC κ ε ω * ((1 : ℝ) / 2) ^ κ := fun ω b => rfl
  have hMcollapse : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
      ∑ b ∈ Finset.univ.filter (fun b : Fin κ → Bool =>
        coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ)),
        PP A BL BR CC κ ε (ω, b)
      = ((Finset.univ.filter (fun b : Fin κ → Bool =>
          coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
        * ((1 : ℝ) / 2) ^ κ
        * ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
            ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
            RP A BL BR CC κ ε ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_congr rfl fun b _ => hPPval ω b, Finset.sum_const,
      nsmul_eq_mul]
    ring
  by_cases hw : windowAt A BL BR CC κ cLo' p₀.1 j
  · have hterm : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
        (∑ b ∈ Finset.univ.filter (fun b : Fin κ → Bool =>
          coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ)),
          PP A BL BR CC κ ε (ω, b)
            * (pX A BL BR CC κ ε cLo' j (ω, b)) ^ 2)
        = ((Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
          * ((1 : ℝ) / 2) ^ κ
          * (RP A BL BR CC κ ε ω * (mgX A BL BR CC κ ε j ω) ^ 2) := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      have hwω : windowAt A BL BR CC κ cLo' ω j :=
        (windowAt_of_ghist A BL BR CC κ cLo' (le_of_lt hj) ω p₀.1
          hω.2).mpr hw
      have hval : ∀ b : Fin κ → Bool,
          PP A BL BR CC κ ε (ω, b)
            * (pX A BL BR CC κ ε cLo' j (ω, b)) ^ 2
          = RP A BL BR CC κ ε ω * ((1 : ℝ) / 2) ^ κ
            * (mgX A BL BR CC κ ε j ω) ^ 2 := by
        intro b
        unfold PP pX
        rw [dif_pos hj, if_pos hwω]
      rw [Finset.sum_congr rfl fun b _ => hval b, Finset.sum_const,
        nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hterm, hMcollapse]
    have hpv : pV A BL BR CC κ ε cLo' j p₀ = mgV A BL BR CC κ ε j p₀.1 := by
      unfold pV
      rw [if_pos hj, if_pos hw]
    rw [hpv]
    calc ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
          ((Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
            * ((1 : ℝ) / 2) ^ κ
            * (RP A BL BR CC κ ε ω * (mgX A BL BR CC κ ε j ω) ^ 2)
        = ((Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
            * ((1 : ℝ) / 2) ^ κ
            * ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
                ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
                RP A BL BR CC κ ε ω * (mgX A BL BR CC κ ε j ω) ^ 2 := by
          rw [Finset.mul_sum]
      _ = ((Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ))).card : ℝ)
            * ((1 : ℝ) / 2) ^ κ
            * (mgV A BL BR CC κ ε j p₀.1
              * ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
                  ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
                  RP A BL BR CC κ ε ω) := by
          rw [race_hvar A BL BR CC κ ε hε hj p₀.1]
      _ = mgV A BL BR CC κ ε j p₀.1
            * (((Finset.univ.filter (fun b : Fin κ → Bool =>
                coinCode κ b (min j κ)
                  = coinCode κ p₀.2 (min j κ))).card : ℝ)
              * ((1 : ℝ) / 2) ^ κ
              * ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
                  ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
                  RP A BL BR CC κ ε ω) := by
          ring
  · have hterm : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        ghist A BL BR CC κ j ω = ghist A BL BR CC κ j p₀.1),
        (∑ b ∈ Finset.univ.filter (fun b : Fin κ → Bool =>
          coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ)),
          PP A BL BR CC κ ε (ω, b)
            * (pX A BL BR CC κ ε cLo' j (ω, b)) ^ 2)
        = ∑ b ∈ Finset.univ.filter (fun b : Fin κ → Bool =>
            coinCode κ b (min j κ) = coinCode κ p₀.2 (min j κ)),
            cLo' ^ 2 * PP A BL BR CC κ ε (ω, b) := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      have hwω : ¬ windowAt A BL BR CC κ cLo' ω j := fun hc =>
        hw ((windowAt_of_ghist A BL BR CC κ cLo' (le_of_lt hj) ω p₀.1
          hω.2).mp hc)
      refine Finset.sum_congr rfl fun b _ => ?_
      have hval : pX A BL BR CC κ ε cLo' j (ω, b)
          = if b ⟨j, hj⟩ then cLo' else -cLo' := by
        unfold pX
        rw [dif_pos hj, if_neg hwω]
      rw [hval]
      by_cases hb : b ⟨j, hj⟩
      · rw [if_pos hb]
        ring
      · rw [if_neg hb]
        ring
    rw [Finset.sum_congr rfl hterm]
    have hpv : pV A BL BR CC κ ε cLo' j p₀ = cLo' ^ 2 := by
      unfold pV
      rw [if_pos hj, if_neg hw]
    rw [hpv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum]

/-- The padded increments form a discrete martingale. -/
theorem pad_martingale (hε : 0 < ε) :
    IsDiscreteMartingale (PP A BL BR CC κ ε) κ (phist A BL BR CC κ)
      (pX A BL BR CC κ ε cLo') (pV A BL BR CC κ ε cLo') := by
  have HM := race_martingale A BL BR CC κ ε hε
  refine ⟨fun p => (PP_pos A BL BR CC κ ε hε p).le, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij p p' h
    rw [phist_iff] at h ⊢
    obtain ⟨hg, hb⟩ := h
    refine ⟨HM.href i j hij _ _ hg, ?_⟩
    exact coinCode_congr fun i' hi' => coinCode_inj hb i'
      (lt_of_lt_of_le hi' (min_le_min hij (le_refl κ)))
  · intro j hjN p p' h
    rw [phist_iff] at h
    obtain ⟨hg, hb⟩ := h
    have hgj : ghist A BL BR CC κ j p.1 = ghist A BL BR CC κ j p'.1 :=
      HM.href j (j + 1) (by omega) _ _ hg
    have hwiff := windowAt_of_ghist A BL BR CC κ cLo' (le_of_lt hjN)
      p.1 p'.1 hgj
    have hmgx := HM.hadapt j hjN _ _ hg
    rw [min_eq_left (by omega : j + 1 ≤ κ)] at hb
    have hbj : p.2 ⟨j, hjN⟩ = p'.2 ⟨j, hjN⟩ :=
      coinCode_inj hb ⟨j, hjN⟩ (Nat.lt_succ_self j)
    unfold pX
    rw [dif_pos hjN, dif_pos hjN]
    by_cases hwp : windowAt A BL BR CC κ cLo' p.1 j
    · rw [if_pos hwp, if_pos (hwiff.mp hwp), hmgx]
    · rw [if_neg hwp, if_neg (fun hc => hwp (hwiff.mpr hc)), hbj]
  · intro j hjN p p' h
    rw [phist_iff] at h
    obtain ⟨hg, hb⟩ := h
    have hwiff := windowAt_of_ghist A BL BR CC κ cLo' (le_of_lt hjN)
      p.1 p'.1 hg
    unfold pV
    rw [if_pos hjN, if_pos hjN]
    by_cases hwp : windowAt A BL BR CC κ cLo' p.1 j
    · rw [if_pos hwp, if_pos (hwiff.mp hwp), HM.hvmeas j hjN _ _ hg]
    · rw [if_neg hwp, if_neg (fun hc => hwp (hwiff.mpr hc))]
  · exact fun j hjN p₀ => pad_hmart A BL BR CC κ ε cLo' hε hjN p₀
  · exact fun j hjN p₀ => pad_hvar A BL BR CC κ ε cLo' hε hjN p₀

theorem pX_abs_le (hε : 0 < ε) (hcB : 0 ≤ cB) (hLo0 : 0 ≤ cLo')
    (hLocB : cLo' ≤ cB + ε) (j : ℕ) (p : PΩ A BL BR CC κ) :
    |pX A BL BR CC κ ε cLo' j p| ≤ cB + ε := by
  unfold pX
  by_cases hj : j < κ
  · rw [dif_pos hj]
    by_cases hw : windowAt A BL BR CC κ cLo' p.1 j
    · rw [if_pos hw]
      exact mgX_abs_le A BL BR CC κ ε hε hcB j p.1
    · rw [if_neg hw]
      by_cases hb : p.2 ⟨j, hj⟩
      · rw [if_pos hb, abs_of_nonneg hLo0]
        exact hLocB
      · rw [if_neg hb, abs_neg, abs_of_nonneg hLo0]
        exact hLocB
  · rw [dif_neg hj, abs_zero]
    linarith [hε.le]

theorem pV_nonneg (hε : 0 < ε) (j : ℕ) (p : PΩ A BL BR CC κ) :
    0 ≤ pV A BL BR CC κ ε cLo' j p := by
  unfold pV
  by_cases hj : j < κ
  · rw [if_pos hj]
    by_cases hw : windowAt A BL BR CC κ cLo' p.1 j
    · rw [if_pos hw]
      exact mgV_nonneg A BL BR CC κ ε hε j p.1
    · rw [if_neg hw]
      exact sq_nonneg _
  · rw [if_neg hj]

theorem pV_total_le (hε : 0 < ε) (hcB : 0 ≤ cB) (hLo0 : 0 ≤ cLo')
    (hLocB : cLo' ≤ cB + ε) (p : PΩ A BL BR CC κ) :
    ∑ j ∈ Finset.range κ, pV A BL BR CC κ ε cLo' j p
      ≤ (κ : ℝ) * (cB + ε) ^ 2 := by
  have h1 : ∀ j ∈ Finset.range κ,
      pV A BL BR CC κ ε cLo' j p ≤ (cB + ε) ^ 2 := by
    intro j hjm
    rw [Finset.mem_range] at hjm
    unfold pV
    rw [if_pos hjm]
    by_cases hw : windowAt A BL BR CC κ cLo' p.1 j
    · rw [if_pos hw]
      exact mgV_le A BL BR CC κ ε hε hcB j p.1
    · rw [if_neg hw]
      exact pow_le_pow_left₀ hLo0 hLocB 2
  refine le_trans (Finset.sum_le_sum h1) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The per-step conditional variance floor, in-window form. -/
theorem mgV_ge_at (hε : 0 < ε) (hεLo : ε ≤ cLo') {j : ℕ} (hj : j < κ)
    (ω : RΩ A BL BR CC κ) (hwin : windowAt A BL BR CC κ cLo' ω j) :
    cLo' ^ 2 ≤ mgV A BL BR CC κ ε j ω := by
  obtain ⟨hnl, hnr⟩ := hwin
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

theorem pV_total_ge (hε : 0 < ε) (hεLo : ε ≤ cLo')
    (p : PΩ A BL BR CC κ) :
    (κ : ℝ) * cLo' ^ 2
      ≤ ∑ j ∈ Finset.range κ, pV A BL BR CC κ ε cLo' j p := by
  calc (κ : ℝ) * cLo' ^ 2 = ∑ _j ∈ Finset.range κ, cLo' ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range κ, pV A BL BR CC κ ε cLo' j p := by
        refine Finset.sum_le_sum fun j hjm => ?_
        rw [Finset.mem_range] at hjm
        unfold pV
        rw [if_pos hjm]
        by_cases hw : windowAt A BL BR CC κ cLo' p.1 j
        · rw [if_pos hw]
          exact mgV_ge_at A BL BR CC κ ε cLo' hε hεLo hjm p.1 hw
        · rw [if_neg hw]

/-- The expected number of out-of-window coin steps. -/
noncomputable def Nbad (ω : RΩ A BL BR CC κ) : ℝ :=
  ∑ j ∈ Finset.range κ,
    if windowAt A BL BR CC κ cLo' ω j then (0 : ℝ) else 1

theorem Nbad_nonneg (ω : RΩ A BL BR CC κ) :
    0 ≤ Nbad A BL BR CC κ cLo' ω := by
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases hw : windowAt A BL BR CC κ cLo' ω j
  · rw [if_pos hw]
  · rw [if_neg hw]
    linarith

/-- The padded martingale sum differs from the real one only on
out-of-window steps. -/
theorem pad_mgSum_diff (hε : 0 < ε) (hcB : 0 ≤ cB) (hLo0 : 0 ≤ cLo')
    (p : PΩ A BL BR CC κ) :
    |mgSum (pX A BL BR CC κ ε cLo') κ p
        - mgSum (mgX A BL BR CC κ ε) κ p.1|
      ≤ (cB + ε + cLo') * Nbad A BL BR CC κ cLo' p.1 := by
  unfold mgSum
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h1 : ∀ j ∈ Finset.range κ,
      |pX A BL BR CC κ ε cLo' j p - mgX A BL BR CC κ ε j p.1|
      ≤ (if windowAt A BL BR CC κ cLo' p.1 j then (0 : ℝ)
         else cB + ε + cLo') := by
    intro j hjm
    rw [Finset.mem_range] at hjm
    by_cases hw : windowAt A BL BR CC κ cLo' p.1 j
    · rw [if_pos hw]
      have : pX A BL BR CC κ ε cLo' j p = mgX A BL BR CC κ ε j p.1 := by
        unfold pX
        rw [dif_pos hjm, if_pos hw]
      rw [this, sub_self, abs_zero]
    · rw [if_neg hw]
      have hx := mgX_abs_le A BL BR CC κ ε hε hcB j p.1
      rw [abs_le] at hx
      have hpx : pX A BL BR CC κ ε cLo' j p
          = (if p.2 ⟨j, hjm⟩ then cLo' else -cLo') := by
        unfold pX
        rw [dif_pos hjm, if_neg hw]
      rw [hpx]
      by_cases hb : p.2 ⟨j, hjm⟩
      · rw [if_pos hb, abs_le]
        constructor <;> linarith
      · rw [if_neg hb, abs_le]
        constructor <;> linarith
  refine le_trans (Finset.sum_le_sum h1) (le_of_eq ?_)
  unfold Nbad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hw : windowAt A BL BR CC κ cLo' p.1 j
  · rw [if_pos hw, if_pos hw, mul_zero]
  · rw [if_neg hw, if_neg hw, mul_one]

/-- Marginalizing a function of the race outcome over the auxiliary
coins. -/
theorem PP_marg (hε : 0 < ε) (f : RΩ A BL BR CC κ → ℝ) :
    ∑ p : PΩ A BL BR CC κ, PP A BL BR CC κ ε p * f p.1
      = ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * f ω := by
  show ∑ p : RΩ A BL BR CC κ × (Fin κ → Bool),
    RP A BL BR CC κ ε p.1 * ((1 : ℝ) / 2) ^ κ * f p.1 = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) =>
    show RP A BL BR CC κ ε (ω, y).1 * ((1 : ℝ) / 2) ^ κ * f (ω, y).1
      = RP A BL BR CC κ ε ω * ((1 : ℝ) / 2) ^ κ * f ω from rfl)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [show ((2 : ℝ) ^ κ) * (RP A BL BR CC κ ε ω * (1 / 2) ^ κ * f ω)
      = ((2 : ℝ) ^ κ * (1 / 2) ^ κ) * (RP A BL BR CC κ ε ω * f ω)
    from by ring, ← mul_pow]
  norm_num

/-- The padded expected magnitude is dominated by the real expected
imbalance plus the drift clamp and the bad-step correction. -/
theorem pad_gain_reduce (hε : 0 < ε) (hcB : 0 ≤ cB) (hLo0 : 0 ≤ cLo')
    {Nb : ℝ} (hNb : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * Nbad A BL BR CC κ cLo' ω ≤ Nb) :
    ∑ p : PΩ A BL BR CC κ, PP A BL BR CC κ ε p
        * |mgSum (pX A BL BR CC κ ε cLo') κ p|
      ≤ (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
        + (κ : ℝ) * ε + (cB + ε + cLo') * Nb := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have hpath : ∀ p : PΩ A BL BR CC κ,
      |mgSum (pX A BL BR CC κ ε cLo') κ p|
      ≤ |sumL A BL BR CC κ p.1 - sumR A BL BR CC κ p.1| + (κ : ℝ) * ε
        + (cB + ε + cLo') * Nbad A BL BR CC κ cLo' p.1 := by
    intro p
    have h1 := pad_mgSum_diff A BL BR CC κ ε cLo' hε hcB hLo0 p
    have h2 := race_mgSum_abs A BL BR CC κ ε hε p.1
    calc |mgSum (pX A BL BR CC κ ε cLo') κ p|
        = |mgSum (mgX A BL BR CC κ ε) κ p.1
            + (mgSum (pX A BL BR CC κ ε cLo') κ p
              - mgSum (mgX A BL BR CC κ ε) κ p.1)| := by
          congr 1
          ring
      _ ≤ |mgSum (mgX A BL BR CC κ ε) κ p.1|
            + |mgSum (pX A BL BR CC κ ε cLo') κ p
              - mgSum (mgX A BL BR CC κ ε) κ p.1| := abs_add_le _ _
      _ ≤ _ := by linarith
  have h3 : ∑ p : PΩ A BL BR CC κ, PP A BL BR CC κ ε p
      * |mgSum (pX A BL BR CC κ ε cLo') κ p|
      ≤ ∑ p : PΩ A BL BR CC κ, PP A BL BR CC κ ε p
          * (|sumL A BL BR CC κ p.1 - sumR A BL BR CC κ p.1|
            + (κ : ℝ) * ε
            + (cB + ε + cLo') * Nbad A BL BR CC κ cLo' p.1) :=
    Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hpath p)
      (PP_pos A BL BR CC κ ε hε p).le
  refine le_trans h3 ?_
  rw [PP_marg A BL BR CC κ ε hε
    (fun ω => |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|
      + (κ : ℝ) * ε + (cB + ε + cLo') * Nbad A BL BR CC κ cLo' ω)]
  have h4 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|
        + (κ : ℝ) * ε + (cB + ε + cLo') * Nbad A BL BR CC κ cLo' ω)
      = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
        + (κ : ℝ) * ε
        + (cB + ε + cLo') * ∑ ω : RΩ A BL BR CC κ,
            RP A BL BR CC κ ε ω * Nbad A BL BR CC κ cLo' ω := by
    rw [Finset.sum_congr rfl (fun ω _ =>
      show RP A BL BR CC κ ε ω
          * (|sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|
            + (κ : ℝ) * ε
            + (cB + ε + cLo') * Nbad A BL BR CC κ cLo' ω)
        = RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|
          + RP A BL BR CC κ ε ω * ((κ : ℝ) * ε)
          + (cB + ε + cLo')
            * (RP A BL BR CC κ ε ω * Nbad A BL BR CC κ cLo' ω)
        from by ring),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_P_mul (RP A BL BR CC κ ε) hRPs ((κ : ℝ) * ε)
        (fun ω => RP A BL BR CC κ ε ω * ((κ : ℝ) * ε))
        (fun ω => by ring),
      ← Finset.mul_sum]
  rw [h4]
  have hc0 : (0 : ℝ) ≤ cB + ε + cLo' := by linarith [hε.le]
  have h5 : (cB + ε + cLo') * ∑ ω : RΩ A BL BR CC κ,
      RP A BL BR CC κ ε ω * Nbad A BL BR CC κ cLo' ω
      ≤ (cB + ε + cLo') * Nb := mul_le_mul_of_nonneg_left hNb hc0
  linarith

end PadSpace

end Race

end KServer


