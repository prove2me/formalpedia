-- Prove2me | Definitions.Def_QMCLeafB_fc40
-- name    : QMCLeafB_fc40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:33:37.583626+00:00
-- url     : https://prove2.me/theorems/5b31078d-91a3-45a1-b72d-6c0ac716ecc0
-- title:
--   QMCLeafB fc40
-- statement:
--   # `Check_fc40_m1` — phase 40, member m1, direction d1 (`factor-check`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_eq38
import Definitions.Def_QMCLeafB_lm38
/-
# `Check_fc40_m1` — phase 40, member m1, direction d1 (`factor-check`)

**Charge.** Phase 40's closing move: *"the depth ceiling `rmax` enlarged to `1/n²` makes the standard
ellipsoid step satisfy the leaf's inequality EXACTLY. Verify the factor, re-discharge the run
parameters at the new constant, and assemble."*  m2/ph38's `Check_eq38_m2` measured the gap: after a
supporting cut at depth `ρ` the SAME normal ranks the body one round later at
`(1−ρ)/(N+ρ)·√σ'`, while the leaf allows `rmax·√σ'`; at the campaign's `rmax = 1/(4N)` the miss is
`4N(1−ρ)/(N+ρ) → 4`.

This file verifies the factor and attempts the re-discharge. **Verdict: the factor is right and
sharp, and the parameter re-discharge FAILS — decisively, at every `m`.**

* **§1 — the factor is exactly `4`, and `1/N` is the exact threshold.**  The closing inequality is a
  one-line identity with a *signed defect*:
  `1/N − (1−ρ)/(N+ρ) = ρ(N+1)/(N(N+ρ)) ≥ 0` for every `ρ ≥ 0` (`ratio_defect`, `ratio_le_inv`).
  Consequences, all machine-checked:
  * the phase note's hypothesis `ρ ≤ 1/N` is **not needed** — the inequality holds at EVERY depth, so
    the reuse cut is admissible at the new ceiling for free (`ratio_le_inv` vs `eq38_m2`'s
    `reuse_short_of_leaf`, which needed `ρ ≤ 1/(4N)` and got the WRONG direction);
  * `1/N` is the *least* ceiling that works, uniformly over legal depths (`ceiling_threshold`), and
    it is ATTAINED at `ρ = 0` (`ratio_eq_inv_iff`) — so the enlargement is exactly at the threshold,
    not comfortably above it;
  * the miss factor is `(1−ρ)/(N+ρ) ÷ (1/(4N)) ≤ 4` with equality **iff** `ρ = 0`
    (`miss_ratio_le_four`, `miss_ratio_eq_four`) — m2's "`→ 4`" is an equality at zero depth;
  * the new constant is exactly four times the old (`newRmax_eq_four_mul`);
  * **at the campaign's OWN ceiling the reuse ratio fits only from depth `3N/(4N+1) > 3/4`**
    (`reuse_needs_depth`), while the ledger allows `ρ ≤ 1/(4N) ≤ 1/8`: so at the banked parameters
    the reuse lane is dead at EVERY legal depth (`no_reuse_at_banked_params`), with the exact margin
    — the sharp form of `Eq38M2.reuse_short_of_leaf`.
* **§2 — the closing move WORKS at one round** (the positive half).  Reusing m2's
  `supporting_normal_ratio`/`supporting_ratio_attained` and m5's `recording_iff`/`round_criterion`
  (no re-derivation): after a supporting cut, the same normal with the witness `A'⁻¹c`, the depth
  `ρ' = 1/N` and the slack `del' = (1/N)√σ'` satisfies the WHOLE ledger at ceiling `1/N`
  (`reuse_records_at_new_ceiling`, ledger SATURATED: `del'² = ρ'²σ'` exactly), hence the round
  criterion holds there (`reuse_criterion_at_new_ceiling`).  So at a single round the factor-4
  enlargement is exactly what the leaf needs.
* **§3 — the re-discharge FAILS: `rmax = 1/n²` admits NO `RunParams` at all.**  `RunParams` has ONE
  ceiling field, used twice: `hle : ρ_k ≤ rmax` (the leaf's ledger) and
  `hhalve : (√(rho0R N rmax))⁻¹ ^ m ≤ 1/2` (the contraction).  `rho0R` is ANTITONE in the depth
  (`rho0R_anti`, banked: a shallower cut is a larger step), so enlarging the ceiling enlarges the
  halving base — the phase note's *"a LARGER `rmax` gives a FASTER contraction, so the halving …
  constraints get easier"* is **backwards** (`halve_base_mono_ceiling`).  Worse, at `ρ = 1/N` the
  per-round potential factor reaches `rho0R N (1/N) ≤ 1` (`rho0R_new_le_one`), so the halving base is
  `≥ 1` and the halving inequality fails at EVERY horizon (`not_hhalve_at_newRmax`,
  `not_halve_at_newRmax`, and `not_hhalve_campaign` at the campaign's own `N = n·n` and rational
  ceiling).  The exact satisfiability boundary is `∃ m, base^m ≤ 1/2 ↔ 1 < rho0R N r`
  (`halve_exists_iff`) — so the admissible ceilings are exactly `{r | 1 < rho0R N r}`, an interval
  `[0, ρ*)` with `ρ* ≈ 1/(2N)` for large `N`: `rho0R N (1/(4N)) ≥ 1 + 1/(8N) > 1` (banked
  `rho0R_shallow_lower`, restated `shallow_ceiling_ok`) is on the safe side, `1/N` on the dead side
  (`halve_base_old_lt_new` puts them in order).  The structure-level companion is
  **`Check_fc40b_m1.lean`** (a separate file: the cones of `Def_QMCLeafB_final_stroke_m7` and
  `Def_QMCLeafB_relax_oracle_m4`/`_merged_m5` do not co-load): `runParams_rho0R_gt_one` — EVERY
  `RunParams` forces `1 < rho0R (n·n) rmax` — and `not_runParams_at_newRmax`, the empty-family
  statement.  `rmax` occurs in exactly two field types (`hrmax : 0 ≤ rmax`, `hhalve`); `hbudget` does
  not mention it.

**Consequence for the campaign.**  The factor-4 fix is real (§2) but **cannot be bought by enlarging
`RunParams.rmax`** (§3).  The two uses of the single ceiling must be decoupled — keep the contraction
ceiling at `rmaxOf N = 1/(4N)` (where `hhalveOf` is banked) and add a *separate* ledger/leaf ceiling
`1/N` carrying `hle`; then §2's recording supplies the leaf's inequality at `1/N` with
`rho0R`/`hhalve` untouched.  "The leaf is one assembly away" is therefore not supported: one
definitional re-shaping (a second ceiling field) is owed first.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every load-bearing declaration.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.Fc40M1

open QMCLeafB
open QMCLeafB.EngineIterates

/-! ## 1.  The factor: the exact defect identity, the threshold, and the miss factor `4`

The closing move's arithmetic, with nothing estimated.  `N` is the dimension of the shape
(`N = n·n` in the campaign); the ceiling to be tested is `1/N`, the old one `rmaxOf N = 1/(4N)`
(`rmaxOf` is definitionally `1/(4·N)`). -/

/-- **THE DEFECT IDENTITY.**  The gap between the new ceiling `1/N` and the standard step's reuse
ratio `(1−ρ)/(N+ρ)` is exactly `ρ(N+1)/(N(N+ρ))` — nonnegative, and `0` only at zero depth. -/
theorem ratio_defect {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 / (N : ℝ) - (1 - ρ) / ((N : ℝ) + ρ)
      = ρ * ((N : ℝ) + 1) / ((N : ℝ) * ((N : ℝ) + ρ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hN0
  have hdne : ((N : ℝ) + ρ) ≠ 0 := ne_of_gt hden
  field_simp
  ring

#print axioms QMCLeafB.Fc40M1.ratio_defect

/-- **THE CLOSING INEQUALITY.**  At EVERY depth `ρ ≥ 0` the standard step's reuse ratio is at most the
new ceiling `1/N`.  No hypothesis `ρ ≤ 1/N` is needed — the ceiling `1/N` dominates the ratio
uniformly in the depth, which is exactly what the phase-40 enlargement buys. -/
theorem ratio_le_inv {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have h := ratio_defect hN hρ
  have hnn : 0 ≤ ρ * ((N : ℝ) + 1) / ((N : ℝ) * ((N : ℝ) + ρ)) := by positivity
  linarith [h]

#print axioms QMCLeafB.Fc40M1.ratio_le_inv

/-- The inequality is STRICT at every strictly positive depth: the ceiling `1/N` has slack at least
`ρ(N+1)/(N(N+ρ))` whenever the round actually spends depth. -/
theorem ratio_lt_inv {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 < ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) < 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have h := ratio_defect hN hρ.le
  have hpos : 0 < ρ * ((N : ℝ) + 1) / ((N : ℝ) * ((N : ℝ) + ρ)) := by positivity
  linarith [h]

#print axioms QMCLeafB.Fc40M1.ratio_lt_inv

/-- **`1/N` is ATTAINED, at zero depth.**  The closing inequality is an equality iff the round spends
no depth at all — so `1/N` cannot be lowered even if one restricts to the `del ≡ 0` regime. -/
theorem ratio_eq_inv_iff {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) = 1 / (N : ℝ) ↔ ρ = 0 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  constructor
  · intro h
    have hd := ratio_defect hN hρ
    have hz : ρ * ((N : ℝ) + 1) / ((N : ℝ) * ((N : ℝ) + ρ)) = 0 := by
      rw [← hd, h]; ring
    rcases div_eq_zero_iff.1 hz with h1 | h2
    · rcases mul_eq_zero.1 h1 with h1' | h1'
      · exact h1'
      · linarith
    · exact absurd h2 (ne_of_gt (mul_pos hN0 hden))
  · intro h
    subst h
    simp

#print axioms QMCLeafB.Fc40M1.ratio_eq_inv_iff

/-- **THE THRESHOLD: `1/N` is the LEAST admissible ceiling.**  A ceiling `t ≥ 0` dominates the reuse
ratio at every legal depth `ρ ≤ t` iff `1/N ≤ t`.  So the phase-40 enlargement lands exactly on the
boundary of what works: no ceiling below `1/N` (in particular not `1/(2N)`, not `rmaxOf N = 1/(4N)`)
can be re-discharged by the standard step's own cut. -/
theorem ceiling_threshold {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ t → (1 - ρ) / ((N : ℝ) + ρ) ≤ t) ↔ 1 / (N : ℝ) ≤ t := by
  constructor
  · intro h
    simpa using h 0 le_rfl ht
  · intro ht' ρ hρ _
    exact le_trans (ratio_le_inv hN hρ) ht'

#print axioms QMCLeafB.Fc40M1.ceiling_threshold

/-- **The new constant is exactly four times the campaign's.**  `1/N = 4 · rmaxOf N`, so the phase-40
enlargement is the factor-`4` enlargement and nothing else. -/
theorem newRmax_eq_four_mul (N : ℕ) (hN : 0 < N) :
    1 / (N : ℝ) = 4 * ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold QMCLeafB.RundataHalving.rmaxOf
  push_cast
  field_simp

#print axioms QMCLeafB.Fc40M1.newRmax_eq_four_mul

/-- **The miss factor is at most `4`.**  Relative to the old ceiling `rmaxOf N = 1/(4N)` the standard
step's reuse ratio is at most four times too big — uniformly in `N` and in the depth. -/
theorem miss_ratio_le_four {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) / (1 / (4 * (N : ℝ))) ≤ 4 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have h1 : (1 - ρ) / ((N : ℝ) + ρ) / (1 / (4 * (N : ℝ)))
      = 4 * (N : ℝ) * (1 - ρ) / ((N : ℝ) + ρ) := by
    field_simp
  rw [h1, div_le_iff₀ hden]
  nlinarith [hN0, hρ]

#print axioms QMCLeafB.Fc40M1.miss_ratio_le_four

/-- **…and `4` is ATTAINED**, at zero depth: `ρ = 0` gives the ratio `1/N`, i.e. exactly `4 · rmaxOf N`.
So m2's "`→ 4`" is not a limit — it is the exact value at the flat end of the depth range. -/
theorem miss_ratio_eq_four {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) / (1 / (4 * (N : ℝ))) = 4 ↔ ρ = 0 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have h1 : (1 - ρ) / ((N : ℝ) + ρ) / (1 / (4 * (N : ℝ)))
      = 4 * (N : ℝ) * (1 - ρ) / ((N : ℝ) + ρ) := by
    field_simp
  rw [h1, div_eq_iff (ne_of_gt hden)]
  constructor
  · intro h
    have h2 : ρ * (4 * (N : ℝ) + 4) = 0 := by linarith [h]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · linarith
  · intro h
    subst h
    ring

#print axioms QMCLeafB.Fc40M1.miss_ratio_eq_four

/-- **The old ceiling is short, at zero depth, with no hypothesis on the depth.**  m2's
`ratio_gt_rmax` in the sharpest instance: at `ρ = 0` the reuse ratio is `1/N > rmaxOf N`.  (This is a
one-line consequence of §1 and is recorded so that the two ceilings are compared at the same point.) -/
theorem old_ceiling_short {N : ℕ} (hN : 0 < N) :
    (QMCLeafB.RundataHalving.rmaxOf N : ℚ) < (1 - (0:ℝ)) / ((N : ℝ) + 0) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold QMCLeafB.RundataHalving.rmaxOf
  push_cast
  rw [sub_zero, add_zero]
  exact one_div_lt_one_div_of_lt hN0 (by linarith)

#print axioms QMCLeafB.Fc40M1.old_ceiling_short

/-! ## 2.  The closing move at one round: the reuse cut records at the new ceiling

Everything below is REUSE.  The round's datum: a positive definite shape `A`, the centre `a`, a
nonzero normal `c` with witness `p` (`A p = c`), a depth `ρ ≥ 0`, and a body `body` on the far side of
the supporting hyperplane through `a`.  The step produces `A' = stepShape N A c p ρ`,
`a' = stepCentre N a c p ρ`, and `σ' = c ⬝ᵥ (A'⁻¹ c)`. -/

/-- **THE CLOSING INEQUALITY, WIRED TO THE STEP.**  One round after a supporting cut at ANY depth
`ρ ≥ 0`, the same normal satisfies the leaf's support inequality *at the new ceiling* `1/N`:
`c ⬝ᵥ (a' − z) ≤ (1/N)·√σ'` for every body point.  m2's `supporting_normal_ratio` gives the ratio
`(1−ρ)/(N+ρ)`; §1 caps it by `1/N`. -/
theorem reuse_le_new_ceiling {N : ℕ} (hn : 2 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) {body : (Fin N → ℝ) → Prop}
    (hsupp : ∀ z, body z → c ⬝ᵥ (a - z) ≤ 0) {z : Fin N → ℝ} (hz : body z) :
    c ⬝ᵥ (stepCentre N a c p ρ - z)
      ≤ (1 / (N : ℝ)) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hn hA hc hAp hρ
  have hinv : (stepShape N A c p ρ) *ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hA', Matrix.one_mulVec]
  have hσ' : 0 < sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := sqrtSigmaR_pos hA' hinv hc
  have h1 := QMCLeafB.Eq38M2.supporting_normal_ratio hn hA hc hAp hρ hsupp hz
  have h2 : (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (N : ℝ) := ratio_le_inv (by omega) hρ
  calc c ⬝ᵥ (stepCentre N a c p ρ - z)
      ≤ ((1 - ρ) / ((N : ℝ) + ρ)) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := h1
    _ ≤ (1 / (N : ℝ)) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) :=
        mul_le_mul_of_nonneg_right h2 hσ'.le

#print axioms QMCLeafB.Fc40M1.reuse_le_new_ceiling

/-- **THE NEXT ROUND'S LEDGER IS SATISFIED AT CEILING `1/N`.**  With normal `c`, witness `A'⁻¹c`,
depth `ρ' = 1/N` and slack `del' = (1/N)√σ'`, the whole recorded ledger holds at the next round —
`0 ≤ ρ' ≤ 1/N`, `0 ≤ del'`, `del'² ≤ ρ'²σ'` (with EQUALITY: the ledger is saturated, nothing is
wasted, nothing is missing) and the cut separates every body point. -/
theorem reuse_records_at_new_ceiling {N : ℕ} (hn : 2 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) {body : (Fin N → ℝ) → Prop}
    (hsupp : ∀ z, body z → c ⬝ᵥ (a - z) ≤ 0) :
    ∃ (ρ' del' : ℝ), 0 ≤ ρ' ∧ ρ' ≤ 1 / (N : ℝ) ∧ 0 ≤ del' ∧
      del' ^ 2 ≤ ρ' ^ 2 * (c ⬝ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c)) ∧
      (∀ z, body z → -del' ≤ c ⬝ᵥ (z - stepCentre N a c p ρ)) := by
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hn hA hc hAp hρ
  have hinv : (stepShape N A c p ρ) *ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hA', Matrix.one_mulVec]
  have hσ' : 0 < sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := sqrtSigmaR_pos hA' hinv hc
  have hsq : sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      = c ⬝ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) := sqrtSigmaR_mul_self hA' hinv hc
  refine ⟨1 / (N : ℝ), (1 / (N : ℝ)) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c),
    by positivity, le_rfl, by positivity, ?_, ?_⟩
  · have hsq' : (sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)) ^ 2
        = c ⬝ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by
      rw [pow_two]; exact hsq
    rw [mul_pow, hsq']
  · intro z hz
    have h := reuse_le_new_ceiling hn hA hc hAp hρ hsupp hz
    rw [show z - stepCentre N a c p ρ = -(stepCentre N a c p ρ - z) by abel, dotProduct_neg]
    linarith [h]

#print axioms QMCLeafB.Fc40M1.reuse_records_at_new_ceiling

/-- **THE ROUND CRITERION AT THE NEXT ROUND.**  m5's `recording_iff` applied to the ledger of §2: at
the next round, at ceiling `1/N`, there IS an `A'`-unit direction whose slab of height `1/N` contains
the body.  This is the leaf's round obligation in criterion form. -/
theorem reuse_criterion_at_new_ceiling {N : ℕ} (hn : 2 ≤ N)
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) {body : (Fin N → ℝ) → Prop}
    (hsupp : ∀ z, body z → c ⬝ᵥ (a - z) ≤ 0) :
    ∃ w : Fin N → ℝ,
      QMCLeafB.Lm38M5.qfR (stepShape N A c p ρ) w = 1 ∧
      ∀ z, body z →
        (z - stepCentre N a c p ρ) ⬝ᵥ ((stepShape N A c p ρ) *ᵥ w) ≤ 1 / (N : ℝ) := by
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hn hA hc hAp hρ
  have hinv : (stepShape N A c p ρ) *ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hA', Matrix.one_mulVec]
  obtain ⟨ρ', del', hρ0, hρle, hdel0, hchk, hcut⟩ :=
    reuse_records_at_new_ceiling hn hA hc hAp hρ hsupp
  have hcrit := (QMCLeafB.Lm38M5.recording_iff hA' {z : Fin N → ℝ | body z}
    (stepCentre N a c p ρ) (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))).mp
    ⟨c, (stepShape N A c p ρ)⁻¹ *ᵥ c, ρ', del', hc, hinv, hρ0, hρle, hdel0, hchk,
      fun z hz => hcut z hz⟩
  obtain ⟨w, hw, hbody⟩ := hcrit
  exact ⟨w, hw, fun z hz => hbody z hz⟩

#print axioms QMCLeafB.Fc40M1.reuse_criterion_at_new_ceiling

/-! ## 3.  The re-discharge FAILS: the halving base at `rmax = 1/N` is `≥ 1`

`RunParams.hhalve` is `(√(rho0R N rmax))⁻¹ ^ m ≤ 1/2`, i.e. *"the potential at the worst legal depth
at least halves in `m` rounds"*.  `rho0R` is ANTITONE in the depth (`rho0R_anti`: a shallower cut is a
larger step), so the ceiling's worst case is `ρ = rmax` itself, and enlarging the ceiling enlarges the
base.  At `rmax = 1/N` the base crosses `1`: no `m` works. -/

/-- **`rho0R N (1/N) ≤ 1`.**  The one-step potential factor at depth `1/N` is at most `1` — the step
does not contract at all in the worst legal case.  Proof: with `a = N`,
`rho0R N ρ = [(a²−1)/(a+ρ)²]^N · (a+1)/(a−1)`; at `ρ = 1/N` the first factor is
`(a²−1)a²/(a²+1)²` and one Bernoulli step `(1+u)^N ≥ 1 + Nu` for `u = 2/(a(a−1))` gives
`(a+1)/(a−1) ≤ (1+u)^N`, leaving the polynomial inequality
`(a²−1)a²(1+u) = a⁴+a²+2a ≤ (a²+1)² = a⁴+2a²+1`, i.e. `(a−1)² ≥ 0`. -/
theorem rho0R_new_le_one (N : ℕ) (hN : 2 ≤ N) :
    rho0R N ((N : ℝ)⁻¹) ≤ 1 := by
  have ha : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha0 : (0 : ℝ) < (N : ℝ) := by linarith
  have ha1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt ha0
  have h1ne : ((N : ℝ) - 1) ≠ 0 := ne_of_gt ha1
  -- the Bernoulli bound `(N+1) ≤ (N−1)(1+u)^N`
  set u : ℝ := 2 / ((N : ℝ) * ((N : ℝ) - 1)) with hu
  have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
  have hNu : ((N : ℝ)) * u = 2 / ((N : ℝ) - 1) := by
    rw [hu]; field_simp
  have hbern : ((N : ℝ) + 1) ≤ ((N : ℝ) - 1) * (1 + u) ^ N := by
    have hb := one_add_mul_le_pow (R := ℝ) (a := u) (by linarith) N
    rw [hNu] at hb
    have heq : ((N : ℝ) - 1) * (1 + 2 / ((N : ℝ) - 1)) = ((N : ℝ) + 1) := by
      field_simp
      ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hb ha1.le
  -- the polynomial core
  have hkey : ((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2 * (1 + u) ≤ ((N : ℝ) ^ 2 + 1) ^ 2 := by
    rw [hu]
    have h : ((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2 * (1 + 2 / ((N : ℝ) * ((N : ℝ) - 1)))
        = ((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2 + 2 * (N : ℝ) * ((N : ℝ) + 1) := by
      field_simp
      ring
    rw [h]
    nlinarith [ha0, sq_nonneg ((N : ℝ) - 1)]
  -- the power bookkeeping
  have hN2 : (0 : ℝ) < (N : ℝ) ^ (2 * N) := by positivity
  have hsplit : ((N : ℝ) ^ 2 - 1) ^ N * (N : ℝ) ^ (2 * N)
      = (((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2) ^ N := by
    rw [pow_mul, mul_pow]
  have hbase_nn : (0 : ℝ) ≤ ((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2 :=
    mul_nonneg (by nlinarith [ha] : (0 : ℝ) ≤ (N : ℝ) ^ 2 - 1) (by positivity)
  have hmain : ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1) * (N : ℝ) ^ (2 * N)
      ≤ ((N : ℝ) - 1) * ((N : ℝ) ^ 2 + 1) ^ (2 * N) := by
    calc ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1) * (N : ℝ) ^ (2 * N)
        = (((N : ℝ) ^ 2 - 1) ^ N * (N : ℝ) ^ (2 * N)) * ((N : ℝ) + 1) := by ring
      _ = (((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2) ^ N * ((N : ℝ) + 1) := by rw [hsplit]
      _ ≤ (((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2) ^ N
            * (((N : ℝ) - 1) * (1 + u) ^ N) :=
          mul_le_mul_of_nonneg_left hbern (pow_nonneg hbase_nn N)
      _ = ((N : ℝ) - 1) * ((((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2) ^ N * (1 + u) ^ N) := by ring
      _ = ((N : ℝ) - 1) * ((((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2) * (1 + u)) ^ N := by
          rw [← mul_pow]
      _ ≤ ((N : ℝ) - 1) * (((N : ℝ) ^ 2 + 1) ^ (2 * N)) := by
          have hbase1_nn : (0 : ℝ) ≤ ((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2 * (1 + u) :=
            mul_nonneg hbase_nn (by linarith : (0 : ℝ) ≤ 1 + u)
          have hp : (((N : ℝ) ^ 2 - 1) * (N : ℝ) ^ 2 * (1 + u)) ^ N
              ≤ (((N : ℝ) ^ 2 + 1) ^ 2) ^ N :=
            pow_le_pow_left₀ hbase1_nn hkey N
          have h2 : (((N : ℝ) ^ 2 + 1) ^ 2) ^ N = ((N : ℝ) ^ 2 + 1) ^ (2 * N) := by rw [pow_mul]
          rw [h2] at hp
          exact mul_le_mul_of_nonneg_left hp (by linarith)
  -- transport to `rho0R`
  have hden_eq : ((N : ℝ) - 1) * ((N : ℝ) + (N : ℝ)⁻¹) ^ (2 * N) * (N : ℝ) ^ (2 * N)
      = ((N : ℝ) - 1) * ((N : ℝ) ^ 2 + 1) ^ (2 * N) := by
    rw [mul_assoc, ← mul_pow]
    have hb : ((N : ℝ) + (N : ℝ)⁻¹) * (N : ℝ) = ((N : ℝ) ^ 2 + 1) := by
      field_simp
    rw [hb]
  have hm : ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1) * (N : ℝ) ^ (2 * N)
      ≤ ((N : ℝ) - 1) * ((N : ℝ) + (N : ℝ)⁻¹) ^ (2 * N) * (N : ℝ) ^ (2 * N) := by
    rw [hden_eq]; exact hmain
  have hfin : ((N : ℝ) ^ 2 - 1) ^ N * ((N : ℝ) + 1)
      ≤ ((N : ℝ) - 1) * ((N : ℝ) + (N : ℝ)⁻¹) ^ (2 * N) :=
    le_of_mul_le_mul_right hm hN2
  rw [rho0R]
  exact (div_le_one (by positivity : (0 : ℝ) < ((N : ℝ) - 1) * ((N : ℝ) + (N : ℝ)⁻¹) ^ (2 * N))).mpr
    hfin

#print axioms QMCLeafB.Fc40M1.rho0R_new_le_one

/-- **The halving base at the new ceiling is `≥ 1`.** -/
theorem inv_sqrt_new_ge_one (N : ℕ) (hN : 2 ≤ N) :
    1 ≤ (Real.sqrt (rho0R N ((N : ℝ)⁻¹)))⁻¹ := by
  have h1 : rho0R N ((N : ℝ)⁻¹) ≤ 1 := rho0R_new_le_one N hN
  have h2 : 0 < rho0R N ((N : ℝ)⁻¹) := rho0R_pos hN (by positivity)
  have h3 : Real.sqrt (rho0R N ((N : ℝ)⁻¹)) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact h1
  have h4 : 0 < Real.sqrt (rho0R N ((N : ℝ)⁻¹)) := Real.sqrt_pos.mpr h2
  exact (one_le_inv₀ h4).mpr h3

#print axioms QMCLeafB.Fc40M1.inv_sqrt_new_ge_one

/-- **THE HALVING INEQUALITY IS FALSE AT `rmax = 1/N`, AT EVERY HORIZON.**  This is the exact shape of
`RunParams.hhalve` at `rmax = (n·n)⁻¹` (with `N` the shape dimension): the potential cannot halve,
because it does not even decrease. -/
theorem not_hhalve_at_newRmax (N : ℕ) (hN : 2 ≤ N) (m : ℕ) :
    ¬ ((Real.sqrt (rho0R N ((N : ℝ)⁻¹)))⁻¹ ^ m ≤ 1 / 2) := by
  intro h
  have hge : 1 ≤ (Real.sqrt (rho0R N ((N : ℝ)⁻¹)))⁻¹ := inv_sqrt_new_ge_one N hN
  have h1 : (1 : ℝ) ≤ (Real.sqrt (rho0R N ((N : ℝ)⁻¹)))⁻¹ ^ m := one_le_pow₀ hge
  linarith

#print axioms QMCLeafB.Fc40M1.not_hhalve_at_newRmax

/-- **No horizon rescues it**: there is no `m` whatsoever. -/
theorem not_halve_at_newRmax (N : ℕ) (hN : 2 ≤ N) :
    ¬ ∃ m : ℕ, ((Real.sqrt (rho0R N ((N : ℝ)⁻¹)))⁻¹ ^ m ≤ 1 / 2) := by
  rintro ⟨m, hm⟩
  exact not_hhalve_at_newRmax N hN m hm

#print axioms QMCLeafB.Fc40M1.not_halve_at_newRmax

/-- **THE CAMPAIGN INSTANCE.**  At the shape dimension `N = n·n` (so `1/N = 1/n²`, the phase-40
constant, and `n ≥ 2`) the halving inequality fails at every horizon, in the campaign's own rational
ceiling `((n·n : ℚ))⁻¹`. -/
theorem not_hhalve_campaign (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) (m : ℕ) :
    ¬ ((Real.sqrt (rho0R (G.n * G.n) ((((G.n * G.n : ℕ) : ℚ)⁻¹ : ℚ) : ℝ)))⁻¹ ^ m ≤ 1 / 2) := by
  have hN : 2 ≤ G.n * G.n := by nlinarith
  have hcast : ((((G.n * G.n : ℕ) : ℚ)⁻¹ : ℚ) : ℝ) = (((G.n * G.n : ℕ) : ℝ))⁻¹ := by
    push_cast
    ring
  rw [hcast]
  exact not_hhalve_at_newRmax (G.n * G.n) hN m

#print axioms QMCLeafB.Fc40M1.not_hhalve_campaign

/-- **THE EXACT SATISFIABILITY BOUNDARY.**  A ceiling `r ≥ 0` admits *some* halving horizon iff the
one-step potential factor at that ceiling exceeds `1`.  So the admissible ceilings form the interval
`[0, ρ*)` and every ceiling past `ρ*` is dead — no `m`, no `K`, no programme choice repairs it. -/
theorem halve_exists_iff (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr : 0 ≤ r) :
    (∃ m : ℕ, (Real.sqrt (rho0R N r))⁻¹ ^ m ≤ 1 / 2) ↔ 1 < rho0R N r := by
  have hρ0 : 0 < rho0R N r := rho0R_pos hN hr
  have hs0 : 0 < Real.sqrt (rho0R N r) := Real.sqrt_pos.mpr hρ0
  constructor
  · rintro ⟨m, hm⟩
    by_contra hcon
    simp only [not_lt] at hcon
    have hs1 : Real.sqrt (rho0R N r) ≤ 1 := by rw [Real.sqrt_le_one]; exact hcon
    have hinv1 : 1 ≤ (Real.sqrt (rho0R N r))⁻¹ := (one_le_inv₀ hs0).mpr hs1
    have h1 : (1 : ℝ) ≤ (Real.sqrt (rho0R N r))⁻¹ ^ m := one_le_pow₀ hinv1
    linarith
  · intro h1
    have hs1 : 1 < Real.sqrt (rho0R N r) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) h1
    have hinv : (Real.sqrt (rho0R N r))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      exact Or.inr hs1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hinv
    exact ⟨m, le_of_lt hm⟩

#print axioms QMCLeafB.Fc40M1.halve_exists_iff

/-- **ENLARGING THE CEILING MAKES THE HALVING HARDER** — the exact negation of the phase-40 note
("a LARGER `rmax` gives a FASTER contraction, so the halving … constraints get easier").  The halving
base is monotone INCREASING in the ceiling, because `rho0R` is antitone in the depth. -/
theorem halve_base_mono_ceiling (N : ℕ) (hN : 2 ≤ N) {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (h : ρ ≤ ρ') :
    (Real.sqrt (rho0R N ρ))⁻¹ ≤ (Real.sqrt (rho0R N ρ'))⁻¹ := by
  have h1 : rho0R N ρ' ≤ rho0R N ρ := rho0R_anti hN hρ h
  have h2 : Real.sqrt (rho0R N ρ') ≤ Real.sqrt (rho0R N ρ) := Real.sqrt_le_sqrt h1
  have h3 : 0 < Real.sqrt (rho0R N ρ') := Real.sqrt_pos.mpr (rho0R_pos hN (le_trans hρ h))
  exact inv_anti₀ h3 h2

#print axioms QMCLeafB.Fc40M1.halve_base_mono_ceiling

/-- **The campaign's own ceiling is on the SAFE side.**  `rho0R N (rmaxOf N) = 1 + 1/(8N) > 1`
(banked `rho0R_shallow_lower`), so `rmaxOf N = 1/(4N)` admits a halving horizon while `1/N` does not:
the two ceilings sit on opposite sides of the satisfiability boundary.  This is what makes the
split-field repair (ledger ceiling `1/N`, contraction ceiling `1/(4N)`) available. -/
theorem shallow_ceiling_ok (N : ℕ) (hN : 2 ≤ N) :
    1 < rho0R N ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) := by
  have h := QMCLeafB.RundataHalving.rho0R_shallow_lower N hN
  have hpos : (0 : ℝ) < 1 / (8 * (N : ℝ)) := by positivity
  unfold QMCLeafB.RundataHalving.rmaxOf at h ⊢
  push_cast at h ⊢
  linarith

#print axioms QMCLeafB.Fc40M1.shallow_ceiling_ok

/-- **The halving base strictly increases across the phase-40 enlargement**: at the old ceiling it is
below the base at the new one, and the new base is already `≥ 1`. -/
theorem halve_base_old_lt_new (N : ℕ) (hN : 2 ≤ N) :
    (Real.sqrt (rho0R N ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ)))⁻¹
      < (Real.sqrt (rho0R N ((N : ℝ)⁻¹)))⁻¹ := by
  have hnew : rho0R N ((N : ℝ)⁻¹) ≤ 1 := rho0R_new_le_one N hN
  have hold : 1 < rho0R N ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) := shallow_ceiling_ok N hN
  have h1 : Real.sqrt (rho0R N ((N : ℝ)⁻¹)) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hnew
  have h2 : 1 < Real.sqrt (rho0R N ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) hold
  have hrm : (0 : ℝ) ≤ ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) := by
    unfold QMCLeafB.RundataHalving.rmaxOf
    push_cast
    positivity
  have hb : (0 : ℝ) < Real.sqrt (rho0R N ((N : ℝ)⁻¹)) :=
    Real.sqrt_pos.mpr (rho0R_pos hN (by positivity))
  have ha : (0 : ℝ) < Real.sqrt (rho0R N ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ)) :=
    Real.sqrt_pos.mpr (rho0R_pos hN hrm)
  rw [inv_lt_inv₀ ha hb]
  linarith

#print axioms QMCLeafB.Fc40M1.halve_base_old_lt_new

/-- **WHAT DEPTH THE OLD CEILING WOULD NEED — the factor `4` in threshold form.**  At the campaign's
own ceiling `rmaxOf N = 1/(4N)` the standard step's reuse ratio fits only at depth
`ρ ≥ 3N/(4N+1) > 3/4`, whereas `RunParams` allows `ρ ≤ 1/(4N) ≤ 1/8` for `N ≥ 2`.  So at the banked
parameters the reuse lane is dead at EVERY legal depth, by an exact margin: the miss factor
`4N(1−ρ)/(N+ρ)` of `Eq38M2` reaches `4` exactly when `ρ = 0` and falls below `1` only past
`ρ = 3N/(4N+1) ≈ 3/4`.  This is the sharp form of `Eq38M2.reuse_short_of_leaf` and of
`pn40_m5`'s `reuse_fails_at_every_params` (which fixes `ρ = 0`). -/
theorem reuse_needs_depth {N : ℕ} (hN : 0 < N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (4 * (N : ℝ))
      ↔ 3 * (N : ℝ) / (4 * (N : ℝ) + 1) ≤ ρ := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have h4 : (0 : ℝ) < 4 * (N : ℝ) := by positivity
  have h41 : (0 : ℝ) < 4 * (N : ℝ) + 1 := by positivity
  have e1 : (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (4 * (N : ℝ))
      ↔ 4 * (N : ℝ) * (1 - ρ) ≤ (N : ℝ) + ρ := by
    constructor
    · intro h
      have h2 : (1 - ρ) / ((N : ℝ) + ρ) * (4 * (N : ℝ)) ≤ 1 :=
        (le_div_iff₀ h4).mp h
      have h3 : ((1 - ρ) * (4 * (N : ℝ))) / ((N : ℝ) + ρ) ≤ 1 := by
        rwa [div_mul_eq_mul_div] at h2
      have h4' := (div_le_one hden).mp h3
      linarith
    · intro h
      have h3 : ((1 - ρ) * (4 * (N : ℝ))) / ((N : ℝ) + ρ) ≤ 1 :=
        (div_le_one hden).mpr (by linarith : (1 - ρ) * (4 * (N : ℝ)) ≤ (N : ℝ) + ρ)
      have h2 : (1 - ρ) / ((N : ℝ) + ρ) * (4 * (N : ℝ)) ≤ 1 := by
        rwa [div_mul_eq_mul_div]
      exact (le_div_iff₀ h4).mpr h2
  have e2 : 3 * (N : ℝ) / (4 * (N : ℝ) + 1) ≤ ρ ↔ 3 * (N : ℝ) ≤ ρ * (4 * (N : ℝ) + 1) :=
    div_le_iff₀ h41
  rw [e1, e2]
  constructor <;> intro h <;> linarith

#print axioms QMCLeafB.Fc40M1.reuse_needs_depth

/-- **The reuse lane is DEAD at the banked parameters, at every legal depth** — the contrapositive of
`reuse_needs_depth` against `ρ ≤ rmaxOf N`.  So the campaign cannot close the leaf by reusing the
step's own normal at `rmaxOf (n·n)`; only a *fresh* separating direction per round can (phase-38's
`SepStream`, `del ≡ 0`).  This is the exact statement of why the factor-`4` ledger is not idle
bookkeeping: it is the difference between the ratio the step supplies and the ledger it must meet. -/
theorem no_reuse_at_banked_params {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / (4 * (N : ℝ))) :
    1 / (4 * (N : ℝ)) < (1 - ρ) / ((N : ℝ) + ρ) := by
  have ha : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have h41 : (0 : ℝ) < 4 * (N : ℝ) + 1 := by positivity
  have hlt : 1 / (4 * (N : ℝ)) < 3 * (N : ℝ) / (4 * (N : ℝ) + 1) := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (N : ℝ))]
    rw [div_mul_eq_mul_div, lt_div_iff₀ h41]
    nlinarith
  have hne : ¬ ((1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (4 * (N : ℝ))) := by
    intro h
    have h' := (reuse_needs_depth (by omega) hρ0).mp h
    linarith
  exact lt_of_not_ge hne

#print axioms QMCLeafB.Fc40M1.no_reuse_at_banked_params


