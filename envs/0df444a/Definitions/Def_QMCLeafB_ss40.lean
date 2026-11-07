-- Prove2me | Definitions.Def_QMCLeafB_ss40
-- name    : QMCLeafB_ss40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:56:17.117318+00:00
-- url     : https://prove2.me/theorems/b85dec5d-f46a-428e-8bcf-7f663ce358ad
-- title:
--   QMCLeafB ss40
-- statement:
--   # `Check_ss40_m3` — phase 40, member m3, direction `sepstream-from-step` (d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_asm36
import Definitions.Def_QMCLeafB_eq38
import Definitions.Def_QMCLeafB_lm38
/-
# `Check_ss40_m3` — phase 40, member m3, direction `sepstream-from-step` (d5)

**Task.** Construct the cut sequence from the standard ellipsoid step and decide whether the leaf's
last object (`SepStream`, `Check_rf38_m1`) follows at the enlarged ceiling `rmax = 1/N`, `N = n·n`.

**What this file establishes (all machine-checked; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`).**

* **§1 THE FACTOR.**  At every legal depth `ρ ≥ 0`, `(1−ρ)/(N+ρ) ≤ 1/N`.  No upper bound on `ρ` is
  needed: enlargement of the ceiling from `1/(4N)` (`rmaxOf (n·n)`) to `1/N` (`1/n²`) suffices for the
  reuse normal at *every* admissible depth, with equality exactly at `ρ = 0`.

* **§2 THE CLOSING MOVE, AT THE LEAF'S OWN INTERFACE.**  A supporting cut at `(A, a)` (nonzero normal
  `c`, witness `p`, `A p = c`, `c·(a−z) ≤ 0` on the body) recorded at depth `ρ ≥ 0` leaves the SAME
  normal seeing the body at the NEXT centre at `≤ (1/N)·√σ'` — the leaf's allowance verbatim
  (`reuse_le_ceiling`).  Transported into the leaf's `∃w`-form (`reuse_round_w`) and then, through
  `Check_lm38_m5.recording_iff`, into the round's full cut record at ceiling `1/N` (`reuse_records`).

* **§3 WHAT THE ENLARGEMENT DOES *NOT* BUY.**  The ledger allows slack `del = ρ√σ` at every round, so
  the hope is that `del > 0` can be spent and the chain continued.  It cannot: `step_dot_eq` gives the
  exact update `c·(a'−z) = c·(a−z) + γ√σ`; `slack_ratio_eq` shows a body point at the ledger's MAXIMUM
  slack produces next-round normalised depth `(1+ρN)/(N+ρ)` exactly; `slack_ratio_gt` shows that
  exceeds the leaf's `1/N` for every `ρ > 0`; `del_zero_of_rho_zero` shows `ρ = 0` forces `del = 0`.
  So the depth ledger cannot replace the exact-support hypothesis.

* **§4 THE ENGINE'S OWN DATA.**  `engine_round_after_support`: for the engine's transcript
  (`Aat`/`Cat` from a `CutData` stream) a supporting round gives the leaf's `∃w` round condition at
  the next iterate, at ceiling `1/N`.

**Verdict (two independent findings).**

1. **The factor is real, and it is one round wide.**  At `rmax = 1/N` a supporting round propagates
   to the next round's leaf obligation (§2), for free, at every legal depth.  It does not manufacture
   support, and §3 shows the ledger's slack cannot stand in for it: a round spending `del = ρ√σ > 0`
   puts a body point at next-round depth `(1+ρN)/(N+ρ) > 1/N`, exactly.  So the leaf's content stays
   *separation* at the accumulated centres; §6 shows it can be stated with the ledger's slack
   (`ShallowCut`, strictly weaker than `SepStream`) and §6.3 recovers the phase-38 form.

2. **The parameter change is NOT admissible — this is the decisive finding (§7).**  The brief's premise
   "a LARGER `rmax` gives a FASTER contraction" is inverted: `RunParams.hhalve` forces `rho0R > 1`
   (`one_lt_rho0R_of_hhalve`) and `rho0R` is antitone in the depth (`hhalve_of_le_ceiling`).  At the
   campaign's smallest order `n = 2` (ellipsoid dimension `4`) the enlarged ceiling `1/n² = 1/4` has
   `rho0R 4 (1/4) < 1`, so **no `RunParams` with `rmax = 1/n²` exists at all**
   (`no_runParams_rmax_quarter`, and a fortiori for every `rmax ≥ 1/4`: `no_runParams_rmax_ge_quarter`).
   Since the leaf quantifies over every `G` with `2 ≤ G.n`, the closing-move family is EMPTY and the
   assembly cannot be run at it — stated outright as `no_rmaxFamily_inv_sq`: there is NO family
   `P : (G) → RunParams G` with `(P G).rmax = 1/(G.n·G.n)`.  A numerical sweep (`rho0R (n·n) (1/n²) = 1 − 1/n² + O(n⁻³) < 1` for
   `2 ≤ n ≤ 100`; the admissibility threshold is `ρ* ≈ 1/(2n²)`, so `1/n² ≈ 2ρ*` is a factor `2`
   beyond it) says this is not an artefact of `n = 2`; the campaign's own `rmaxOf (n·n) = 1/(4n²)`
   is safely inside (`rho0R 4 (1/16) = 1.137… > 1`).

**The closing move as specified is therefore falsified, not merely unproved.**  What survives is
exactly the old ceiling with the old separation hypothesis; the factor `4` has to be bought some
other way (a potential argument that does not need `rho0R > 1`, or a different ceiling with `hhalve`
re-discharged *downward*).

Discipline: `set_option autoImplicit false`; every theorem carries `#print axioms`, all exactly
`[propext, Classical.choice, Quot.sound]`; imports are published `Definitions.*` bundles plus the two
coordinator-compiled phase-38 bundles whose statements are reused (`Check_eq38_m2`, `Check_lm38_m5`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.Ss40M3

open QMCLeafB.EngineIterates

/-! ## 1.  The factor, at the enlarged ceiling `rmax = 1/N` -/

/-- **THE FACTOR.**  `(1−ρ)/(N+ρ) ≤ 1/N` for every `ρ ≥ 0` — no upper bound on the depth needed. -/
theorem one_sub_div_le_inv (N : ℕ) (hN : 1 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have hrhs : (1 / (N : ℝ)) * ((N : ℝ) + ρ) = 1 + ρ / (N : ℝ) := by
    field_simp
  rw [div_le_iff₀ hden, hrhs]
  have h1 : 0 ≤ ρ / (N : ℝ) := div_nonneg hρ hNpos.le
  linarith

#print axioms QMCLeafB.Ss40M3.one_sub_div_le_inv

/-- The same factor over `ℚ`, the field the engine's depth ledger lives in. -/
theorem one_sub_div_le_inv_rat (N : ℕ) (hN : 1 ≤ N) {ρ : ℚ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℚ) + ρ) ≤ 1 / (N : ℚ) := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hden : (0 : ℚ) < (N : ℚ) + ρ := by linarith
  have hrhs : (1 / (N : ℚ)) * ((N : ℚ) + ρ) = 1 + ρ / (N : ℚ) := by
    field_simp
  rw [div_le_iff₀ hden, hrhs]
  have h1 : 0 ≤ ρ / (N : ℚ) := div_nonneg hρ hNpos.le
  linarith

#print axioms QMCLeafB.Ss40M3.one_sub_div_le_inv_rat

/-- The new ceiling in the engine's own arithmetic: `1/n² = 1/(n·n)`, the ellipsoid dimension being
`n·n`.  So `rmax := (n·n : ℚ)⁻¹` is `rmaxOf`'s constant with the factor `4` removed. -/
theorem rmax_nn (n : ℕ) :
    (1 : ℚ) / ((n : ℚ) * (n : ℚ)) = 1 / ((n * n : ℕ) : ℚ) := by
  push_cast
  ring

#print axioms QMCLeafB.Ss40M3.rmax_nn

/-- At the new ceiling the ledger's check is exactly sharp: `del = (1/N)·√σ` satisfies
`del² ≤ rmax²·σ` with equality.  This is the `hcheck` slot `RunParts` asks for, re-discharged at the
constant `1/N`. -/
theorem hcheck_at_new_ceiling (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ((1 / (N : ℝ)) * Real.sqrt σ) ^ 2 ≤ (1 / (N : ℝ)) ^ 2 * σ := by
  have hsq : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ
  nlinarith [hsq]

#print axioms QMCLeafB.Ss40M3.hcheck_at_new_ceiling

/-! ## 2.  The closing move at the leaf's interface

Reuse only: `Check_eq38_m2.supporting_normal_ratio` is the exact ratio `(1−ρ)/(N+ρ)` of the reused
normal in the next round's own units; §1 says it is at most `1/N`.  No geometry is re-derived. -/

/-- **THE CLOSING MOVE (support form).**  If `c` supports the body at `(A, a)` and the step is taken
at depth `ρ ≥ 0`, the SAME normal sees the body at the next centre with normalised depth at most
`1/N` — the leaf's allowance at `rmax = 1/N`. -/
theorem reuse_le_ceiling {N : ℕ} (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {B : Set (Fin N → ℝ)} (hsupp : ∀ z ∈ B, c ⬝ᵥ (a - z) ≤ 0)
    {z : Fin N → ℝ} (hz : z ∈ B) :
    c ⬝ᵥ (stepCentre N a c p ρ - z)
      ≤ (1 / (N : ℝ)) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by
  have h1 := QMCLeafB.Eq38M2.supporting_normal_ratio hN hA hc hAp hρ
    (body := fun z => z ∈ B) hsupp hz
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hN hA hc hAp hρ
  have hinv : (stepShape N A c p ρ) *ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hA', Matrix.one_mulVec]
  have hs : 0 < sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := sqrtSigmaR_pos hA' hinv hc
  have hN1 : 1 ≤ N := by omega
  exact le_trans h1 (mul_le_mul_of_nonneg_right (one_sub_div_le_inv N hN1 hρ) hs.le)

#print axioms QMCLeafB.Ss40M3.reuse_le_ceiling

/-- **THE CLOSING MOVE (leaf form).**  The `∃w` round condition of `Check_lm38_m5.recording_iff` at
the NEXT iterate, at ceiling `1/N`: some `A'`-unit direction whose `A'`-pairing with every body point
is at most `1/N`.  The witness is the reused normal renormalised, `w = −A'⁻¹c/√σ'`. -/
theorem reuse_round_w {N : ℕ} (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {B : Set (Fin N → ℝ)} (hsupp : ∀ z ∈ B, c ⬝ᵥ (a - z) ≤ 0) :
    ∃ w : Fin N → ℝ,
      qfR (stepShape N A c p ρ) w = 1 ∧
        ∀ z ∈ B, (z - stepCentre N a c p ρ) ⬝ᵥ ((stepShape N A c p ρ) *ᵥ w) ≤ 1 / (N : ℝ) := by
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hN hA hc hAp hρ
  have hinv : (stepShape N A c p ρ) *ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hA', Matrix.one_mulVec]
  have hss : sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      = ((stepShape N A c p ρ)⁻¹ *ᵥ c) ⬝ᵥ c := by
    rw [sqrtSigmaR_mul_self hA' hinv hc]
    simp only [sigmaR]
    exact dotProduct_comm _ _
  have hs : 0 < sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := sqrtSigmaR_pos hA' hinv hc
  refine ⟨(-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)))
    • ((stepShape N A c p ρ)⁻¹ *ᵥ c), ?_, ?_⟩
  · have hAw : (stepShape N A c p ρ) *ᵥ
        ((-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)))
          • ((stepShape N A c p ρ)⁻¹ *ᵥ c))
        = (-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c))) • c := by
      rw [Matrix.mulVec_smul, hinv]
    rw [qfR, hAw,
      show ((-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)))
            • ((stepShape N A c p ρ)⁻¹ *ᵥ c)) ⬝ᵥ
          ((-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c))) • c)
        = (-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)))
            * (-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)))
            * (((stepShape N A c p ρ)⁻¹ *ᵥ c) ⬝ᵥ c) from by
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring]
    rw [show ((stepShape N A c p ρ)⁻¹ *ᵥ c) ⬝ᵥ c
        = sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
          * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) from hss.symm]
    field_simp
  · intro z hz
    have hAw : (stepShape N A c p ρ) *ᵥ
        ((-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)))
          • ((stepShape N A c p ρ)⁻¹ *ᵥ c))
        = (-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c))) • c := by
      rw [Matrix.mulVec_smul, hinv]
    rw [hAw, dotProduct_smul, smul_eq_mul]
    have hneg : (z - stepCentre N a c p ρ) ⬝ᵥ c
        = -(c ⬝ᵥ (stepCentre N a c p ρ - z)) := by
      rw [show z - stepCentre N a c p ρ = -(stepCentre N a c p ρ - z) from by abel,
        neg_dotProduct, dotProduct_comm (stepCentre N a c p ρ - z) c]
    rw [hneg]
    have h3 := reuse_le_ceiling hN hA hc hAp hρ hsupp hz
    have h4 : (-(1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)))
        * (-(c ⬝ᵥ (stepCentre N a c p ρ - z)))
        = (1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c))
          * (c ⬝ᵥ (stepCentre N a c p ρ - z)) := by ring
    rw [h4]
    have h5 : (1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c))
        * (c ⬝ᵥ (stepCentre N a c p ρ - z))
        ≤ (1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c))
          * ((1 / (N : ℝ)) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h6 : (1 / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c))
        * ((1 / (N : ℝ)) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)) = 1 / (N : ℝ) := by
      field_simp
    linarith [h5, h6.le, h6.ge]

#print axioms QMCLeafB.Ss40M3.reuse_round_w

/-- **THE CLOSING MOVE (record form).**  At ceiling `1/N` the next round admits a FULL cut recording
in the sense of `Check_lm38_m5.recording_iff`: a normal, a witness, a depth `ρ ≤ 1/N` and a slack
`del` with `del² ≤ ρ²(c·p)` — the whole ledger, at the enlarged constant. -/
theorem reuse_records {N : ℕ} (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {B : Set (Fin N → ℝ)} (hsupp : ∀ z ∈ B, c ⬝ᵥ (a - z) ≤ 0) :
    ∃ (c' p' : Fin N → ℝ) (ρ' del' : ℝ), c' ≠ 0 ∧ (stepShape N A c p ρ) *ᵥ p' = c' ∧
      0 ≤ ρ' ∧ ρ' ≤ 1 / (N : ℝ) ∧ 0 ≤ del' ∧ del' ^ 2 ≤ ρ' ^ 2 * (c' ⬝ᵥ p') ∧
      ∀ z ∈ B, -del' ≤ c' ⬝ᵥ (z - stepCentre N a c p ρ) := by
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hN hA hc hAp hρ
  have ht : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  exact (QMCLeafB.Lm38M5.recording_iff hA' B (stepCentre N a c p ρ) ht).mpr
    (reuse_round_w hN hA hc hAp hρ hsupp)

#print axioms QMCLeafB.Ss40M3.reuse_records

/-! ## 3.  What the enlargement does NOT buy: the ledger's slack does not compose

The hope after §1 is that a round whose slack `del` is spent can be followed by another legal round.
It cannot, and the failure is exact: a body point that spends the ledger's whole allowance sits at
next-round normalised depth `(1+ρN)/(N+ρ)`, which exceeds the leaf's `1/N` for every `ρ > 0`. -/

/-- **The exact step identity.**  After one step the reused normal sees `c·(a−z) + γ√σ`: the centre
moves `γ√σ` in the cut direction and nothing else changes. -/
theorem step_dot_eq {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a z : Fin N → ℝ} {ρ : ℝ} :
    c ⬝ᵥ (stepCentre N a c p ρ - z) = c ⬝ᵥ (a - z) + gammaR N ρ * sqrtSigmaR c p := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hrr : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  have hstep : stepCentre N a c p ρ - z = (a - z) + (gammaR N ρ / sqrtSigmaR c p) • p := by
    rw [stepCentre]; abel
  rw [hstep, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h2 : (gammaR N ρ / sqrtSigmaR c p) * (c ⬝ᵥ p) = gammaR N ρ * sqrtSigmaR c p := by
    rw [show c ⬝ᵥ p = sqrtSigmaR c p * sqrtSigmaR c p from hrr.symm]
    have hsne : sqrtSigmaR c p ≠ 0 := ne_of_gt (sqrtSigmaR_pos hA hAp hc)
    field_simp
  linarith [h2]

#print axioms QMCLeafB.Ss40M3.step_dot_eq

/-- **THE ATTAINED SLACK POINT.**  The body point spending the ledger's entire allowance at `(A, a)`:
`z₀ = a − (ρ/√σ)·p`, i.e. `c·(a−z₀) = ρ√σ`.  (Nothing larger is admissible: `del² ≤ ρ²σ`.) -/
theorem slack_point_value {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ} :
    c ⬝ᵥ (a - (a - ((ρ * sqrtSigmaR c p) / sigmaR c p) • p))
      = ρ * sqrtSigmaR c p := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hσne : sigmaR c p ≠ 0 := ne_of_gt hσ
  have hrr : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  rw [show a - (a - ((ρ * sqrtSigmaR c p) / sigmaR c p) • p)
      = ((ρ * sqrtSigmaR c p) / sigmaR c p) • p from by abel]
  rw [dotProduct_smul, smul_eq_mul]
  rw [show c ⬝ᵥ p = sqrtSigmaR c p * sqrtSigmaR c p from hrr.symm]
  field_simp
  rw [pow_three, hrr]
  ring

#print axioms QMCLeafB.Ss40M3.slack_point_value

/-- **THE SLACKED RATIO, EXACTLY.**  The point at the ledger's maximum slack produces next-round
normalised depth `(1+ρN)/(N+ρ)` — the value the campaign's `reuse_short_of_leaf` compares with the
ceiling. -/
theorem slack_ratio_eq {N : ℕ} (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    c ⬝ᵥ (stepCentre N a c p ρ - (a - ((ρ * sqrtSigmaR c p) / sigmaR c p) • p))
        / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      = (1 + ρ * (N : ℝ)) / ((N : ℝ) + ρ) := by
  have hs : 0 < sqrtSigmaR c p := sqrtSigmaR_pos hA hAp hc
  have hsne : sqrtSigmaR c p ≠ 0 := ne_of_gt hs
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  rw [step_dot_eq hA hc hAp, slack_point_value hA hc hAp,
    QMCLeafB.Eq38M2.sqrtSigmaR_inv_stepShape hN hA hc hAp hρ0, gammaR]
  field_simp
  ring

#print axioms QMCLeafB.Ss40M3.slack_ratio_eq

/-- **THE SLACKED RATIO EXCEEDS THE CEILING.**  `1/N < (1+ρN)/(N+ρ)` for every `ρ > 0`, `N ≥ 2`. -/
theorem slack_ratio_gt {N : ℕ} (hN : 2 ≤ N) {ρ : ℝ} (hρ : 0 < ρ) :
    1 / (N : ℝ) < (1 + ρ * (N : ℝ)) / ((N : ℝ) + ρ) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have hkey : (1 + ρ * (N : ℝ)) / ((N : ℝ) + ρ) - 1 / (N : ℝ)
      = (ρ * ((N : ℝ) ^ 2 - 1)) / (((N : ℝ) + ρ) * (N : ℝ)) := by
    field_simp
    ring
  have hpos : 0 < (ρ * ((N : ℝ) ^ 2 - 1)) / (((N : ℝ) + ρ) * (N : ℝ)) := by
    apply div_pos _ (by positivity)
    have h1 : (1 : ℝ) < (N : ℝ) ^ 2 := by nlinarith
    nlinarith
  linarith [hkey, hpos]

#print axioms QMCLeafB.Ss40M3.slack_ratio_gt

/-- **`ρ = 0` FORCES `del = 0`.**  The ledger's check `del² ≤ ρ²σ` leaves no slack at zero depth, so
the only depth at which the slacked ratio meets the ceiling (`ρ = 0`) is also the only depth at which
the ledger demands exact support. -/
theorem del_zero_of_rho_zero {ρ del σ : ℝ} (hρ : ρ = 0) (hdel0 : 0 ≤ del)
    (hchk : del ^ 2 ≤ ρ ^ 2 * σ) : del = 0 := by
  subst hρ
  nlinarith [sq_nonneg del]

#print axioms QMCLeafB.Ss40M3.del_zero_of_rho_zero

/-- **THE SLACK DOES NOT COMPOSE.**  If the body spends the ledger's entire allowance at `(A, a)` —
the point `z₀ = a − (ρ/√σ)·p` with `0 < ρ` — then the reused normal sees `z₀` at the NEXT round at
normalised depth `> 1/N`: beyond the leaf's ceiling, at every `N ≥ 2`.  So a round with `del > 0`
cannot be followed by a legal round in the reused direction, however the ceiling is enlarged; only
`del = 0` (exact support) propagates, and at `ρ = 0` the ledger forces `del = 0`. -/
theorem slack_no_reuse {N : ℕ} (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : 0 < ρ) :
    1 / (N : ℝ) <
      c ⬝ᵥ (stepCentre N a c p ρ - (a - ((ρ * sqrtSigmaR c p) / sigmaR c p) • p))
        / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by
  rw [slack_ratio_eq hN hA hc hAp hρ0]
  exact slack_ratio_gt hN hρ

#print axioms QMCLeafB.Ss40M3.slack_no_reuse

/-! ## 4.  The engine's own transcript

`Aat`/`Cat` are the engine's exact iterates; the round's leaf obligation is stated about them in
`∃w`-form.  §2 transports across `Cat_unfold` and `rStep_cast`. -/

/-- **THE CLOSING MOVE ON THE ENGINE'S OWN DATA.**  A round of the engine's transcript whose recorded
normal supports the relaxation at the accumulated centre leaves the leaf's `∃w` round condition at the
NEXT iterate, at ceiling `1/N`. -/
theorem engine_round_after_support {N : ℕ} (hN : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ}
    {cd : ℕ → CutData N} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {B : Set (Fin N → ℝ)} {a0 : Fin N → ℝ} (k : ℕ)
    (hsupp : ∀ z ∈ B, cutCR cd k ⬝ᵥ (Cat N a0 cd k - z) ≤ 0) :
    ∃ w : Fin N → ℝ,
      qfR (castM (Aat N A0 cd (k + 1))) w = 1 ∧
        ∀ z ∈ B,
          (z - Cat N a0 cd (k + 1)) ⬝ᵥ ((castM (Aat N A0 cd (k + 1))) *ᵥ w) ≤ 1 / (N : ℝ) := by
  have hAk : (castM (Aat N A0 cd k)).PosDef := Aat_cast_posDef hN hA0 hwit hρ hcne k
  have hpw : castM (Aat N A0 cd k) *ᵥ cutPR cd k = cutCR cd k := cast_witness hwit k
  have hcR : cutCR cd k ≠ 0 := cast_normal_ne (hcne k)
  have hround := reuse_round_w hN hAk hcR hpw (a := Cat N a0 cd k)
    (ρ := ((cd k).rho : ℝ)) (by exact_mod_cast hρ k) hsupp
  simpa only [Cat_unfold, Aat_unfold, rStep_cast] using hround

#print axioms QMCLeafB.Ss40M3.engine_round_after_support

/-- The same, in the round's full cut-record form (the ledger included), at the engine's next
iterate and ceiling `1/N`. -/
theorem engine_round_records {N : ℕ} (hN : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ}
    {cd : ℕ → CutData N} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {B : Set (Fin N → ℝ)} {a0 : Fin N → ℝ} (k : ℕ)
    (hsupp : ∀ z ∈ B, cutCR cd k ⬝ᵥ (Cat N a0 cd k - z) ≤ 0) :
    ∃ (c' p' : Fin N → ℝ) (ρ' del' : ℝ),
      c' ≠ 0 ∧ (castM (Aat N A0 cd (k + 1))) *ᵥ p' = c' ∧
        0 ≤ ρ' ∧ ρ' ≤ 1 / (N : ℝ) ∧ 0 ≤ del' ∧ del' ^ 2 ≤ ρ' ^ 2 * (c' ⬝ᵥ p') ∧
          ∀ z ∈ B, -del' ≤ c' ⬝ᵥ (z - Cat N a0 cd (k + 1)) := by
  have hAk : (castM (Aat N A0 cd k)).PosDef := Aat_cast_posDef hN hA0 hwit hρ hcne k
  have hpw : castM (Aat N A0 cd k) *ᵥ cutPR cd k = cutCR cd k := cast_witness hwit k
  have hcR : cutCR cd k ≠ 0 := cast_normal_ne (hcne k)
  have hround := reuse_records hN hAk hcR hpw (a := Cat N a0 cd k)
    (ρ := ((cd k).rho : ℝ)) (by exact_mod_cast hρ k) hsupp
  simpa only [Cat_unfold, Aat_unfold, rStep_cast] using hround

#print axioms QMCLeafB.Ss40M3.engine_round_records

/-! ## 5.  The headline: what the closing move is, and what it is not -/

/-- **THE CLOSING MOVE, IN ONE STATEMENT.**  At the enlarged ceiling `rmax = 1/N`:

* `1/N` really is above the reuse ratio at every legal depth (§1);
* an exactly supporting round DOES propagate: the next round satisfies the leaf's `∃w` condition at
  `1/N` (`reuse_round_w`);
* the ledger's slack does NOT propagate: the point spending `del = ρ√σ` with `ρ > 0` sits at
  next-round depth `> 1/N`.

So the enlargement removes the factor `4` for one round at a time, from support — and the leaf's
remaining hypothesis stays *separation*, not an estimate. -/
theorem closing_move_summary {N : ℕ} (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ}
    {B : Set (Fin N → ℝ)} (hsupp : ∀ z ∈ B, c ⬝ᵥ (a - z) ≤ 0) :
    (∀ ρ : ℝ, 0 ≤ ρ → (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (N : ℝ))
      ∧ (∀ ρ : ℝ, 0 ≤ ρ → ∃ w : Fin N → ℝ,
          qfR (stepShape N A c p ρ) w = 1 ∧
            ∀ z ∈ B, (z - stepCentre N a c p ρ) ⬝ᵥ ((stepShape N A c p ρ) *ᵥ w)
              ≤ 1 / (N : ℝ))
      ∧ (∀ ρ : ℝ, 0 ≤ ρ → 0 < ρ →
          ∀ z : Fin N → ℝ, z = a - ((ρ * sqrtSigmaR c p) / sigmaR c p) • p →
            c ⬝ᵥ (a - z) = ρ * sqrtSigmaR c p ∧
              1 / (N : ℝ) < c ⬝ᵥ (stepCentre N a c p ρ - z)
                / sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)) := by
  refine ⟨fun ρ hρ => one_sub_div_le_inv N (by omega) hρ,
    fun ρ hρ => reuse_round_w hN hA hc hAp hρ hsupp, ?_⟩
  intro ρ hρ0 hρ z hz
  subst hz
  exact ⟨slack_point_value hA hc hAp, slack_no_reuse hN hA hc hAp hρ0 hρ⟩

#print axioms QMCLeafB.Ss40M3.closing_move_summary

/-! ## 6.  The leaf from a shallow-cut stream: the exact one-hypothesis remainder

`Check_rf38_m1.solution_of_separating` fires the leaf from a stream whose rounds are recorded with
`del ≡ 0` (an exact supporting hyperplane at every accumulated centre).  The same assembly goes
through with `del` free inside the ledger's allowance: the last binder below is `ShallowCut`, and every
exactly supporting stream is one.  So the leaf's remainder is *not* exact separation — it is the
per-round shallow-cut record, and §3 shows the time this buys is exactly one round per supporting cut. -/

/-- **THE LEAF FROM A SHALLOW-CUT STREAM.**  `FinishLine.SolutionStatement` from `{Automatic.Poly}`
bit + `{1 ≤ K·m}` + top slice + upper slot + `{ShallowCut}` at every bit-false point in the band.
`ShallowCut` allows a recorded slack `0 ≤ del ≤ rmax·√σ` at every round, so this hypothesis is implied
by — and is strictly weaker than — `m1`'s `SepStream`. -/
theorem solution_of_shallowCut
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (H : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = false →
      QMCLeafB.ThinRec34M4.ShallowCut G t (P G) hn) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (fun G t hn hlo hlt hb =>
      QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn (H G t hn hlo hlt hb))

#print axioms QMCLeafB.Ss40M3.solution_of_shallowCut

/-- **RECOVERY OF PHASE 38's LEAF FORM.**  An exactly supporting rational stream (the content of
`Check_rf38_m1.SepStream`, verbatim, but stated here so this bundle owes no `Solutions.*` import)
implies `ShallowCut`, hence the leaf.  So §6.1 strictly generalises `solution_of_separating`. -/
theorem shallowCut_of_supportingStream {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      (fun i => (((c k) i : ℚ) : ℝ))
          ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
        ≤ (fun i => (((c k) i : ℚ) : ℝ)) ⬝ᵥ z) :
    QMCLeafB.ThinRec34M4.ShallowCut G t P hn :=
  QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P) hn c hc hsep

#print axioms QMCLeafB.Ss40M3.shallowCut_of_supportingStream

/-- **AND THEREFORE THE LEAF, FROM SEPARATION** — the phase-38 one-hypothesis form, re-derived through
the shallow-cut interface of §6. -/
theorem solution_of_supportingStream
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      ∀ k, k < (P G).K * (P G).m → ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t (P G),
        (fun i => (((c G t k) i : ℚ) : ℝ))
            ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.ThinRec34M4.NormalCut G (P G) hn (c G t) (hc G t)) k
          ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (fun G t hn hlo hlt hb =>
      QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
        (shallowCut_of_supportingStream hn (c G t) (hc G t) (hsep G t hn)))

#print axioms QMCLeafB.Ss40M3.solution_of_supportingStream

/-! ## 7.  THE DECISIVE OBSTRUCTION: `rmax = 1/n²` is not an admissible `RunParams` ceiling

The phase-40 brief assumes that "a LARGER `rmax` gives a FASTER contraction, so the halving and budget
constraints get easier".  That is **inverted**, and it kills the parameter change.

`RunParams.hhalve` is `(√(rho0R (n·n) rmax))⁻¹ ^ m ≤ 1/2`.  `rho0R` is the one-step determinant factor
(`Def_QMCLeafB_EngineIterates.stepShape_det`), so `rho0R > 1` is exactly *contraction of the shape
matrix*; with `rho0R ≤ 1` the left side is `≥ 1` for every `m` and `hhalve` is unsatisfiable.  Since
`rho0R` is ANTITONE in the depth (`rho0R_anti`), **enlarging `rmax` makes `hhalve` harder**.  And at the
campaign's smallest order `n = 2` (ellipsoid dimension `2·2 = 4`) the enlarged ceiling `1/n² = 1/4`
already has `rho0R 4 (1/4) < 1`.  Hence no `RunParams` at `rmax = 1/(n·n)` exists at `n = 2`: the
closing move's parameter family is EMPTY, so the leaf (a statement about every `G` with `2 ≤ G.n`)
cannot be assembled at it.  The enlarged ceiling must be abandoned, not re-discharged. -/

/-- **`hhalve` DEMANDS `rho0R > 1`.**  With a positive one-step factor, a halving witness forces the
factor above `1`; at `rho0R ≤ 1` the left side is `≥ 1 > 1/2` for every `m`. -/
theorem one_lt_rho0R_of_hhalve {N m : ℕ} {ρ : ℝ}
    (hpos : 0 < QMCLeafB.EngineIterates.rho0R N ρ)
    (h : (Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ))⁻¹ ^ m ≤ 1 / 2) :
    1 < QMCLeafB.EngineIterates.rho0R N ρ := by
  by_contra hle
  push_neg at hle
  have hs1 : Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ) ≤ 1 := Real.sqrt_le_one.2 hle
  have hs0 : 0 < Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ) := Real.sqrt_pos.2 hpos
  have hinv : 1 ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ))⁻¹ := by
    rw [← one_div]
    exact (one_le_div hs0).2 hs1
  have hp : 1 ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R N ρ))⁻¹ ^ m := one_le_pow₀ hinv
  linarith

#print axioms QMCLeafB.Ss40M3.one_lt_rho0R_of_hhalve

/-- **A LARGER CEILING MAKES `hhalve` HARDER, not easier**: a halving witness at the larger ceiling
`ρ'` transfers to the smaller ceiling `ρ` (same `m`), never the other way round. -/
theorem hhalve_of_le_ceiling {n : ℕ} (hn : 2 ≤ n) {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (hle : ρ ≤ ρ') {m : ℕ}
    (h : (Real.sqrt (QMCLeafB.EngineIterates.rho0R n ρ'))⁻¹ ^ m ≤ 1 / 2) :
    (Real.sqrt (QMCLeafB.EngineIterates.rho0R n ρ))⁻¹ ^ m ≤ 1 / 2 := by
  have hanti : QMCLeafB.EngineIterates.rho0R n ρ' ≤ QMCLeafB.EngineIterates.rho0R n ρ :=
    QMCLeafB.EngineIterates.rho0R_anti hn hρ hle
  have hpos : 0 < QMCLeafB.EngineIterates.rho0R n ρ :=
    QMCLeafB.EngineIterates.rho0R_pos hn hρ
  have hpos' : 0 < QMCLeafB.EngineIterates.rho0R n ρ' :=
    QMCLeafB.EngineIterates.rho0R_pos hn (le_trans hρ hle)
  have hs : Real.sqrt (QMCLeafB.EngineIterates.rho0R n ρ')
      ≤ Real.sqrt (QMCLeafB.EngineIterates.rho0R n ρ) := Real.sqrt_le_sqrt hanti
  have hs0 : 0 < Real.sqrt (QMCLeafB.EngineIterates.rho0R n ρ') := Real.sqrt_pos.2 hpos'
  have hinv : (Real.sqrt (QMCLeafB.EngineIterates.rho0R n ρ))⁻¹
      ≤ (Real.sqrt (QMCLeafB.EngineIterates.rho0R n ρ'))⁻¹ := inv_anti₀ hs0 hs
  exact le_trans (pow_le_pow_left₀ (by positivity) hinv m) h

#print axioms QMCLeafB.Ss40M3.hhalve_of_le_ceiling

/-- **THE NUMBER.**  At the campaign's smallest order (`n = 2`, ellipsoid dimension `4`) the enlarged
ceiling `rmax = 1/n² = 1/4` already has `rho0R 4 (1/4) = 5529600000/6975757441 < 1`: the shape
matrix EXPANDS, so the potential does not halve at any `m`. -/
theorem rho0R_four_quarter_lt_one :
    QMCLeafB.EngineIterates.rho0R 4 ((1 / 4 : ℚ) : ℝ) < 1 := by
  rw [QMCLeafB.EngineIterates.rho0R]
  norm_num

#print axioms QMCLeafB.Ss40M3.rho0R_four_quarter_lt_one

/-- **NO `RunParams` AT THE CLOSING MOVE'S CONSTANT (n = 2).**  At `G.n = 2` the enlarged ceiling
`rmax = 1/n² = 1/4` admits no `RunParams` at all: `hhalve` is unsatisfiable because `rho0R 4 (1/4) < 1`.
(The campaign's actual constant `rmaxOf 4 = 1/16` is fine: `rho0R 4 (1/16) = 1.137…> 1`.) -/
theorem no_runParams_rmax_quarter {G : QuantumMaxCutEnergy.Input} (hG : G.n = 2)
    (P : QMCLeafB.FinalStroke.RunParams G) : P.rmax ≠ 1 / 4 := by
  intro hP
  have hH := P.hhalve
  rw [hG, hP] at hH
  have hH' : (Real.sqrt (QMCLeafB.EngineIterates.rho0R 4 ((1 / 4 : ℚ) : ℝ)))⁻¹
      ^ P.m ≤ 1 / 2 := by simpa using hH
  have hpos : 0 < QMCLeafB.EngineIterates.rho0R 4 ((1 / 4 : ℚ) : ℝ) :=
    QMCLeafB.EngineIterates.rho0R_pos (by norm_num) (by norm_num)
  have hgt := one_lt_rho0R_of_hhalve hpos hH'
  linarith [rho0R_four_quarter_lt_one]

#print axioms QMCLeafB.Ss40M3.no_runParams_rmax_quarter

/-- **AND THE SAME FOR EVERY LARGER CEILING.**  `hhalve` is monotone the wrong way, so once the
enlarged ceiling `1/4` fails at `n = 2`, every `rmax ≥ 1/4` fails too. -/
theorem no_runParams_rmax_ge_quarter {G : QuantumMaxCutEnergy.Input} (hG : G.n = 2)
    (P : QMCLeafB.FinalStroke.RunParams G) (hq : 1 / 4 ≤ P.rmax) : False := by
  have hH := P.hhalve
  rw [hG] at hH
  have hqQ : ((1 / 4 : ℚ) : ℝ) ≤ ((P.rmax : ℚ) : ℝ) := by exact_mod_cast hq
  have hρ0 : (0 : ℝ) ≤ (1 / 4 : ℚ) := by norm_num
  have hsmall : (Real.sqrt (QMCLeafB.EngineIterates.rho0R (2 * 2) ((1 / 4 : ℚ) : ℝ)))⁻¹
      ^ P.m ≤ 1 / 2 :=
    hhalve_of_le_ceiling (n := 2 * 2) (by norm_num) hρ0 hqQ hH
  have hpos : 0 < QMCLeafB.EngineIterates.rho0R (2 * 2) ((1 / 4 : ℚ) : ℝ) :=
    QMCLeafB.EngineIterates.rho0R_pos (by norm_num) hρ0
  have hlt : QMCLeafB.EngineIterates.rho0R (2 * 2) ((1 / 4 : ℚ) : ℝ) < 1 :=
    rho0R_four_quarter_lt_one
  have hgt := one_lt_rho0R_of_hhalve hpos hsmall
  linarith

#print axioms QMCLeafB.Ss40M3.no_runParams_rmax_ge_quarter

/-- The campaign's smallest order, as an explicit input (all weights zero): `n = 2`. -/
def inp2 : QuantumMaxCutEnergy.Input := ⟨2, fun _ => 0⟩

theorem inp2_n : inp2.n = 2 := rfl

#print axioms QMCLeafB.Ss40M3.inp2_n

/-- **THE CLOSING MOVE'S PARAMETER FAMILY DOES NOT EXIST.**  There is no family of `RunParams` with
`rmax = 1/(n·n)` — because the leaf needs one such `P` at every `G` with `2 ≤ G.n`, and at `n = 2` the
ceiling `1/(n·n) = 1/4` already makes `hhalve` unsatisfiable (`no_runParams_rmax_quarter`).  So the
constant `1/n²` cannot be re-discharged inside the formalized programme: the closing move is
falsified at the level of its own parameters, independently of any geometry. -/
theorem no_rmaxFamily_inv_sq :
    ¬ ∃ P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G,
        ∀ G : QuantumMaxCutEnergy.Input, (P G).rmax = 1 / ((G.n : ℚ) * (G.n : ℚ)) := by
  rintro ⟨P, hP⟩
  have h2 := hP inp2
  have hquarter : (P inp2).rmax = 1 / 4 := by
    have h2' : (1 : ℚ) / ((2 : ℚ) * 2) = 1 / 4 := by norm_num
    simpa [inp2] using h2.trans h2'
  exact no_runParams_rmax_quarter inp2_n (P inp2) hquarter

#print axioms QMCLeafB.Ss40M3.no_rmaxFamily_inv_sq

end QMCLeafB.Ss40M3


