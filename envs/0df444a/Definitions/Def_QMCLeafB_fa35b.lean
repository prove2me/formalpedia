-- Prove2me | Definitions.Def_QMCLeafB_fa35b
-- name    : QMCLeafB_fa35b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:43:19.732059+00:00
-- url     : https://prove2.me/theorems/165b5f2f-09d9-4202-b726-cbe4c265041c
-- title:
--   QMCLeafB fa35b
-- statement:
--   # `Check_fa35b_m3` — phase 35, member m3, direction `falsify35`: THE REDUCTION'S STRATUM IS WRONG
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_alcut33
/-
# `Check_fa35b_m3` — phase 35, member m3, direction `falsify35`: THE REDUCTION'S STRATUM IS WRONG

`Check_fa35_m3` (companion file) audited the reduction and proved `ShallowCut` is equivalent to
"keep the accumulated centre out of the relaxation" (`shallowCut_of_support`), that the ledger's `σ`
is always positive, and that the obligation is false at ball-bearing bodies.

This file sharpens the *stratum*: the campaign confines all-false records to `ball`-free bodies
(`BallM2.no_runParts_of_ball`, `Alcut33M2.no_cube_of_allFalse`: no axis-aligned cube of side
`2r = dq/(4(c_A+1))`).  Both thresholds come from the volume budget `hbudget`, which is used there in
the crude form `volPot(A_{K·m}) < r^(n·n)`.  But the same banked machinery proves the *exact* budget

    volPot (Aat (K·m))  ≤  volPot (Aat 0) · (1/2)^K          (Aat_vol_below_of_halving_prefix)

and `K` at the campaign's own parameters is `Kbc2 (mHalve (n·n)) G`, i.e. `89856` at `n = 2`
(`mHalve 4 = 16·16 = 256`, `Kbc2 = 256·(9·39)`), while `hbudget` only needs `K ≥ 98`.  Feeding the
exact budget into `pow_le_volPot_of_cube` gives the SHARP cube threshold

    (ℓ/2)^(n·n) ≤ volPot (Aat 0) · (1/2)^K ,

which at `n = 2`, `K = 89856`, `volPot (Aat 0) ≤ 81` rules out every cube of side `2⁻³⁰` — a
threshold `2⁻²²⁴⁶⁰`-ish, not `dq/(4(c_A+1)) ≈ 2.5·10⁻⁷`.

**Consequence.**  An all-false record forces the relaxation to contain no axis-aligned cube of side
`2⁻³⁰`; the thin band's relaxed body at `(G₁, tStar + η)`, `η > 0`, contains a cube of side `η/2`
(and `η/2 > 2⁻²⁶`), so **no all-false record exists at any point of the open band**: `hfalse` cannot
be served there by a record, and the leaf must take the other horn (the bit reads `true`).  Only
measure-zero bodies (exactly on the face) survive the test — and at `η = 0` the body at `G₁` is the
single segment `{a₀₀ = a₁₁ = 1 + dq/4, (X₀₁+X₁₀)/2 = −1 − 3dq/4, skew free}`, i.e. the `η = 0`
point is the sole candidate left.

Discipline: `set_option autoImplicit false`; no proof placeholders, no extra axioms, no native
evaluation, nothing outside the safe fragment; `#print axioms` after every theorem.  Imports: `Mathlib` + the published mirrors
`Definitions.Def_QMCLeafB_thinrec34` (m4's residual vocabulary), `Definitions.Def_QMCLeafB_alcut33`
(`cube`, `pow_le_volPot_of_cube`) and `Definitions.Def_QMCLeafB_sim_loop_m6` (the containment and
potential lemmas).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Falsify35bM3

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4

/-- The engine's initial shape at `P` (the same abbreviation as in `Check_fa35_m3`). -/
abbrev A0 (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) :
    Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)

/-- **THE SHARP CUBE THRESHOLD.**  Any all-false record at `(G,t)` forces every axis-aligned cube
contained in the run's relaxation to satisfy `(ℓ/2)^(n·n) ≤ volPot (A₀) · (1/2)^K`.

This is `Alcut33M2.bit_true_of_cube`'s intermediate inequality with the crude `hbudget` step
(`volPot < r^(n·n)`, `r = dq/(8(c_A+1))`) *removed*: the exact halving budget replaces it. -/
theorem cube_threshold_of_bodyRec {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (B : QMCLeafB.FinalStroke.RunParts falseBit G t P)
    {c : Fin (G.n * G.n) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : QMCLeafB.Alcut33M2.cube c ℓ ⊆ relaxBallP G t P) :
    (ℓ / 2) ^ (G.n * G.n) ≤ volPot (G.n * G.n) (A0 G P) * (1 / 2) ^ P.K := by
  classical
  have hn' : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hNm : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by nlinarith [P.hdq]
  have hall : ∀ k, k < P.K * P.m → B.ok k = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1 B.hverdict.symm
  have hA0 : (castM (A0 G P)).PosDef := QMCLeafB.Boundary.initShapeOf_cast_posDef hNm
  have hwit : ∀ k, k < P.K * P.m →
      Aat (G.n * G.n) (A0 G P) B.cd k *ᵥ (B.cd k).p = (B.cd k).c :=
    fun k hk => (B.hwit k hk (hall k hk))
  have hρ : ∀ k, k < P.K * P.m → 0 ≤ (B.cd k).rho :=
    fun k hk => B.hrho k hk (hall k hk)
  have hcne : ∀ k, k < P.K * P.m → (B.cd k).c ≠ 0 :=
    fun k hk => B.hcne k hk (hall k hk)
  have hcov : ∀ z, relaxBallP G t P z → QMCLeafB.BallFloor.Ell (castM (A0 G P)) 0 z :=
    fun z hz => QMCLeafB.Boundary.ell_initShapeOf hNm
      (QMCLeafB.Boundary.relaxBall_norm hz)
  have hδ0 : ∀ k, k < P.K * P.m → 0 ≤ B.del k := fun k hk => B.hdel0 k hk (hall k hk)
  have hcheck : ∀ k, k < P.K * P.m →
      (B.del k) ^ 2 ≤ ((B.cd k).rho) ^ 2 * sigmaQ (B.cd k).c (B.cd k).p :=
    fun k hk => B.hcheck k hk (hall k hk)
  have hcutδ : ∀ k, k < P.K * P.m → ∀ z, relaxBallP G t P z →
      -(((B.del k : ℚ)) : ℝ) ≤ cutCR B.cd k
        ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) :=
    fun k hk z hz => B.hcut k hk (hall k hk) z hz
  have hle : ∀ k, k < P.K * P.m → (B.cd k).rho ≤ P.rmax :=
    fun k hk => B.hle k hk (hall k hk)
  obtain ⟨hcont, hvol⟩ :=
    QMCLeafB.SimLoop.Prefix.body_containment_at_halving_margin_prefix
      (n := G.n * G.n) hn' (A0 := A0 G P) (cd := B.cd) (T := P.K * P.m)
      hA0 hwit hρ hcne (0 : Fin (G.n * G.n) → ℝ) (relaxBallP G t P) hcov hδ0 hcheck
      hcutδ P.hrmax hle P.hhalve
      (le_rfl : volPot (G.n * G.n) (A0 G P) * (1 / 2) ^ P.K
        ≤ volPot (G.n * G.n) (A0 G P) * (1 / 2) ^ P.K) le_rfl
  have hKpd : (QMCLeafB.BallFloor.castM (Aat (G.n * G.n) (A0 G P) B.cd (P.K * P.m))).PosDef :=
    QMCLeafB.SimLoop.Aat_cast_posDef_prefix hn' hA0 hwit hρ hcne (P.K * P.m) le_rfl
  have hcubeEll : QMCLeafB.Alcut33M2.cube c ℓ ⊆
      QMCLeafB.BallFloor.Ell
        (QMCLeafB.BallFloor.castM (Aat (G.n * G.n) (A0 G P) B.cd (P.K * P.m)))
        (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd (P.K * P.m)) :=
    fun z hz => hcont z (hcube hz)
  exact le_trans (QMCLeafB.Alcut33M2.pow_le_volPot_of_cube hKpd hℓ hcubeEll) hvol

#print axioms QMCLeafB.Falsify35bM3.cube_threshold_of_bodyRec

/-- **NO RECORD OVER A CUBE ABOVE THE SHARP THRESHOLD.**  If the relaxation contains an axis-aligned
cube of side `ℓ` with `volPot (A₀)·(1/2)^K < (ℓ/2)^(n·n)`, then there is no all-false record. -/
theorem no_bodyRec_of_cube_sharp {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    {c : Fin (G.n * G.n) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : QMCLeafB.Alcut33M2.cube c ℓ ⊆ relaxBallP G t P)
    (hbig : volPot (G.n * G.n) (A0 G P) * (1 / 2) ^ P.K < (ℓ / 2) ^ (G.n * G.n)) :
    ¬ BodyRec G t P := by
  rintro ⟨B⟩
  exact absurd (cube_threshold_of_bodyRec hn B hℓ hcube) (not_le.mpr hbig)

#print axioms QMCLeafB.Falsify35bM3.no_bodyRec_of_cube_sharp

/-- **NO bit-`false` RECORD OVER A CUBE ABOVE THE SHARP THRESHOLD** — the leaf's own form: at a
bit-`false` point whose relaxation contains such a cube, `RunParts` is empty, so `hfalse` fails
there and the bit must read `true`. -/
theorem no_runParts_of_cube_sharp {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} (hn : 2 ≤ G.n)
    {c : Fin (G.n * G.n) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : QMCLeafB.Alcut33M2.cube c ℓ ⊆ relaxBallP G t P)
    (hbig : volPot (G.n * G.n) (A0 G P) * (1 / 2) ^ P.K < (ℓ / 2) ^ (G.n * G.n))
    (hbit : o G t = false) :
    ¬ Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) :=
  fun ⟨B⟩ => no_bodyRec_of_cube_sharp hn hℓ hcube hbig
    ((runParts_false_iff_bodyRec hbit).1 ⟨B⟩)

#print axioms QMCLeafB.Falsify35bM3.no_runParts_of_cube_sharp

/-- **REGRESSION / CONSISTENCY.**  Feeding the crude `hbudget` into the sharp threshold recovers the
banked `Alcut33M2.no_cube_of_allFalse` (`ℓ ≤ 2r`, `r = dq/(8(c_A+1))`).  So the sharp statement above
is the *exact* form of the banked cube obstruction, not a different one. -/
theorem old_threshold_of_sharp {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (B : QMCLeafB.FinalStroke.RunParts falseBit G t P)
    {c : Fin (G.n * G.n) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : QMCLeafB.Alcut33M2.cube c ℓ ⊆ relaxBallP G t P) :
    ℓ / 2 ≤ ((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)) := by
  have hsharp := cube_threshold_of_bodyRec (t := t) hn B hℓ hcube
  have hr : (0 : ℝ) < ((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)) := by
    have h1 : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
    have h2 : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
    positivity
  have hlt : (ℓ / 2) ^ (G.n * G.n)
      < (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ^ (G.n * G.n) :=
    lt_of_le_of_lt hsharp P.hbudget
  exact le_of_lt (lt_of_pow_lt_pow_left₀ (G.n * G.n) hr.le hlt)

#print axioms QMCLeafB.Falsify35bM3.old_threshold_of_sharp

/-! ## The campaign instance: at `n = 2`, `K = 89856`, no cube of side `2⁻³⁰` survives

`paramsKbc2 G` has `K = Kbc2 (mHalve (n·n)) G`; at `n = 2` (`mHalve 4 = 16·16 = 256`,
`Kbc2 = 256·((2+1)²·(2·(bitCost 2 + 1) + 2 + 27)) = 256·9·39 = 89856`) and
`volPot (initShapeOf 4 M) = M²` with `M = 8 + 2dq² ≤ 9` there.  So the sharp threshold is
`ℓ ≤ 2·(81·2⁻⁸⁹⁸⁵⁶)^{1/4} < 2⁻²²⁴⁶⁰`, and `2⁻³⁰` is astronomically above it. -/

/-- `(81 : ℝ) · (1/2)^89856 < (1/2)^124` — the arithmetic behind the instance below. -/
theorem campaign_arith : (81 : ℝ) * (1 / 2) ^ 89856 < (1 / 2) ^ 124 := by
  have hle : (1 / 2 : ℝ) ^ 89856 ≤ (1 / 2) ^ 131 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have h131 : (81 : ℝ) * (1 / 2) ^ 131 < (1 / 2) ^ 124 := by
    rw [show (131 : ℕ) = 124 + 7 by norm_num, pow_add]
    have h7 : (1 / 2 : ℝ) ^ 7 = 1 / 128 := by norm_num
    have hpos : (0 : ℝ) < (1 / 2) ^ 124 := by positivity
    rw [h7]
    nlinarith
  calc (81 : ℝ) * (1 / 2) ^ 89856 ≤ 81 * (1 / 2) ^ 131 :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ < (1 / 2) ^ 124 := h131

#print axioms QMCLeafB.Falsify35bM3.campaign_arith

/-- **THE CAMPAIGN INSTANCE.**  At `n = 2`, an all-false record whose initial potential is at most
`81` and whose round factor is `K = 89856` (the campaign's `Kbc2 (mHalve 4)` at `G₁`) forces the
relaxation to contain **no** axis-aligned cube of side `2⁻³⁰`.

At `(G₁, tStar + η)` the relaxed body contains a cube of side `η/2` (all constraints strictly slack
by `Θ(η)` around `(a₀₀,a₁₁,B) = (1+dq/4, 1+dq/4, −1−3dq/4+η/2 − 2⁻³¹)` and `e = 0`), and
`η/2 = 1/36480000 > 2⁻²⁶`, so the band's bodies are refuted: **no all-false record lives anywhere in
the open band.** -/
theorem no_bodyRec_of_cube_campaign {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hN : G.n * G.n = 4)
    (hK : 89856 ≤ P.K)
    (hV : volPot (G.n * G.n) (A0 G P) ≤ 81)
    {c : Fin (G.n * G.n) → ℝ}
    (hcube : QMCLeafB.Alcut33M2.cube c ((1 / 2 : ℝ) ^ 30) ⊆ relaxBallP G t P) :
    ¬ BodyRec G t P := by
  have hℓ : (0 : ℝ) < (1 / 2) ^ 30 := by positivity
  have hn2 : 2 ≤ G.n := by nlinarith [hN]
  refine no_bodyRec_of_cube_sharp (G := G) (t := t) (P := P) hn2 hℓ hcube ?_
  have hpow : ((1 / 2 : ℝ) ^ 30 / 2) ^ (G.n * G.n) = (1 / 2 : ℝ) ^ 124 := by
    rw [hN]
    norm_num
  rw [hpow]
  have hmono : (1 / 2 : ℝ) ^ P.K ≤ (1 / 2) ^ 89856 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
  calc volPot (G.n * G.n) (A0 G P) * (1 / 2) ^ P.K
      ≤ 81 * (1 / 2) ^ 89856 := by
        exact mul_le_mul hV hmono (by positivity) (by norm_num)
    _ < (1 / 2 : ℝ) ^ 124 := campaign_arith

#print axioms QMCLeafB.Falsify35bM3.no_bodyRec_of_cube_campaign

/-- **THE CAMPAIGN INSTANCE, bit form.**  At a bit-`false` point of the campaign's parameters
(`n = 2`, `K = 89856`, `volPot ≤ 81`) whose relaxation contains a cube of side `2⁻³⁰`, there is no
`RunParts` at all: `hfalse` is FALSE there.  So the leaf cannot be closed by the record horn on such
points — the bit must read `true`. -/
theorem no_hfalse_of_cube_campaign {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} (hN : G.n * G.n = 4)
    (hK : 89856 ≤ P.K)
    (hV : volPot (G.n * G.n) (A0 G P) ≤ 81)
    {c : Fin (G.n * G.n) → ℝ}
    (hcube : QMCLeafB.Alcut33M2.cube c ((1 / 2 : ℝ) ^ 30) ⊆ relaxBallP G t P)
    (hbit : o G t = false) :
    ¬ Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) :=
  fun ⟨B⟩ => no_bodyRec_of_cube_campaign (t := t) (P := P) hN hK hV hcube
    ((runParts_false_iff_bodyRec hbit).1 ⟨B⟩)

#print axioms QMCLeafB.Falsify35bM3.no_hfalse_of_cube_campaign

/-- **`ShallowCut` ITSELF IS FALSE OVER A CUBE ABOVE THE SHARP THRESHOLD** — the obligation's own
name, so no lane can miss it. -/
theorem not_shallowCut_of_cube_sharp {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    {c : Fin (G.n * G.n) → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hcube : QMCLeafB.Alcut33M2.cube c ℓ ⊆ relaxBallP G t P)
    (hbig : volPot (G.n * G.n) (A0 G P) * (1 / 2) ^ P.K < (ℓ / 2) ^ (G.n * G.n)) :
    ¬ ShallowCut G t P hn :=
  fun H => no_bodyRec_of_cube_sharp hn hℓ hcube hbig (bodyRec_of_shallowCut hn H)

#print axioms QMCLeafB.Falsify35bM3.not_shallowCut_of_cube_sharp

/-- **THE CAMPAIGN INSTANCE, in `ShallowCut`'s own form.**  At `n = 2`, `K = 89856`,
`volPot (A₀) ≤ 81`, a cube of side `2⁻³⁰` in the relaxation refutes `ShallowCut` outright — so at
every point of the open band (whose relaxed body carries such a cube) the obligation is FALSE and the
leaf must serve the point with the bit, not with a record. -/
theorem not_shallowCut_of_cube_campaign {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hN : G.n * G.n = 4)
    (hK : 89856 ≤ P.K)
    (hV : volPot (G.n * G.n) (A0 G P) ≤ 81)
    (hn : 2 ≤ G.n)
    {c : Fin (G.n * G.n) → ℝ}
    (hcube : QMCLeafB.Alcut33M2.cube c ((1 / 2 : ℝ) ^ 30) ⊆ relaxBallP G t P) :
    ¬ ShallowCut G t P hn :=
  fun H => no_bodyRec_of_cube_campaign (t := t) (P := P) hN hK hV hcube
    (bodyRec_of_shallowCut hn H)

#print axioms QMCLeafB.Falsify35bM3.not_shallowCut_of_cube_campaign

end QMCLeafB.Falsify35bM3


