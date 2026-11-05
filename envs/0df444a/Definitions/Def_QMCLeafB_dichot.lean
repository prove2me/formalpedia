-- Prove2me | Definitions.Def_QMCLeafB_dichot
-- name    : QMCLeafB_dichot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:01:33.009572+00:00
-- url     : https://prove2.me/theorems/13a66d92-1be2-4704-a38e-d017a5266fa1
-- title:
--   QMCLeafB dichot
-- statement:
--   # `Check_dichot_m3` — phase 25, member m3, direction `ball-stratum-dichotomy`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_thrice
/-
# `Check_dichot_m3` — phase 25, member m3, direction `ball-stratum-dichotomy`

**What this file decides.**  The phase-24 thrice-split residual `ThriceM3.TripleSupply` asks, at each
interior point with a nonempty relaxed body, for
(2) `CoreDataG` if the program's bit reads `true`, and (3) `FinalStroke.RunParts` if it reads
`false`.  At the sliver exemplar `(G₁, t₁)` — two vertices, one edge of weight `1`, `t₁ = −2 + 71/1520000`,
`Rq = 2`, `ε = 1/20000`, `dq = 1/380000` — the body is **nonempty** (`AnchorFactsM2.realBody_G₁`), and:

* bit `true` ⟹ `CoreDataG` at `(G₁,t₁)`, which is uninhabited **for every bit**
  (`AnchorFactsM2.not_coreDataG_G₁`);
* bit `false` ⟹ `RunParts` at `(G₁,t₁)`, which forces the bit `true` — the body carries the
  campaign's ball (`BallM2.sliver_bit_true`).

So `TripleSupply o paramsKbc2` is **uninhabited for every bit `o`** (§1, `not_tripleSupply`): the
thrice-split is the fourth recurrence of the vacuity defect (phase 20 `SolutionFinite`, phase 21
`ResidFinite`/`ResidG`, phase 22 `ResidSplit`, now phase 24/25 `TripleSupply`).  Note what the kill
does *not* use: no hypothesis on the program's read-out data at all.

**The surviving residual, and the exact read-out obstruction.**  `PartsM2.ResidParts` keeps only the
`RunParts` half, so the ball argument no longer bites.  But the campaign's own read-out data does:
with the run's centres pinned to the **lower band edge** `1 − dq/4` (`hdia`), no such centre is a
member (`EmptyBodyM5.no_pinched_member_G₁`), so `ok ≡ false` below the horizon and the bit reads
`false` at `(G₁,t₁)` (`ThriceM3.bit_false_at_exemplar`); the ball then forces `true`.  Hence
`ResidParts` is **uninhabited given the campaign data** (§2, `not_residParts_of_data`), and the
concrete run's centres *are* pinned (`RecordsM2.cXst` has diagonal `1 − dq/4` by construction, §6c
`cXst_hdia`).  So `PartsM2.hdProp_of_campaign_parts` closes nothing once its `hok` is instantiated at
the run's own centres, and `ThriceM3.solution_of_triple` — whose hypothesis list contains
`hbit`/`hok`/`hdia` **and** `TripleSupply` — is doubly vacuous.  The escape is explicit: the `hdia`
slot is what must change (a centre at diagonal `≥ 1 − dq/8` admits a member, `ok_centre_diag_ge`);
with `hdia` dropped, the stroke's logic is untouched and `ResidParts` becomes the right residual.

**What production stands there (the design answer).**  The obstruction is the *pinch*, not the
level: at `(G₁,t₁)` a matrix with diagonal `d` is a member **iff** `1 − dq/8 ≤ d ∧ |d − 1| ≤ dq/4`
(§3, `member_iff_diag`, both directions).  The pinched centre `1 − dq/4` misses the threshold by
exactly `dq/8`; a centre at diagonal `1` (or anywhere in `[1 − dq/8, 1 + dq/4]`) admits a member
(`member_at_threshold`, `member_diag_one`).  So the third stratum's production is an `ok` round at an
**un-pinched** centre, certified on the objective side by the genuine witness `!![1,-1;-1,1]`
(`BallM2.sliver_hcert_witness`) — the bit then reads `true` there, `RunParts` is consistent, and
`ResidParts` is dischargeable.

§4 records the geometric form of the same fact at an arbitrary point: with the pinched read-out, a
`¬ PinchFeasible` nonempty interior point can carry **no ball at all** (`no_ball_at_not_pinchFeasible`)
— the third stratum is ball-free, which is exactly why the volume obstruction cannot produce it.

§6 answers question (a) of the brief.  At a single-edge `2 × 2` input the region of levels with
`body nonempty ∧ ¬ PinchFeasible` is **exactly** `u ∈ [−(1 + 5δ/4), −(1 + 3δ/4))`, width `δ/2 > 0`,
for every tolerance `δ > 0` (`third_stratum_band`, `body_empty_below`, `no_pinched_of_band`): the
pinch costs `δ/2` of objective range, permanently.  Slack tuning cannot remove it either — all `ε`
does is shift the band (`t = u + ε`), and the band leaves the leaf's bracket only when `ε ≤ 3δ/4`
(`band_below_bracket`), whereas the campaign has `δ = ε/10`.  At `G₀` the band is inhabited at the
campaign's own numbers (`nonempty_not_pinchFeasible_G₀`).  So **the third stratum is not empty by
design**; and since `sliver_runParts` inhabits `RunParts` there with the `true` bit, the production
that stands at it is an `ok` round at an **un-pinched** centre certified by a genuine witness.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom receipts at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.DichotM3

open QuantumMaxCutEnergy

/-! ## 0.  The exemplar and its numeric facts -/

/-- The sliver input (`= Check_emptybody_m5.G₁`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.AnchorFactsM2.G₁

/-- The sliver threshold (`= Check_anchorfacts_m2.t₁`). -/
abbrev t₁ : ℚ := QMCLeafB.AnchorFactsM2.t₁

/-- The empty-body input (`= Check_emptybody_m5.G₀`). -/
abbrev G₀ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₀

/-- The campaign parameter family at `G₀`. -/
abbrev P₀ : QMCLeafB.FinalStroke.RunParams G₀ := QMCLeafB.UnionShallow.paramsKbc2 G₀

/-- The campaign parameter family at `G₁`. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.UnionShallow.paramsKbc2 G₁

theorem hn₁ : 2 ≤ G₁.n := QMCLeafB.AnchorFactsM2.hn₁

theorem sliver_interior :
    -QMCLeafB.EngineRuntime.Rq G₁ ≤ t₁ ∧
      (t₁ : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) :=
  QMCLeafB.EmptyBodyM5.t₁_mem_bracket

theorem dq₁ : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq

theorem eps₁ : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁

/-- **The sliver body is nonempty** (`ThriceM3.BodyEmpty` form). -/
theorem sliver_not_bodyEmpty : ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ t₁ P₁ := by
  intro h
  obtain ⟨X, hX⟩ := QMCLeafB.AnchorFactsM2.realBody_G₁
  exact h X hX

/-! ## 1.  The thrice-split is vacuous: `TripleSupply` is uninhabited at every bit

The dichotomy, in one line: at `(G₁,t₁)` a `true` bit owes `CoreDataG` (dead by the crater), a
`false` bit owes `RunParts` (which forces the bit `true` by the volume obstruction). -/

/-- **`TripleSupply` is uninhabited, for every verdict bit.** -/
theorem not_tripleSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have hint := sliver_interior
  cases hb : o G₁ t₁ with
  | true =>
      exact QMCLeafB.AnchorFactsM2.not_coreDataG_G₁ o
        ⟨H.trueBit G₁ t₁ hn₁ hint.1 hint.2 hb⟩
  | false =>
      have B := H.third G₁ t₁ hn₁ hint.1 hint.2 sliver_not_bodyEmpty hb
      have htrue := QMCLeafB.BallM2.sliver_bit_true B
      rw [hb] at htrue
      exact Bool.noConfusion htrue

#print axioms QMCLeafB.DichotM3.not_tripleSupply

/-- **At the campaign bit**: the phase-24 residual itself is uninhabited. -/
theorem not_tripleSupply_campaign :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :=
  not_tripleSupply _

#print axioms QMCLeafB.DichotM3.not_tripleSupply_campaign

/-! ## 2.  The surviving residual dies too, given the campaign's pinched read-out

`ResidParts` demands `RunParts` at the sliver; the ball makes the bit `true`.  The campaign's own
data — a stream whose `ok` flag reads out as the bit, whose `ok` rounds are members at centres pinned
to `1 − dq/4` — makes it `false`.  The two are incompatible, so the phase-23 stroke's hypothesis list
is unsatisfiable. -/

/-- **`ResidParts` is uninhabited given the campaign's read-out data.** -/
theorem not_residParts_of_data
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) :
    ¬ Nonempty (QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have hint := sliver_interior
  have hbody : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
        ((t₁ : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
        (((P₁.dq : ℚ) : ℝ)) X :=
    QMCLeafB.AnchorFactsM2.realBody_G₁
  have B := H G₁ t₁ hn₁ hint.1 hint.2 hbody
  have htrue := QMCLeafB.BallM2.sliver_bit_true B
  have hfalse := QMCLeafB.ThriceM3.bit_false_at_exemplar (o := QMCLeafB.Audit2M5.campaignBit)
    (rb := rb G₁ t₁) (cX := cXp G₁ t₁) (hbit G₁ t₁) (hok G₁ t₁) (hdia G₁ t₁)
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

#print axioms QMCLeafB.DichotM3.not_residParts_of_data

/-! ## 3.  The exact diagonal threshold at the sliver: the pinch misses by `dq/8`

At `(G₁,t₁)` the objective is `⟪A,Q⟫ = Q₀₁ + Q₁₀` (`wMatrix G₁` is the one-edge matrix).  For a
symmetric candidate with diagonal `d` the two `RelaxMem` inequalities that involve the off-diagonal
are the `psd_margin` at `x = (1,1)` and `trace_le`, and they meet iff `d ≥ 1 − dq/8`.  The pinched
centre `1 − dq/4` — the campaign's frozen one — is `dq/8` below that: **that** is the whole
obstruction, and it is a property of the pinch, not of the engine's level. -/

/-- The off-diagonal of the candidate: `−(1 + 3·dq/8) = −(1 + 3/3040000)`. -/
def sCand : ℚ := -(1 + 3 / 3040000)

theorem two_mul_sCand : 2 * sCand = -(2 + 3 / 1520000) := by
  unfold sCand; ring

/-- The level identity at the sliver: `t₁ − ε + dq/2 = −(2 + 3·dq/4)`. -/
theorem sliver_level : t₁ - QMCLeafB.RundataCert.eps G₁ + P₁.dq / 2 = -(2 + 3 / 1520000) := by
  rw [eps₁, dq₁]; unfold t₁ QMCLeafB.AnchorFactsM2.t₁; norm_num

/-- **The 2×2 quadratic-form bound**: at diagonal `d` and off-diagonal `s`, `psd_margin` holds as
soon as `|s| ≤ d + δ/2`. -/
theorem qf_two_diag {d s δ : ℚ} (h : |s| ≤ d + δ / 2) (x : Fin 2 → ℚ) :
    -(δ / 2) * (∑ i, x i ^ 2) ≤
      QMCLeafB.SepOracle.qf (!![d, s; s, d]) x := by
  have hx : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
  have hq : QMCLeafB.SepOracle.qf (!![d, s; s, d]) x
      = d * (x 0 ^ 2 + x 1 ^ 2) + 2 * s * (x 0 * x 1) := by
    rw [QMCLeafB.SepOracle.qf_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp
    ring
  have hs1 : -s ≤ d + δ / 2 := by have := (abs_le.mp h).1; linarith
  have hs2 : s ≤ d + δ / 2 := (abs_le.mp h).2
  have key : 0 ≤ (d + δ / 2 + s) * (x 0 + x 1) ^ 2 + (d + δ / 2 - s) * (x 0 - x 1) ^ 2 := by
    have h1 : 0 ≤ d + δ / 2 + s := by linarith
    have h2 : 0 ≤ d + δ / 2 - s := by linarith
    have := mul_nonneg h1 (sq_nonneg (x 0 + x 1))
    have := mul_nonneg h2 (sq_nonneg (x 0 - x 1))
    linarith
  rw [hx, hq]
  nlinarith [key]

/-- The candidate matrix at diagonal `d`. -/
def cand (d : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![d, sCand; sCand, d]

theorem cand_diag (d : ℚ) : ∀ i, cand d i i = d := by
  intro i; fin_cases i <;> rfl

/-- **Sufficiency**: every diagonal in `[1 − dq/8, 1 + dq/4]` carries a member. -/
theorem member_of_diag {d : ℚ} (hlo : 1 - P₁.dq / 8 ≤ d) (hhi : |d - 1| ≤ P₁.dq / 4) :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
        (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq ∧ ∀ i, Q i i = d := by
  have hdq : (0 : ℚ) < P₁.dq := P₁.hdq
  have hdqeq : P₁.dq = 1 / 380000 := dq₁
  have habs : |sCand| ≤ d + P₁.dq / 2 := by
    have h1 : sCand ≤ 0 := by unfold sCand; norm_num
    rw [abs_of_nonpos h1, hdqeq]
    have hlo' := hlo
    rw [hdqeq] at hlo'
    unfold sCand
    norm_num at hlo' ⊢
    linarith
  refine ⟨cand d, ?_, cand_diag d⟩
  refine ⟨hdq, ?_, ?_, ?_⟩
  · intro x
    exact qf_two_diag (δ := P₁.dq) habs x
  · intro i
    rw [cand_diag d i]; exact hhi
  · -- `trace_le`: the objective is `2·sCand`, exactly at the level
    have hW : (∑ i : Fin 2, ∑ j : Fin 2,
        QMCLeafB.Finalization.wMatrixQ G₁ i j * cand d i j) = 2 * sCand := by
      simp only [Fin.sum_univ_two]
      simp [QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01,
        QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11, cand]
      ring
    simp only [QMCLeafB.SepOracle.frob]
    rw [hW, two_mul_sCand, sliver_level]

/-- **Necessity**: any member with diagonal `d` forces `d ≥ 1 − dq/8` and `|d − 1| ≤ dq/4`. -/
theorem diag_of_member {d : ℚ} {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hdiag : ∀ i, Q i i = d)
    (hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
      (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq) :
    1 - P₁.dq / 8 ≤ d ∧ |d - 1| ≤ P₁.dq / 4 := by
  have hd0 : |d - 1| ≤ P₁.dq / 4 := by
    have := hM.diag_near 0
    rwa [hdiag 0] at this
  refine ⟨?_, hd0⟩
  have hpsd := hM.psd_margin (fun _ : Fin 2 => (1 : ℚ))
  have hsum : (∑ i : Fin 2, ((1 : ℚ)) ^ 2) = 2 := by norm_num
  have hq : QMCLeafB.SepOracle.qf Q (fun _ : Fin 2 => (1 : ℚ))
      = Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
    rw [QMCLeafB.SepOracle.qf_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp
    ring
  rw [hsum, hq, hdiag 0, hdiag 1] at hpsd
  have hfrob : QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁) Q
      = Q 0 1 + Q 1 0 := by
    rw [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01,
      QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11]
  have hle := hM.trace_le
  rw [hfrob, sliver_level] at hle
  have hdq : (0 : ℚ) < P₁.dq := P₁.hdq
  have : P₁.dq = 1 / 380000 := dq₁
  nlinarith

/-- **THE THRESHOLD**: at `(G₁,t₁)` a diagonal-`d` matrix is a member **iff**
`1 − dq/8 ≤ d ∧ |d − 1| ≤ dq/4`. -/
theorem member_iff_diag (d : ℚ) :
    (∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
          (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq ∧ ∀ i, Q i i = d)
      ↔ (1 - P₁.dq / 8 ≤ d ∧ |d - 1| ≤ P₁.dq / 4) := by
  constructor
  · rintro ⟨Q, hM, hd⟩
    exact diag_of_member hd hM
  · rintro ⟨h1, h2⟩
    exact member_of_diag h1 h2

#print axioms QMCLeafB.DichotM3.member_iff_diag

/-- **The pinch misses the threshold by exactly `dq/8`.** -/
theorem pinch_gap : 1 - P₁.dq / 8 - (1 - P₁.dq / 4) = P₁.dq / 8 := by ring

/-- **The production that stands at the third stratum**: a centre at diagonal `1` (the un-pinched
`Q₁` of `Check_emptybody_m5`) is a member, although no centre at `1 − dq/4` is. -/
theorem member_diag_one :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
        (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq ∧ ∀ i, Q i i = 1 := by
  refine member_of_diag ?_ ?_
  · have hdq : (0 : ℚ) < P₁.dq := P₁.hdq
    linarith
  · rw [show (1 : ℚ) - 1 = 0 by ring, abs_zero]
    have hdq : (0 : ℚ) < P₁.dq := P₁.hdq
    linarith

#print axioms QMCLeafB.DichotM3.member_of_diag
#print axioms QMCLeafB.DichotM3.diag_of_member
#print axioms QMCLeafB.DichotM3.member_diag_one
#print axioms QMCLeafB.DichotM3.pinch_gap

/-! ## 4.  The third stratum is ball-free

The geometric form of the same fact at an *arbitrary* point: with the campaign's pinched read-out, a
`¬ PinchFeasible` interior point cannot carry a `RunParts` at a ball-bearing body — the ball forces
the bit `true`, the pinch forces it `false`.  So the third stratum, wherever it is real, lives in
bodies too thin to carry the campaign's ball; the volume obstruction can neither produce nor forbid a
run there. -/

/-- **No ball at a `¬ PinchFeasible` interior point** (whenever the read-out is the campaign's). -/
theorem no_ball_at_not_pinchFeasible
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (k : ℕ) (i : Fin G.n),
      cX k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (h : ¬ QMCLeafB.ThriceM3.PinchFeasible G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (B : QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} :
    ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).dq
          / (8 * ((QMCLeafB.UnionShallow.paramsKbc2 G).cAq + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (QMCLeafB.UnionShallow.paramsKbc2 G)) := by
  intro hball
  have htrue := QMCLeafB.BallM2.no_runParts_of_ball hn hball B
  have hfalse := QMCLeafB.ThriceM3.bit_false_of_not_pinchFeasible hbit hok hdia h
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

#print axioms QMCLeafB.DichotM3.no_ball_at_not_pinchFeasible

/-- **At the sliver**: `¬ PinchFeasible` and the ball are incompatible with any run + read-out.  (In
`hdia`-free form this is `not_residParts_of_data`; here the ball is exhibited.) -/
theorem sliver_no_runParts_of_pinched_readout
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : o G₁ t₁ = QMCLeafB.SimLoop.anyOk rb (P₁.K * P₁.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) (cX k)
        (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2), cX k i i = 1 - P₁.dq / 4) :
    ¬ Nonempty (QMCLeafB.FinalStroke.RunParts o G₁ t₁ P₁) := by
  rintro ⟨B⟩
  exact no_ball_at_not_pinchFeasible hn₁ sliver_interior.1 sliver_interior.2 rb cX hbit hok hdia
    QMCLeafB.ThriceM3.not_pinchFeasible_G₁ B QMCLeafB.BallM2.sliver_ball_campaign

#print axioms QMCLeafB.DichotM3.sliver_no_runParts_of_pinched_readout

/-! ## 5.  The production that stands at the third stratum: an `ok` round with the true bit

`RunParts` at `(G₁, t₁)` is **inhabited** — with `ok ≡ true` and the genuine witness
`!![1,-1;-1,1]` (`BallM2.sliver_hcert_witness`) as the `ok` certificate.  No drift slot, no cut
witness, nothing owed: every cut-conditioned field is vacuous.  So the sliver is not an obstruction
to the run interface at all; what the pinch destroys is only the *`false`-bit* read-out. -/


/-- `anyOk` of the constant-`true` stream at a positive horizon. -/
theorem anyOk_true_of_pos : ∀ T : ℕ, 0 < T →
    QMCLeafB.SimLoop.anyOk (fun _ => true) T = true
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | (k + 1), _ => by
      rw [QMCLeafB.SimLoop.anyOk_succ]
      simp

/-- A `RunParts` at the sliver, with the bit `true`. -/
def sliver_runParts : QMCLeafB.FinalStroke.RunParts (fun _ _ => true) G₁ t₁ P₁ where
  ok := fun _ => true
  cd := fun _ => ⟨0, 0, 0⟩
  del := fun _ => 0
  hcert := fun _ _ _ => QMCLeafB.BallM2.sliver_hcert_witness
  hwit := fun _ _ h => Bool.noConfusion h
  hrho := fun _ _ h => Bool.noConfusion h
  hcne := fun _ _ h => Bool.noConfusion h
  hdel0 := fun _ _ h => Bool.noConfusion h
  hcheck := fun _ _ h => Bool.noConfusion h
  hle := fun _ _ h => Bool.noConfusion h
  hcut := fun _ _ h => Bool.noConfusion h
  hverdict := by
    have hpos : 0 < P₁.K * P₁.m := Nat.lt_trans (by norm_num) QMCLeafB.AnchorFactsM2.Km₁
    exact (anyOk_true_of_pos _ hpos).symm

#print axioms QMCLeafB.DichotM3.sliver_runParts

theorem sliver_runParts_bit : (fun _ _ => true : QuantumMaxCutEnergy.Input → ℚ → Bool) G₁ t₁
    = true := rfl

/-- **The repaired read-out is consistent at the sliver**: an `ok` stream, a centre family at
diagonal `1` (un-pinched), the member certificate, the verdict equation and the run all coexist.  So
the design repair named by §2–§3 (test at an un-pinched centre, certify on the objective side) is not
merely necessary — it is sufficient at the exemplar. -/
theorem repaired_readout_consistent :
    ∃ (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ),
      (∀ k, rb k = true →
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) (cX k)
          (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq) ∧
      (∀ k, cX k 0 0 = 1 ∧ cX k 1 1 = 1) ∧
      ((fun _ _ => true : QuantumMaxCutEnergy.Input → ℚ → Bool) G₁ t₁
        = QMCLeafB.SimLoop.anyOk rb (P₁.K * P₁.m)) ∧
      (QMCLeafB.SimLoop.anyOk rb (P₁.K * P₁.m) = true) := by
  obtain ⟨Q, hQ, hdiag⟩ := member_diag_one
  have hpos : 0 < P₁.K * P₁.m := Nat.lt_trans (by norm_num) QMCLeafB.AnchorFactsM2.Km₁
  refine ⟨fun _ => true, fun _ => Q, ?_, ?_, ?_, ?_⟩
  · intro k _
    exact hQ
  · intro k; exact ⟨hdiag 0, hdiag 1⟩
  · exact (anyOk_true_of_pos _ hpos).symm
  · exact anyOk_true_of_pos _ hpos

#print axioms QMCLeafB.DichotM3.repaired_readout_consistent

/-! ## 6.  "Empty by design" is impossible: at a single-edge `2 × 2` input the band
`nonempty ∧ ¬ PinchFeasible` is nonempty for EVERY tolerance `δ > 0`

This is the answer to question (a) of the phase-25 brief.  The relaxed body allows the diagonal to
sit anywhere in `[1 − δ/4, 1 + δ/4]` and the PSD margin to be `δ/2`; so an *un-pinned* centre can
reach objective `1 + 3δ/4` below zero, while a centre **pinned to `1 − δ/4`** reaches only `1 + δ/4`
and must stay above the level `u + δ/2` (`EmptyBodyM5.frob_ge_of_pinched`).  The pinch therefore
costs `δ/2` of objective range, and the body's nonemptiness threshold is lower than the
pinched-member threshold by a margin that no choice of `δ` closes: the band of levels with
`nonempty ∧ ¬ PinchFeasible` is exactly `u ∈ [−(1 + 5δ/4), −(1 + 3δ/4))`, of width `δ/2 > 0`.

What the leaf can *tune* is not `δ` but `ε`, and all `ε` does is shift the band: `t = u + ε`.  The
band leaves the leaf's bracket `[−Rq, 0)` (at the single-edge input, `Rq = 1`) only if
`−(1 + 3δ/4) + ε ≤ −1`, i.e. `ε ≤ 3δ/4` (§6d, `band_below_bracket`).  The campaign has the opposite
inequality by a factor of `13⅓`: `δ = ε/(9·Rq + 1) = ε/10`.  So killing the stratum would need
`δ ≥ 4ε/3` — a tolerance the ok-round rounding budget (`dq ≈ ε/(9·cAq+1)`) forbids.  **The third
stratum is not empty by design, and cannot be made so by slack tuning.** -/


/-- The single-edge weight matrix `!![0, 1/2; 1/2, 0]` (`= wMatrixQ G₀`). -/
def Ase : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1 / 2; 1 / 2, 0]

/-- The un-pinned body witness: unit diagonal, off-diagonal `−(1 + 3δ/8)` (lower eigenvalue
`−3δ/8`, inside the `δ/2` margin; objective `−(1 + 3δ/8)`). -/
def Xse (δ : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, -(1 + 3 * δ / 8); -(1 + 3 * δ / 8), 1]

theorem Ase_00 : Ase 0 0 = 0 := rfl
theorem Ase_01 : Ase 0 1 = 1 / 2 := rfl
theorem Ase_10 : Ase 1 0 = 1 / 2 := rfl
theorem Ase_11 : Ase 1 1 = 0 := rfl

/-- **A body point at a prescribed diagonal and off-diagonal**: the three `relaxBodyLE` slots reduce
to `|d − 1| ≤ δ/4`, `|s| ≤ d + δ/2` and `s ≤ u + δ/2`. -/
theorem body_of_level {δ u d s : ℚ} (hδ : 0 < δ)
    (hdiag : |d - 1| ≤ δ / 4) (habs : |s| ≤ d + δ / 2) (hlev : s ≤ u + δ / 2) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat Ase) (u : ℝ) (δ : ℝ)
      (QMCLeafB.SepOracle.castMat (!![d, s; s, d])) := by
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hq : QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat (!![d, s; s, d])) x
        = (d : ℝ) * (x 0 ^ 2 + x 1 ^ 2) + 2 * (s : ℝ) * (x 0 * x 1) := by
      rw [QMCLeafB.BallFloor.qfR_eq_sum]
      simp only [Fin.sum_univ_two, QMCLeafB.SepOracle.castMat_apply]
      simp
      ring
    rw [hq]
    have hx : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    rw [hx]
    have habs' : |(s : ℝ)| ≤ (d : ℝ) + (δ : ℝ) / 2 := by
      have h := habs
      exact_mod_cast h
    have key : 0 ≤ ((d : ℝ) + (δ : ℝ) / 2 + (s : ℝ)) * (x 0 + x 1) ^ 2
        + ((d : ℝ) + (δ : ℝ) / 2 - (s : ℝ)) * (x 0 - x 1) ^ 2 := by
      have h1 : 0 ≤ (d : ℝ) + (δ : ℝ) / 2 + (s : ℝ) := by
        have := (abs_le.mp habs').1; linarith
      have h2 : 0 ≤ (d : ℝ) + (δ : ℝ) / 2 - (s : ℝ) := by
        have := (abs_le.mp habs').2; linarith
      have h3 := mul_nonneg h1 (sq_nonneg (x 0 + x 1))
      have h4 := mul_nonneg h2 (sq_nonneg (x 0 - x 1))
      linarith
    nlinarith [key]
  · intro i
    have he : QMCLeafB.SepOracle.castMat (!![d, s; s, d]) i i = (d : ℝ) := by
      rw [QMCLeafB.SepOracle.castMat_apply]
      fin_cases i <;> simp
    rw [he]
    have h := hdiag
    have h' : |(d : ℝ) - 1| ≤ (δ : ℝ) / 4 := by exact_mod_cast h
    linarith [abs_nonneg ((d : ℝ) - 1)]
  · have hf : QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat Ase)
        (QMCLeafB.SepOracle.castMat (!![d, s; s, d])) = (s : ℝ) := by
      rw [QMCLeafB.BallFloor.frob]
      simp only [Fin.sum_univ_two, QMCLeafB.SepOracle.castMat_apply]
      simp [Ase]
      ring
    rw [hf]
    have hlev' : (s : ℝ) ≤ (u : ℝ) + (δ : ℝ) / 2 := by exact_mod_cast hlev
    linarith

/-- **The body is nonempty at the top of the band** (`u ≥ −(1 + 7δ/8)`): the unit-diagonal point with
off-diagonal `−(1 + 3δ/8)`. -/
theorem body_of_band {δ u : ℚ} (hδ : 0 < δ) (h1 : -(1 + 7 * δ / 8) ≤ u) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat Ase) (u : ℝ) (δ : ℝ)
      (QMCLeafB.SepOracle.castMat (Xse δ)) := by
  have h1' : -(1 + 3 * δ / 8) ≤ u + δ / 2 := by linarith
  have h2' : |-(1 + 3 * δ / 8)| ≤ 1 + δ / 2 := by
    rw [abs_of_nonpos (by linarith : -(1 + 3 * δ / 8) ≤ 0)]
    linarith
  have h3' : |(1 : ℚ) - 1| ≤ δ / 4 := by
    rw [show (1 : ℚ) - 1 = 0 by ring, abs_zero]; linarith
  have := body_of_level (δ := δ) (u := u) (d := 1) (s := -(1 + 3 * δ / 8)) hδ h3' h2' h1'
  simpa [Xse] using this

/-- **The objective floor of the real body**: every body point has `frob ≥ −(1 + 3δ/4)` — the
diagonal's upper edge `1 + δ/4` together with the PSD margin at `(1,1)`.  Consequently the body is
empty below the level `−(1 + 5δ/4)`. -/
theorem frob_floor_real {δ u : ℚ} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat Ase) (u : ℝ) (δ : ℝ) X) :
    -(1 + 3 * (δ : ℝ) / 4) ≤ QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat Ase) X := by
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  have hq := hpsd (fun _ : Fin 2 => (1 : ℝ))
  have hs : (∑ i : Fin 2, ((1 : ℝ)) ^ 2) = 2 := by norm_num
  rw [hs] at hq
  have h00 : X 0 0 ≤ 1 + (δ : ℝ) / 4 := by
    have := (abs_le.mp (hdiag 0)).2; linarith
  have h11 : X 1 1 ≤ 1 + (δ : ℝ) / 4 := by
    have := (abs_le.mp (hdiag 1)).2; linarith
  have hqf : QMCLeafB.BallFloor.qfR X (fun _ : Fin 2 => (1 : ℝ))
      = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    rw [QMCLeafB.BallFloor.qfR_eq_sum]
    simp [Fin.sum_univ_two]
    ring
  rw [hqf] at hq
  have hf : QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat Ase) X
      = (X 0 1 + X 1 0) / 2 := by
    rw [QMCLeafB.BallFloor.frob]
    simp only [Fin.sum_univ_two, QMCLeafB.SepOracle.castMat_apply]
    simp [Ase]
    ring
  rw [hf]
  linarith

/-- **The body is nonempty at the exact bottom of the band** (`u ≥ −(1 + 5δ/4)`): the diagonal-edge
point with `d = 1 + δ/4` and off-diagonal `−(1 + 3δ/4)` (lower eigenvalue exactly `−δ/2`). -/
theorem body_at_exact_level {δ u : ℚ} (hδ : 0 < δ) (h1 : -(1 + 5 * δ / 4) ≤ u) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat Ase) (u : ℝ) (δ : ℝ)
      (QMCLeafB.SepOracle.castMat (!![1 + δ / 4, -(1 + 3 * δ / 4);
        -(1 + 3 * δ / 4), 1 + δ / 4])) := by
  have h1' : -(1 + 3 * δ / 4) ≤ u + δ / 2 := by linarith
  have h2' : |-(1 + 3 * δ / 4)| ≤ (1 + δ / 4) + δ / 2 := by
    rw [abs_of_nonpos (by linarith : -(1 + 3 * δ / 4) ≤ 0)]
    linarith
  have h3' : |(1 + δ / 4) - 1| ≤ δ / 4 := by
    rw [show (1 : ℚ) + δ / 4 - 1 = δ / 4 by ring,
      abs_of_pos (by linarith : (0 : ℚ) < δ / 4)]
  exact body_of_level (δ := δ) (u := u) (d := 1 + δ / 4) (s := -(1 + 3 * δ / 4))
    hδ h3' h2' h1'

/-- **No pinched member at the bottom of the band** (`u < −(1 + 3δ/4)`). -/
theorem no_pinched_of_band {δ u : ℚ} (hδ : 0 < δ) (h2 : u < -(1 + 3 * δ / 4)) :
    ∀ Q : Matrix (Fin 2) (Fin 2) ℚ, (∀ i, Q i i = 1 - δ / 4) →
      ¬ QMCLeafB.RelaxOracle.RelaxMem Ase Q u δ := by
  intro Q hdiag hM
  have hge := QMCLeafB.EmptyBodyM5.frob_ge_of_pinched (c := 1 / 2) (δ := δ) (u := u)
    (by norm_num) Ase_00 Ase_01 Ase_10 Ase_11 hdiag hM
  have hle := hM.trace_le
  linarith

/-- **The nonemptiness floor**: below `u = −(1 + 5δ/4)` the body is empty. -/
theorem body_empty_below {δ u : ℚ} (hδ : 0 < δ) (h : u < -(1 + 5 * δ / 4)) :
    ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat Ase) (u : ℝ) (δ : ℝ) X := by
  intro X hX
  have hfloor := frob_floor_real hX
  have htr := hX.2.2
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hc : ((-(1 + 5 * δ / 4) : ℚ) : ℝ) = -(1 + 5 * ((δ : ℝ) / 4)) := by push_cast; ring
  have hlt : (u : ℝ) < -(1 + 5 * ((δ : ℝ) / 4)) := by
    have h2 : ((u : ℚ) : ℝ) < ((-(1 + 5 * δ / 4) : ℚ) : ℝ) := by exact_mod_cast h
    rwa [hc] at h2
  linarith

/-- **The band is nonempty for every `δ > 0`.** -/
theorem band_arith (δ : ℚ) (hδ : 0 < δ) : -(1 + 5 * δ / 4) < -(1 + 3 * δ / 4) := by linarith

/-- **The structural refutation of "empty by design"**: for every `δ > 0` and every level `u` in the
band `[−(1 + 5δ/4), −(1 + 3δ/4))` — an interval of width `δ/2` — the body is nonempty while no
pinched matrix is a member.  The upper edge is exact (`no_pinched_of_band`) and the lower edge is
exact (`body_empty_below`), so this is the complete `nonempty ∧ ¬ PinchFeasible` region at a
single-edge input. -/
theorem third_stratum_band {δ u : ℚ} (hδ : 0 < δ)
    (h1 : -(1 + 5 * δ / 4) ≤ u) (h2 : u < -(1 + 3 * δ / 4)) :
    (∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat Ase) (u : ℝ) (δ : ℝ) X) ∧
      (∀ Q : Matrix (Fin 2) (Fin 2) ℚ, (∀ i, Q i i = 1 - δ / 4) →
        ¬ QMCLeafB.RelaxOracle.RelaxMem Ase Q u δ) :=
  ⟨⟨_, body_at_exact_level hδ h1⟩, no_pinched_of_band hδ h2⟩

#print axioms QMCLeafB.DichotM3.third_stratum_band

/-! ### 6b.  The band at the empty-body input `G₀`, at the campaign's own `(ε, dq)`

`G₀` is `2` vertices with one edge of weight `1/2` (`Rq = 1`, `ε = 1/40000`, `dq = 1/400000`); the
phase-21 refutation put `(G₀, −99999/100000)` in the *empty* stratum.  The band is the interval
`t ∈ [−1 + 1/40000 − 7/8·dq, −1 + 1/40000 − 3/4·dq)`, i.e. `t ∈ [−199985/200000 − 7dq/8, ...)`;
we take `t = −1 + 295/12800000` (so `u = t − ε = −1 − 25/12800000`, strictly inside). -/

/-- The band threshold at `G₀`: `u = −1 − 25/12800000`. -/
def tBand : ℚ := -1 + 295 / 12800000

theorem tBand_u : tBand - QMCLeafB.RundataCert.eps G₀ = -1 - 25 / 12800000 := by
  rw [QMCLeafB.EmptyBodyM5.eps_G₀]; unfold tBand; norm_num

/-- The level at `tBand` in `ℝ`, matching `BodyEmpty`'s own cast shape. -/
theorem tBand_level : ((tBand : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₀ / 40000 : ℚ)) : ℝ))
    = ((-1 - 25 / 12800000 : ℚ) : ℝ) := by
  have hRq : QMCLeafB.EngineRuntime.Rq G₀ = 1 := QMCLeafB.ResidRefute.Rq_G₀
  unfold tBand
  rw [hRq]
  norm_num

theorem tBand_interior :
    -QMCLeafB.EngineRuntime.Rq G₀ ≤ tBand ∧
      (tBand : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₀ / 40000 : ℚ)) : ℝ) := by
  constructor
  · rw [QMCLeafB.ResidRefute.Rq_G₀]; unfold tBand; norm_num
  · rw [QMCLeafB.ResidRefute.Rq_G₀]
    have : ((tBand : ℚ) : ℝ) = ((-1 + 295 / 12800000 : ℚ) : ℝ) := rfl
    rw [this]; norm_num

theorem wMatrix_G₀_00 : QMCLeafB.wMatrix G₀ (0 : Fin 2) (0 : Fin 2) = 0 :=
  QMCLeafB.wMatrix_apply_of_eq

theorem wMatrix_G₀_11 : QMCLeafB.wMatrix G₀ (1 : Fin 2) (1 : Fin 2) = 0 :=
  QMCLeafB.wMatrix_apply_of_eq

theorem wMatrix_G₀_01 :
    QMCLeafB.wMatrix G₀ (0 : Fin 2) (1 : Fin 2) = 1 / 2 := by
  rw [QMCLeafB.wMatrix_apply_of_lt (show (0 : Fin 2) < 1 by decide)]
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrix_G₀_10 :
    QMCLeafB.wMatrix G₀ (1 : Fin 2) (0 : Fin 2) = 1 / 2 := by
  rw [QMCLeafB.wMatrix_apply_of_gt (show (0 : Fin 2) < 1 by decide)]
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrix_G₀_eq : QMCLeafB.wMatrix G₀ =
    QMCLeafB.SepOracle.castMat Ase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QMCLeafB.SepOracle.castMat_apply, wMatrix_G₀_00, wMatrix_G₀_01, wMatrix_G₀_10,
      wMatrix_G₀_11, Ase]

theorem wMatrixQ_G₀_eq : QMCLeafB.Finalization.wMatrixQ G₀ = Ase := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ase, QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_01,
      QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_11]

/-- **The third stratum is inhabited at `G₀` too** — the input whose *lower* thresholds are the
empty stratum: interior, body nonempty, no pinched member, at the campaign's own `(ε, dq)`.  So the
`nonempty ∧ ¬ PinchFeasible` band is not a sliver artefact: it is the upper end of every input's
threshold interval.  (This point is NOT ball-free — at `G₀` the body is wide in the off-diagonal
directions; the band statement below is about `¬ PinchFeasible`, not about thinness.) -/
theorem nonempty_not_pinchFeasible_G₀ :
    -QMCLeafB.EngineRuntime.Rq G₀ ≤ tBand ∧
      (tBand : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₀ / 40000 : ℚ)) : ℝ) ∧
      ¬ QMCLeafB.ThriceM3.BodyEmpty G₀ tBand
          (QMCLeafB.UnionShallow.paramsKbc2 G₀) ∧
      ¬ QMCLeafB.ThriceM3.PinchFeasible G₀ tBand
          (QMCLeafB.UnionShallow.paramsKbc2 G₀) := by
  have hδ : (0 : ℚ) < (QMCLeafB.UnionShallow.paramsKbc2 G₀).dq :=
    (QMCLeafB.UnionShallow.paramsKbc2 G₀).hdq
  have hδeq : (QMCLeafB.UnionShallow.paramsKbc2 G₀).dq = 1 / 400000 :=
    QMCLeafB.EmptyBodyM5.dq₀_eq
  have hu : tBand - QMCLeafB.RundataCert.eps G₀
      = -1 - 25 / 12800000 := tBand_u
  have h1 : -(1 + 5 * (QMCLeafB.UnionShallow.paramsKbc2 G₀).dq / 4)
      ≤ -1 - 25 / 12800000 := by
    rw [hδeq]; norm_num
  have h2 : -1 - 25 / 12800000
      < -(1 + 3 * (QMCLeafB.UnionShallow.paramsKbc2 G₀).dq / 4) := by
    rw [hδeq]; norm_num
  obtain ⟨hbody, hpinch⟩ := third_stratum_band (δ := (QMCLeafB.UnionShallow.paramsKbc2
    G₀).dq)
    (u := -1 - 25 / 12800000) hδ h1 h2
  refine ⟨tBand_interior.1, tBand_interior.2, ?_, ?_⟩
  · intro hempty
    obtain ⟨X, hX⟩ := hbody
    refine hempty X ?_
    rw [wMatrix_G₀_eq, tBand_level]
    exact hX
  · rintro ⟨Q, hQ, hdiag⟩
    have hQ' : QMCLeafB.RelaxOracle.RelaxMem Ase Q
        (tBand - QMCLeafB.RundataCert.eps G₀)
        (QMCLeafB.UnionShallow.paramsKbc2 G₀).dq := by
      rw [wMatrixQ_G₀_eq] at hQ; exact hQ
    have hdiag' : ∀ i, Q i i = 1
        - (QMCLeafB.UnionShallow.paramsKbc2 G₀).dq / 4 := hdiag
    rw [hu] at hQ'
    exact hpinch Q hdiag' hQ'

#print axioms QMCLeafB.DichotM3.wMatrix_G₀_eq
#print axioms QMCLeafB.DichotM3.nonempty_not_pinchFeasible_G₀

/-! ### 6d.  The band meets the leaf's bracket unless `ε ≤ 3δ/4` -/

/-- **The band is below the bracket only if `ε ≤ 3δ/4`**: for a single-edge input (`Rq = 1`,
`δ = dq`, level `u = t − ε`), every level in the band has `t < −1` as soon as `ε ≤ 3δ/4`.  In other
words the `nonempty ∧ ¬ PinchFeasible` band is unreachable at a single-edge input only at tolerances
`δ ≥ 4ε/3`; the campaign's `δ = ε/10` is nowhere near it. -/
theorem band_below_bracket {δ u ε : ℚ} (hδ : 0 < δ)
    (h1 : -(1 + 5 * δ / 4) ≤ u) (h2 : u < -(1 + 3 * δ / 4)) (hε : ε ≤ 3 * δ / 4) :
    u + ε < -(1 : ℚ) := by
  linarith

#print axioms QMCLeafB.DichotM3.band_below_bracket

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.DichotM3.sliver_not_bodyEmpty
#print axioms QMCLeafB.DichotM3.not_tripleSupply
#print axioms QMCLeafB.DichotM3.not_tripleSupply_campaign
#print axioms QMCLeafB.DichotM3.not_residParts_of_data
#print axioms QMCLeafB.DichotM3.qf_two_diag
#print axioms QMCLeafB.DichotM3.member_of_diag
#print axioms QMCLeafB.DichotM3.diag_of_member
#print axioms QMCLeafB.DichotM3.member_iff_diag
#print axioms QMCLeafB.DichotM3.member_diag_one
#print axioms QMCLeafB.DichotM3.pinch_gap
#print axioms QMCLeafB.DichotM3.no_ball_at_not_pinchFeasible
#print axioms QMCLeafB.DichotM3.sliver_no_runParts_of_pinched_readout
#print axioms QMCLeafB.DichotM3.anyOk_true_of_pos
#print axioms QMCLeafB.DichotM3.sliver_runParts
#print axioms QMCLeafB.DichotM3.repaired_readout_consistent
#print axioms QMCLeafB.DichotM3.body_of_level
#print axioms QMCLeafB.DichotM3.body_of_band
#print axioms QMCLeafB.DichotM3.frob_floor_real
#print axioms QMCLeafB.DichotM3.body_at_exact_level
#print axioms QMCLeafB.DichotM3.body_empty_below
#print axioms QMCLeafB.DichotM3.no_pinched_of_band
#print axioms QMCLeafB.DichotM3.band_arith
#print axioms QMCLeafB.DichotM3.third_stratum_band
#print axioms QMCLeafB.DichotM3.tBand_level
#print axioms QMCLeafB.DichotM3.tBand_interior
#print axioms QMCLeafB.DichotM3.wMatrix_G₀_eq
#print axioms QMCLeafB.DichotM3.nonempty_not_pinchFeasible_G₀


/-! ## 6c.  The design condition the threshold imposes on the run, and its concreteness

`RelaxMem` at an `ok` round forces the centre's diagonal up; the campaign's frozen centres
(`RecordsM2.cXst`) sit at the *lower* edge `1 − dq/4`, so at the sliver they cannot be the centres of
an `ok` round.  That is the precise repair the phase-25 brief asks for, and it is a one-line
consequence of §3. -/

/-- **The design condition**: a member at the sliver whose diagonal is `d` forces `d ≥ 1 − dq/8`. -/
theorem ok_centre_diag_ge {Q : Matrix (Fin 2) (Fin 2) ℚ} {d : ℚ}
    (h00 : Q 0 0 = d) (h11 : Q 1 1 = d)
    (hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
      (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq) :
    1 - P₁.dq / 8 ≤ d :=
  (diag_of_member (fun i => by fin_cases i <;> assumption) hM).1

/-- The pinched edge is excluded: `1 − dq/4 < 1 − dq/8`. -/
theorem pinch_edge_excluded : ¬ (1 - P₁.dq / 8 ≤ 1 - P₁.dq / 4) := by
  have hdq : (0 : ℚ) < P₁.dq := P₁.hdq
  intro h; linarith

/-- **The campaign's own centres satisfy the pinched hypothesis `hdia` by definition** — so
`not_residParts_of_data` is not a hypothetical: it is the read-out the concrete run has. -/
theorem cXst_hdia (X : ℕ → List ℚ) (k : ℕ) (i : Fin G₁.n) :
    QMCLeafB.RecordsM2.cXst G₁.n X P₁.dq k i i = 1 - P₁.dq / 4 :=
  QMCLeafB.RecordsM2.cXst_diag G₁.n X P₁.dq k i

#print axioms QMCLeafB.DichotM3.ok_centre_diag_ge
#print axioms QMCLeafB.DichotM3.cXst_hdia

end QMCLeafB.DichotM3


