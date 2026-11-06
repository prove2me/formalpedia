-- Prove2me | Definitions.Def_QMCLeafB_thin32
-- name    : QMCLeafB_thin32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:56:46.363283+00:00
-- url     : https://prove2.me/theorems/7645fe34-1c93-447d-a54c-8a943689ec89
-- title:
--   QMCLeafB thin32
-- statement:
--   # `Check_thin32_m2` — phase 32, member m2, direction `thin-visit` (d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_htop_ledgerW_m7
import Definitions.Def_QMCLeafB_asm_m8
import Definitions.Def_QMCLeafB_pivexact
import Definitions.Def_QMCLeafB_bitdec
/-
# `Check_thin32_m2` — phase 32, member m2, direction `thin-visit` (d2)

## The question

`hcomplete` (the second of the two residual statements at the campaign program
`(RSt, InitDq.init0, LedgerW.roundWG, RoundProgram.verdict, Tbc2)`) reads

  `∀ G t, 2 ≤ G.n → Interior G t → ¬ EmptyBody G t P → bit G t = true`,

i.e. *a non-empty relaxed body forces the program's `ok` stream to fire below the horizon*.  At
ball-bearing bodies the volume machinery answers it (`BallM2.no_runParts_of_ball`,
`TrajM3.exists_member_of_ball`).  This file answers the thin/ball-free half — negatively and sharply.

## The finding: the exact-unit-diagonal gate is fatal, in a fat window, at the campaign's own exemplar

`OkLower.okW` reads (in the interior branch) `!(oracleV s).1`, and `oracleV`'s `ok` answer is gated
by `dvR s = 0` (`dvR = ∑ i |Xᵢᵢ − 1|`, m3's `diagSumV`): the program reports `ok` only at centres
whose diagonal is exactly `1`.  Two facts at the sliver input `G₁` (two vertices, one edge of weight
`1`; `Rq = 2`, `ε = 1/20000`, `d = dqShallow = 1/380000`):

* THE RIGIDITY.  At the level `u_W = −(2 + 7d/4) = −Rq − 7d/4` — i.e. at the interior threshold
  `t_W = u_W + ε` — the relaxed body is non-empty (`nonempty_W`), and it contains no unit-diagonal
  matrix at all (`no_unitDiag_of_level`): a unit diagonal together with the `d/2`-PSD margin forces
  `frob ≥ −2 − d` at the all-ones vector, while the level clause forces `frob ≤ u_W + d/2 = −2 − 5d/4`.
* THE BALL.  The same body carries the campaign's own ball: the Frobenius ball of radius
  `d/24 = 1/9120000 = P₁.dq/(8(c_A+1))` around `Xb` lies inside it (`Xb_ball`), so the volume
  obstruction applies there.

Consequently:

* `hcomplete` is FALSE for every sound program (`not_hcomplete_of_gated_sound`): if every `ok`
  round's centre is a member of the run's body — exactly what the grid enlargement
  (`stD ≥ 2n²/dqShallow`, `LdltCertM5.pivPsdMargin_of_tolerance`) buys for `hok` — then no round can
  be `ok` at `(G₁, t_W)`, so the bit reads `false` at a point with a non-empty body.
* Stronger, the record is unimplementable there (`no_runParts_of_gated_sound`): a `RunParts` at
  `(G₁, t_W)` whose `ok` centres are (i) members and (ii) unit-diagonal is contradictory — the ball
  forces the bit `true` (`BallM2.no_runParts_of_ball`) while the rigidity forces every `ok` below the
  horizon to be `false`.  So `Hpsd` (soundness at the `ok` states) and the leaf's `hd` slot are
  simultaneously unsatisfiable at `(G₁,t_W)` at the `dvR = 0` round.

## The minimal program change

Drop the exact gate: test the diagonal at the body's own tolerance, `dvR s ≤ dqOf s / 4` instead of
`= 0`.  Then (i) every member becomes acceptable — `RelaxMem`'s diagonal clause is
`|Xᵢᵢ − 1| ≤ d/4`, so the gate was strictly stronger than the body it tests; (ii) `hok` loses
nothing (its witness is taken at the ok centre, which stays a member); and (iii) `hcomplete` at the
window falls straight back into the volume lane — `Xb_ball` is `4/3` of the campaign radius, so
`BallM2.no_runParts_of_ball` forces a visited member below the horizon, i.e. an `ok` round.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom receipts at the end (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Thin32M2

open QuantumMaxCutEnergy

/-! ## 0.  The exemplar and the window point -/

/-- The sliver input (`= Check_anchorfacts_m2.G₁`): two vertices, one edge of weight `1`. -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.AnchorFactsM2.G₁

/-- The campaign parameter family at `G₁`. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.AnchorFactsM2.P₁

theorem hn₁ : 2 ≤ G₁.n := QMCLeafB.AnchorFactsM2.hn₁

theorem n₁ : G₁.n = 2 := QMCLeafB.AnchorFactsM2.n₁

theorem Rq₁ : QMCLeafB.EngineRuntime.Rq G₁ = 2 := QMCLeafB.EmptyBodyM5.Rq_G₁

theorem dq₁ : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq

theorem cAq₁ : P₁.cAq = 2 := by
  rw [show P₁ = QMCLeafB.UnionShallow.paramsKbc2 G₁ from rfl,
    QMCLeafB.BallM2.paramsKbc2_cAq, Rq₁]

/-- The window point: `t_W = −Rq + ε'` with `u_W = t_W − ε = −(2 + 7d/4)`. -/
abbrev tW : ℚ := -(2 : ℚ) + 69 / 1520000

/-- The run's level at the window point: `t_W − Rq/40000 = −(2 + 7d/4)`. -/
theorem level_W :
    ((tW : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
      = -(2 + 7 / 1520000) := by
  rw [Rq₁]
  unfold tW
  push_cast
  norm_num

/-- The window point is interior: `−Rq ≤ t_W < −ε`. -/
theorem interior_W : _root_.AsmM8.Interior G₁ tW := by
  refine ⟨?_, ?_⟩
  · rw [Rq₁]
    unfold tW
    norm_num
  · rw [Rq₁]
    unfold tW
    push_cast
    norm_num

/-! ## 1.  The rigidity: no unit-diagonal member at the window level

`frob (wMatrix G₁) X = X₀₁ + X₁₀` (one edge of weight `1`), and the quadratic form at the all-ones
vector is `X₀₀ + X₀₁ + X₁₀ + X₁₁`.  On a unit diagonal the PSD margin `d/2` therefore forces
`X₀₁ + X₁₀ ≥ −2 − d`, while the level clause at `u_W` forces `X₀₁ + X₁₀ ≤ −2 − 5d/4`. -/

theorem qfR_ones (X : Matrix (Fin 2) (Fin 2) ℝ) :
    QMCLeafB.BallFloor.qfR X (fun _ => (1 : ℝ)) = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
  rw [QMCLeafB.BallFloor.qfR_eq_sum]
  simp only [Fin.sum_univ_two]
  ring

theorem frob_sl (X : Matrix (Fin 2) (Fin 2) ℝ) :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) X = X 0 1 + X 1 0 := by
  rw [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
  ring

/-- THE RIGIDITY.  Every member of the relaxed body below the level `−Rq − 3d/2` has a non-unit
diagonal.  (In particular no `dvR = 0` state can be a member there: `dvR s = 0` says exactly that
every diagonal entry is `1`.) -/
theorem no_unitDiag_of_level {u : ℝ} (hu : u < -(2 + 3 / 760000))
    {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u ((1 / 380000 : ℚ) : ℝ) X) :
    ¬ (∀ i, X i i = 1) := by
  intro hd
  have hpsd := hX.1 (fun _ => (1 : ℝ))
  rw [qfR_ones] at hpsd
  have hsum : (∑ i : Fin 2, (fun _ : Fin 2 => (1 : ℝ)) i ^ 2) = 2 := by
    rw [Fin.sum_univ_two]; norm_num
  rw [hsum] at hpsd
  have h00 : X 0 0 = 1 := hd 0
  have h11 : X 1 1 = 1 := hd 1
  have hpsd' : -(2 + 1 / 380000) ≤ X 0 1 + X 1 0 := by linarith
  have hfrob := hX.2.2
  rw [frob_sl] at hfrob
  push_cast at hfrob
  linarith

/-! ## 2.  The body at the window is non-empty

The witness `Xw`: diagonal `1 + d/4`, off-diagonal `−(1 + 3d/4)`.  Its PSD margin is exactly `d/2`
(attained at `x = (1,−1)`), its diagonal distance is exactly `d/4`, and its objective is
`−(2 + 3d/2) ≤ u_W + d/2 = −(2 + 5d/4)`. -/

/-- The non-emptiness witness at the window level. -/
def Xw : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 1 + 1 / 1520000 else -(1 + 3 / 1520000)

theorem Xw_qf (x : Fin 2 → ℝ) :
    QMCLeafB.BallFloor.qfR Xw x
      = (1 + 1 / 1520000) * (x 0 ^ 2 + x 1 ^ 2) - 2 * (1 + 3 / 1520000) * (x 0 * x 1) := by
  simp [QMCLeafB.BallFloor.qfR, Xw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem Xw_frob :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) Xw = -(2 + 6 / 1520000) := by
  rw [frob_sl]
  simp [Xw]
  norm_num

/-- The window body is non-empty. -/
theorem nonempty_W :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) (-(2 + 7 / 1520000))
      ((1 / 380000 : ℚ) : ℝ) Xw := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [Xw_qf]
    have hx : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    rw [hx]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1)]
  · intro i
    fin_cases i <;> simp [Xw] <;> norm_num
  · rw [Xw_frob]
    norm_num

/-! ## 3.  The same body carries the campaign's ball

Centre `Xb`: diagonal `1 + 3d/16`, off-diagonal `−(1 + 5d/8)`.  Its three slacks are PSD `7d/16`,
diagonal `3d/16`, level `0`, and the Frobenius ball of radius `d/24 = 1/9120000` (exactly the
campaign radius `P.dq/(8(c_A+1))` at `G₁`) fits inside all three. -/

/-- The ball centre at the window level. -/
def Xb : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 1 + 5 / 9120000 else -(1 + 16 / 9120000)

theorem Xb_qf (x : Fin 2 → ℝ) :
    QMCLeafB.BallFloor.qfR Xb x
      = (1 + 5 / 9120000) * (x 0 ^ 2 + x 1 ^ 2) - 2 * (1 + 16 / 9120000) * (x 0 * x 1) := by
  simp [QMCLeafB.BallFloor.qfR, Xb, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem Xb_qf_lb (x : Fin 2 → ℝ) :
    -(11 / 9120000) * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR Xb x := by
  rw [Xb_qf, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 - x 1)]

theorem Xb_frob :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) Xb = -(2 + 32 / 9120000) := by
  rw [frob_sl]
  simp [Xb]
  norm_num

theorem Xb_frobNormSq :
    QMCLeafB.BallFloor.frobNormSq Xb
      = 2 * (1 + 5 / 9120000) ^ 2 + 2 * (1 + 16 / 9120000) ^ 2 := by
  simp [QMCLeafB.BallFloor.frobNormSq, Xb, Fin.sum_univ_two]
  norm_num

theorem wMatrix_asum : (∑ i : Fin 2, ∑ j : Fin 2, |QMCLeafB.wMatrix G₁ i j|) = 2 := by
  simp [Fin.sum_univ_two, QMCLeafB.AnchorFactsM2.wMatrix_G₁_00,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_11, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10]
  norm_num

/-- The ball of radius `d/24` around `Xb` lies in the window body (Frobenius form). -/
theorem Xb_matBall :
    QMCLeafB.BallFloor.matBall Xb (1 / 9120000) ⊆
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
        (-(2 + 7 / 1520000)) ((1 / 380000 : ℚ) : ℝ) := by
  refine QMCLeafB.BallM2.matBall_subset_relaxBodyLE (A := QMCLeafB.wMatrix G₁)
    (u := -(2 + 7 / 1520000)) (δ := ((1 / 380000 : ℚ) : ℝ)) (cA := 2) (r := 1 / 9120000)
    (m₁ := 11 / 9120000) (m₂ := 5 / 9120000) (m₃ := 10 / 9120000) (by norm_num) (by norm_num) ?_
    (by simpa using Xb_qf_lb) ?_ ?_ ?_ ?_ ?_
  · rw [wMatrix_asum]
  · intro i
    fin_cases i <;> simp [Xb] <;> norm_num
  · rw [Xb_frob]; norm_num
  · norm_num
  · norm_num
  · norm_num

/-- The ball is inside the run's relaxation `relaxBall` (body *and* norm bound), at exactly the
campaign radius `P.dq/(8·(c_A+1))`. -/
theorem Xb_ball {P : QMCLeafB.FinalStroke.RunParams G₁} (hdq : P.dq = 1 / 380000)
    (hcAq : P.cAq = 2) :
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat Xb)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G₁ tW P := by
  have hr : (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) = 1 / 9120000 := by
    rw [hdq, hcAq]; norm_num
  rw [hr]
  intro z hz
  have hE : QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z - Xb)
      ≤ (1 / 9120000) ^ 2 := by
    have hfn : QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z - Xb)
        = ∑ k : Fin (2 * 2), (QMCLeafB.AnswerProducer.flat
            (QMCLeafB.Boundary.unflat z - Xb)) k ^ 2 :=
      (QMCLeafB.Boundary.sum_sq_flat (QMCLeafB.Boundary.unflat z - Xb)).symm
    rw [hfn]
    refine le_trans (le_of_eq ?_) hz
    exact Finset.sum_congr rfl fun k _ => by
      simp [QMCLeafB.Boundary.flat_sub, QMCLeafB.Boundary.flat_unflat]
  refine ⟨?_, ?_⟩
  · rw [level_W, hdq]
    exact Xb_matBall (show QMCLeafB.Boundary.unflat z
      ∈ QMCLeafB.BallFloor.matBall Xb (1 / 9120000) from hE)
  · have hnorm : (∑ k, z k ^ 2) = QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z) := by
      rw [show (∑ k, z k ^ 2)
          = ∑ k : Fin (2 * 2),
              (QMCLeafB.AnswerProducer.flat (QMCLeafB.Boundary.unflat z)) k ^ 2 from by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [QMCLeafB.Boundary.flat_unflat]]
      rw [QMCLeafB.Boundary.sum_sq_flat]
      rfl
    have hdec : QMCLeafB.Boundary.unflat z = Xb + (QMCLeafB.Boundary.unflat z - Xb) :=
      (add_sub_cancel Xb (QMCLeafB.Boundary.unflat z)).symm
    rw [hnorm, hdec]
    have hb := QMCLeafB.BallM2.frobNormSq_add_le Xb (QMCLeafB.Boundary.unflat z - Xb)
    have h3 : (3 : ℝ) * QMCLeafB.BallFloor.frobNormSq (QMCLeafB.Boundary.unflat z - Xb)
        ≤ 3 * (1 / 9120000) ^ 2 := by linarith
    have hM : ((2 * (G₁.n : ℚ) ^ 2 + 2 * (P.dq) ^ 2 : ℚ) : ℝ)
        = 8 + 2 * (1 / 380000 : ℝ) ^ 2 := by
      rw [n₁, hdq]; push_cast; ring
    rw [hM]
    have h4 : (3 / 2 : ℝ) * QMCLeafB.BallFloor.frobNormSq Xb
        = 3 * (1 + 5 / 9120000) ^ 2 + 3 * (1 + 16 / 9120000) ^ 2 := by
      rw [Xb_frobNormSq]; ring
    rw [h4] at hb
    have hnum : (0 : ℝ) < (1 / 9120000) ^ 2 := by norm_num
    nlinarith [hb, h3, hnum]

/-! ## 4.  The no-go: a gated *sound* run cannot exist at the window

`sound` is "every `ok` round's centre is a member of the run's own body" — the exact content the
grid enlargement supplies for `hok`; `gated` is "every `ok` round's centre has unit diagonal" — the
exact content of `dvR s = 0`.  The volume obstruction (`Xb_ball` + `no_runParts_of_ball`) forces the
bit `true`; the rigidity forces every `ok` below the horizon to be `false`. -/

theorem no_runParts_of_gated_sound
    {P : QMCLeafB.FinalStroke.RunParams G₁} (hdq : P.dq = 1 / 380000) (hcAq : P.cAq = 2)
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G₁ tW P)
    (X : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hsound : ∀ k, k < P.K * P.m → B.ok k = true →
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) (-(2 + 7 / 1520000))
        ((1 / 380000 : ℚ) : ℝ) (X k))
    (hgate : ∀ k, k < P.K * P.m → B.ok k = true → ∀ i, X k i i = 1) :
    False := by
  classical
  have htrue : o G₁ tW = true :=
    QMCLeafB.BallM2.no_runParts_of_ball hn₁ (Xb_ball hdq hcAq) B
  have hall : ∀ k, k < P.K * P.m → B.ok k = false := by
    intro k hk
    by_contra hcon
    have hok : B.ok k = true := by
      cases h : B.ok k with
      | false => exact absurd h hcon
      | true => rfl
    exact no_unitDiag_of_level (by norm_num) (hsound k hk hok) (hgate k hk hok)
  have hfalse : o G₁ tW = false := by
    rw [B.hverdict]
    exact (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).mpr hall
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

/-! ## 5.  `hcomplete` is false for every sound, gated program

`HComplete` is the campaign's `hcomplete` shape (verbatim quantifiers over the interior bracket and
the non-empty body).  At `(G₁,t_W)` the body is non-empty (`nonempty_W`) and interior
(`interior_W`), and any run whose `ok` stream is sound and gated reads `false` there. -/

/-- `hcomplete` in the campaign's shape, at an arbitrary bit and parameter family. -/
def HComplete (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : ∀ G : QuantumMaxCutEnergy.Input, QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → _root_.AsmM8.Interior G t →
    ¬ _root_.AsmM8.EmptyBody G t (P G) → o G t = true

/-- `hcomplete` fails at the window for every sound, gated bit.  The bit is the `anyOk` read-out of a
stream `ok` whose `true` entries (below the horizon) are at members with unit diagonal. -/
theorem not_hcomplete_of_gated_sound
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : ∀ G : QuantumMaxCutEnergy.Input, QMCLeafB.FinalStroke.RunParams G)
    (hP₁ : Pfam G₁ = P₁)
    (ok : ℕ → Bool)
    (hbit : o G₁ tW = QMCLeafB.SimLoop.anyOk ok (P₁.K * P₁.m))
    (X : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hsound : ∀ k, k < P₁.K * P₁.m → ok k = true →
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) (-(2 + 7 / 1520000))
        ((1 / 380000 : ℚ) : ℝ) (X k))
    (hgate : ∀ k, k < P₁.K * P₁.m → ok k = true → ∀ i, X k i i = 1) :
    ¬ HComplete o Pfam := by
  intro hC
  have hall : ∀ k, k < P₁.K * P₁.m → ok k = false := by
    intro k hk
    by_contra hcon
    have hok : ok k = true := by
      cases h : ok k with
      | false => exact absurd h hcon
      | true => rfl
    exact no_unitDiag_of_level (by norm_num) (hsound k hk hok) (hgate k hk hok)
  have hfalse : o G₁ tW = false := by
    rw [hbit]
    exact (QMCLeafB.SimLoop.anyOk_eq_false_iff ok (P₁.K * P₁.m)).mpr hall
  have hne : ¬ _root_.AsmM8.EmptyBody G₁ tW (Pfam G₁) := by
    rw [hP₁]
    intro hE
    refine hE Xw ?_
    rw [level_W, dq₁]
    exact nonempty_W
  have htrue := hC G₁ tW hn₁ interior_W hne
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue


/-! ## 6.  The gate is *definitional* at the campaign round

`okW s = true` on the interior branch means `(oracleV s).1 = false`, and `oracleV` answers `cut`
(`(true, ·)`) whenever `dvR s ≠ 0` (the diagonal-repair branch) — so `ok` at `roundWG` forces
`dvR s = 0`, i.e. `∑ i |Xᵢᵢ − 1| = 0`, i.e. every diagonal entry of the state's block is exactly `1`.
This is the `hgate` hypothesis of §4/§5, at the campaign's own program; the §4 soundness hypothesis
is what the grid enlargement (`LdltCertM5.pivPsdMargin_of_tolerance`, `stD ≥ 2n²/dqShallow`) adds. -/

/-- **The `ok` flag is gated by `dvR = 0`** (interior branch of `okW`). -/
theorem okW_dvR {s : QMCLeafB.RoundProgram.RSt}
    (hlo : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s))
    (h : QMCLeafB.OkLower.okW s = true) : QMCLeafB.RoundProgram.dvR s = 0 := by
  unfold QMCLeafB.OkLower.okW at h
  rw [if_neg hlo] at h
  unfold QMCLeafB.OkLower.oracleV at h
  by_cases hdv : QMCLeafB.RoundProgram.dvR s = 0
  · exact hdv
  · rw [if_neg hdv] at h
    exact absurd h (by simp)

/-- A sum of absolute-value terms over a list is non-negative. -/
theorem sum_map_absq_nonneg (l : List ℕ) (f : ℕ → ℚ) :
    0 ≤ (l.map (fun i => QMCLeafB.RoundProgram.absq (f i - 1))).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons]
    have h1 : 0 ≤ QMCLeafB.RoundProgram.absq (f a - 1) := by
      rw [QMCLeafB.RoundProgram.absq_eq]; exact abs_nonneg _
    linarith

/-- **Vanishing diagonal defect identifies the diagonal.**  If `∑ i |f i − 1| = 0` then `f i = 1` at
every listed index. -/
theorem sum_map_absq_eq_zero {l : List ℕ} {f : ℕ → ℚ}
    (h : (l.map (fun i => QMCLeafB.RoundProgram.absq (f i - 1))).sum = 0) :
    ∀ i ∈ l, f i = 1 := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons a t ih =>
    intro i hi
    rw [List.map_cons, List.sum_cons] at h
    have hhead_nn : 0 ≤ QMCLeafB.RoundProgram.absq (f a - 1) := by
      rw [QMCLeafB.RoundProgram.absq_eq]; exact abs_nonneg _
    have htail_nn : 0 ≤ (List.map (fun i => QMCLeafB.RoundProgram.absq (f i - 1)) t).sum :=
      sum_map_absq_nonneg t f
    have hhead : QMCLeafB.RoundProgram.absq (f a - 1) = 0 := by linarith
    have htail : (List.map (fun i => QMCLeafB.RoundProgram.absq (f i - 1)) t).sum = 0 := by linarith
    rcases List.mem_cons.mp hi with rfl | hmem
    · rw [QMCLeafB.RoundProgram.absq_eq, abs_eq_zero] at hhead
      linarith
    · exact ih htail i hmem

/-- **`dvR = 0` pins the state's diagonal to `1`.** -/
theorem entV_diag_of_dvR {s : QMCLeafB.RoundProgram.RSt} (h : QMCLeafB.RoundProgram.dvR s = 0)
    {i : ℕ} (hi : i ∈ QMCLeafB.RoundProgram.idxs (QMCLeafB.RoundProgram.stN s,
      QMCLeafB.RoundProgram.stX s)) :
    QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s) i i = 1 := by
  have h' : (List.map (fun k => QMCLeafB.RoundProgram.absq
      (QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s)
        k k - 1))
        (QMCLeafB.RoundProgram.idxs (QMCLeafB.RoundProgram.stN s,
          QMCLeafB.RoundProgram.stX s))).sum = 0 := by
    simpa [QMCLeafB.RoundProgram.dvR, QMCLeafB.RoundProgram.diagSumV] using h
  exact sum_map_absq_eq_zero h' i hi

/-- **The campaign's `ok` state carries a unit-diagonal block**: the concrete form of the gate. -/
theorem matOf_diag_of_okW {s : QMCLeafB.RoundProgram.RSt}
    (hlo : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s))
    (h : QMCLeafB.OkLower.okW s = true)
    (hlen : QMCLeafB.RoundProgram.stN s ≤ (QMCLeafB.RoundProgram.stX s).length)
    (i : Fin (QMCLeafB.RoundProgram.stN s)) :
    QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s) (QMCLeafB.RoundProgram.stX s) i i = 1 := by
  show QMCLeafB.RoundProgram.entV (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s)
    (i : ℕ) (i : ℕ) = 1
  refine entV_diag_of_dvR (okW_dvR hlo h) ?_
  rw [QMCLeafB.PivExact.idxs_eq hlen]
  exact List.mem_range.mpr i.isLt

#print axioms QMCLeafB.Thin32M2.no_unitDiag_of_level
#print axioms QMCLeafB.Thin32M2.nonempty_W
#print axioms QMCLeafB.Thin32M2.Xb_ball
#print axioms QMCLeafB.Thin32M2.no_runParts_of_gated_sound
#print axioms QMCLeafB.Thin32M2.not_hcomplete_of_gated_sound
#print axioms QMCLeafB.Thin32M2.okW_dvR
#print axioms QMCLeafB.Thin32M2.entV_diag_of_dvR
#print axioms QMCLeafB.Thin32M2.matOf_diag_of_okW

/-! ## 7.  The window, quantitatively

The two computations above are monotone in the level, so they hold on the whole interval
`[−Rq − 7d/4, −Rq − 3d/2)` — a window of width `d/4`.  On it the body is ball-bearing and yet has
no unit-diagonal member; and `−Rq − 3d/2` is exactly the level at which a unit-diagonal member
appears.  So the gate costs the program exactly `d/2` of level: the recognisable body is the body at
the shifted level `u − d/2`. -/

/-- The relaxed body is monotone in its level. -/
theorem relaxBodyLE_mono {u u' δ : ℝ} (hu : u ≤ u') {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u δ X) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u' δ X :=
  ⟨hX.1, hX.2.1, le_trans hX.2.2 (by linarith)⟩

/-- **THE FAT WINDOW.**  At every level `u ∈ [−Rq − 7d/4, −Rq − 3d/2)` the relaxed body carries the
campaign ball of radius `d/24`, and yet no member of it has a unit diagonal. -/
theorem window_ball_and_rigidity {u : ℝ} (hlo : -(2 + 7 / 1520000) ≤ u)
    (hhi : u < -(2 + 3 / 760000)) :
    QMCLeafB.BallFloor.matBall Xb (1 / 9120000) ⊆
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u ((1 / 380000 : ℚ) : ℝ) ∧
      (∀ X, QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u ((1 / 380000 : ℚ) : ℝ) X →
        ¬ (∀ i, X i i = 1)) := by
  refine ⟨?_, fun X hX => no_unitDiag_of_level hhi hX⟩
  intro z hz
  exact relaxBodyLE_mono hlo (Xb_matBall hz)

/-- **Non-emptiness on the whole window**: the witness `Xw` works at every level `u ≥ −Rq − 2d`. -/
theorem nonempty_of_level {u : ℝ} (hu : -(2 + 2 / 380000) ≤ u) :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u ((1 / 380000 : ℚ) : ℝ) Xw := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [Xw_qf]
    have hx : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    rw [hx]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1)]
  · intro i
    fin_cases i <;> simp [Xw] <;> norm_num
  · rw [Xw_frob]
    push_cast
    linarith

/-- The unit-diagonal test point at the gate's threshold. -/
def Xt : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 1 else -(1 + 1 / 760000)

theorem Xt_diag : ∀ i, Xt i i = 1 := by
  intro i; fin_cases i <;> simp [Xt]

theorem Xt_qf (x : Fin 2 → ℝ) :
    QMCLeafB.BallFloor.qfR Xt x = (x 0 ^ 2 + x 1 ^ 2) - 2 * (1 + 1 / 760000) * (x 0 * x 1) := by
  simp [QMCLeafB.BallFloor.qfR, Xt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem Xt_frob : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₁) Xt = -(2 + 2 / 760000) := by
  rw [frob_sl]
  simp [Xt]
  norm_num

/-- **The gate's exact cost.**  A unit-diagonal member exists at the level `−Rq − 3d/2`
(`X = !![1, s; s, 1]` with `s = −(1 + d/2)`: PSD margin `d/2`, diagonal `0`, objective `−(2 + d)`),
and — by `no_unitDiag_of_level` — at no lower level.  Hence the program's recognisable body is the
body shifted down by `d/2` in the level. -/
theorem unitDiag_member_at_threshold :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) (-(2 + 3 / 760000))
        ((1 / 380000 : ℚ) : ℝ) Xt ∧
      (∀ i, Xt i i = 1) := by
  refine ⟨⟨?_, ?_, ?_⟩, Xt_diag⟩
  · intro x
    rw [Xt_qf]
    have hx : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    rw [hx]
    nlinarith [sq_nonneg (x 0 - x 1)]
  · intro i
    rw [Xt_diag i]
    norm_num
  · rw [Xt_frob]
    norm_num

#print axioms QMCLeafB.Thin32M2.window_ball_and_rigidity
#print axioms QMCLeafB.Thin32M2.nonempty_of_level
#print axioms QMCLeafB.Thin32M2.unitDiag_member_at_threshold

/-! ## 8.  The other side of the dichotomy: gate-free runs read `true` at the window

So the failure above is a *test-design* failure, not a search failure: at the same point the
volume lane already forces every run record's bit to `true`. -/

/-- **At `(G₁,t_W)` every run record forces the bit `true`** — the ball is in the body
(`Xb_ball`), so `BallM2.no_runParts_of_ball` applies with no gate anywhere. -/
theorem bit_true_of_ball {P : QMCLeafB.FinalStroke.RunParams G₁} (hdq : P.dq = 1 / 380000)
    (hcAq : P.cAq = 2) {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G₁ tW P) : o G₁ tW = true :=
  QMCLeafB.BallM2.no_runParts_of_ball hn₁ (Xb_ball hdq hcAq) B

/-- **The window dichotomy.**  At the window level the relaxed body is non-empty and ball-bearing,
yet no unit-diagonal member exists; consequently a run whose `ok` centres are members with unit
diagonal is impossible, while a gate-free run is forced to `true`.  The exact gate is therefore the
obstruction, and dropping it (`dvR s ≤ dqOf s / 4`) is the minimal repair. -/
theorem window_dichotomy {P : QMCLeafB.FinalStroke.RunParams G₁} (hdq : P.dq = 1 / 380000)
    (hcAq : P.cAq = 2) {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : QMCLeafB.FinalStroke.RunParts o G₁ tW P)
    (X : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hsound : ∀ k, k < P.K * P.m → B.ok k = true →
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) (-(2 + 7 / 1520000))
        ((1 / 380000 : ℚ) : ℝ) (X k))
    (hgate : ∀ k, k < P.K * P.m → B.ok k = true → ∀ i, X k i i = 1) :
    False :=
  no_runParts_of_gated_sound hdq hcAq B X hsound hgate

#print axioms QMCLeafB.Thin32M2.bit_true_of_ball
#print axioms QMCLeafB.Thin32M2.window_dichotomy

/-! ## 9.  The concrete round: a window `okW` state cannot carry the `Hpsd` margin

This wires the campaign's own bridges (`OkLower.relaxMem_of_oracleV_ok`,
`BitdecM4.relaxMem_iff_bodyLE`, `HemptyR_M3.castMat_wMatrixQ`) to the rigidity, so that the
`sound` hypothesis of §4/§5 is *derived* rather than assumed at a concrete state: an `okW` state at
the window whose pivot certifies the campaign tolerance (`hpsd`, exactly `Hpsd`'s conclusion at
`dq = dqShallow`) is impossible.  The remaining hypotheses are the campaign's own invariance plugs
(`stT`, `epsOf`, `dqOf`, and the weight-code coherence `hF`). -/

theorem no_okW_at_window (s : QMCLeafB.RoundProgram.RSt)
    (hN : QMCLeafB.RoundProgram.stN s = 2)
    (hlen : QMCLeafB.RoundProgram.stN s ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hT : QMCLeafB.RoundProgram.stT s = tW)
    (hEps : QMCLeafB.RoundT.epsOf s = 1 / 20000)
    (hdq : QMCLeafB.OkLower.dqOf s = 1 / 380000)
    (hpos : 0 < QMCLeafB.RoundT.massV s)
    (hlo : ¬ (0 ≤ QMCLeafB.RoundProgram.stT s + QMCLeafB.RoundT.epsOf s))
    (hF : QMCLeafB.RoundProgram.fvR s
      = QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁)
          (QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX s)))
    (hpsd : ∀ x : Fin 2 → ℚ, -(QMCLeafB.OkLower.dqOf s / 2) * (∑ i, x i ^ 2) ≤
      QMCLeafB.SepOracle.qf (QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX s)) x)
    (hok : QMCLeafB.OkLower.okW s = true) : False := by
  classical
  -- the gate: `okW` at an interior state means `oracleV` answers `ok`
  have hok' : (QMCLeafB.OkLower.oracleV s).1 = false := by
    unfold QMCLeafB.OkLower.okW at hok
    rw [if_neg hlo] at hok
    simpa using hok
  have hdv : QMCLeafB.RoundProgram.dvR s = 0 := (QMCLeafB.OkLower.oracleV_ok s hok').1
  have hdqpos : 0 < QMCLeafB.OkLower.dqOf s := by rw [hdq]; norm_num
  -- the diagonal of the state's block is exactly 1
  have hdiag1 : ∀ i : Fin 2,
      QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX s) i i = 1 := by
    intro i
    have hm : (i : ℕ) ∈ QMCLeafB.RoundProgram.idxs (QMCLeafB.RoundProgram.stN s,
        QMCLeafB.RoundProgram.stX s) := by
      rw [QMCLeafB.PivExact.idxs_eq hlen, hN]
      exact List.mem_range.mpr i.isLt
    have h1 := entV_diag_of_dvR hdv hm
    have hpr : (2, QMCLeafB.RoundProgram.stX s)
        = (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s) := by rw [← hN]
    show QMCLeafB.RoundProgram.entV (2, QMCLeafB.RoundProgram.stX s) (i : ℕ) (i : ℕ) = 1
    rw [hpr]
    exact h1
  have hdiag : ∀ i : Fin 2,
      |QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX s) i i - 1|
        ≤ QMCLeafB.OkLower.dqOf s / 4 := by
    intro i
    rw [hdiag1 i]
    simp only [sub_self, abs_zero]
    positivity
  -- the campaign's own bridge: the ok state is a member, at its own level and tolerance
  have hmem := QMCLeafB.OkLower.relaxMem_of_oracleV_ok
    (A := QMCLeafB.Finalization.wMatrixQ G₁)
    (cX := QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX s)) (s := s)
    hF hok' hpos hpsd hdiag
  have hbody := (_root_.BitdecM4.relaxMem_iff_bodyLE
    (A := QMCLeafB.Finalization.wMatrixQ G₁)
    (cX := QMCLeafB.PivExact.matOf 2 (QMCLeafB.RoundProgram.stX s))
    (u := QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s)
    (δ := QMCLeafB.OkLower.dqOf s) hdqpos).mp hmem
  rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ] at hbody
  have hlev : (((QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s : ℚ)) : ℝ)
      = -(2 + 7 / 1520000) := by
    rw [hT, hEps]
    simp only [tW]
    push_cast
    norm_num
  have hdl : (((QMCLeafB.OkLower.dqOf s : ℚ)) : ℝ) = ((1 / 380000 : ℚ) : ℝ) := by rw [hdq]
  rw [hlev, hdl] at hbody
  refine no_unitDiag_of_level (by norm_num) hbody ?_
  intro i
  rw [QMCLeafB.SepOracle.castMat_apply, hdiag1 i]
  norm_num

#print axioms QMCLeafB.Thin32M2.no_okW_at_window

/-! ## 10.  The campaign's own family: `hcomplete` at `paramsKbc2` is false

`hcomplete` in `MechM6.leaf_of_hok_and_complete` is stated at the campaign family
`UnionShallow.paramsKbc2`.  The instantiation is `rfl`. -/

theorem campaign_hcomplete_false
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ok : ℕ → Bool)
    (hbit : o G₁ tW = QMCLeafB.SimLoop.anyOk ok (P₁.K * P₁.m))
    (X : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (hsound : ∀ k, k < P₁.K * P₁.m → ok k = true →
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) (-(2 + 7 / 1520000))
        ((1 / 380000 : ℚ) : ℝ) (X k))
    (hgate : ∀ k, k < P₁.K * P₁.m → ok k = true → ∀ i, X k i i = 1) :
    ¬ (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → _root_.AsmM8.Interior G t →
        ¬ _root_.AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → o G t = true) :=
  not_hcomplete_of_gated_sound o QMCLeafB.UnionShallow.paramsKbc2 rfl ok hbit X hsound hgate

#print axioms QMCLeafB.Thin32M2.campaign_hcomplete_false

end QMCLeafB.Thin32M2


