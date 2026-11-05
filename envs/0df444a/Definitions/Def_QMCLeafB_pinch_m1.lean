-- Prove2me | Definitions.Def_QMCLeafB_pinch_m1
-- name    : QMCLeafB_pinch_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:59:26.502506+00:00
-- url     : https://prove2.me/theorems/b010cda2-f48e-4dbe-aaf8-36dcc23f190d
-- title:
--   QMCLeafB pinch_m1
-- statement:
--   # leaf B phase 25 — m1, direction `pinch-machinery-read`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thrice
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_centre_adm_m1
/-
# leaf B phase 25 — m1, direction `pinch-machinery-read`

`Check_centre_adm_m1` fixed what the centre is: `diagPinch Q dq` = `Q` with its diagonal
**overwritten** by `1 − dq/4`, off-diagonals inherited.  It proved the *sufficient* direction
(`relaxMem_diagPinch`: unit diagonal + exact PSD + the `ok` test ⟹ the pinched centre is a member).
What the phase-25 tension needs is the **exact** criterion: at which levels a pinched matrix can be a
member at all, i.e. which slot fails and by how much at the sliver.

Deliverables, all at the banked definitions:

* §1 **the pinch's member criterion, as an iff.**  `relaxMem_diagPinch_iff`: for a diagonal-free
  weight matrix the pinched centre is a `RelaxMem` member **iff** the level is above the base's own
  objective and the base carries the quadratic-form margin that the `dq/4` diagonal drop costs.
  Unit-diagonal base: the margin is `dq/4` (`relaxMem_diagPinch_iff_unitDiag`) — *not* exact PSD,
  which sharpens the banked sufficient version — and for an exactly PSD base the criterion is
  literally the programme's own `ok` test (`relaxMem_diagPinch_iff_psd`).
* §2 **the pinch is forced, not chosen.**  `exists_mem_htrc_iff_pinned`: a member whose trace meets
  the conduit's ceiling `n(1 − dq/4)` is the same thing as a member on the pinned diagonal.  So
  `ThriceM3.PinchFeasible` is *exactly* "some `ok`-round centre can be a member", which is why
  `¬PinchFeasible` forces the bit `false`.
* §3 **the sliver arithmetic, exact in `t`.**  At `G₁` the pinched-member threshold is
  `t ≥ ε − dq` (`pinchFeasible_G₁_iff`, both directions, `−2` the base value) and the body's own
  nonemptiness threshold is `t ≥ ε − 2dq` (`not_bodyEmpty_G₁_iff`).  Hence the third stratum is
  exactly the band `[ε − 2dq, ε − dq)` above `−2` — of width `dq`, disjoint from both its
  neighbours, and containing the campaign's `t₁` at three quarters of its length.  The obstruction
  in `trace_le` is exactly `dq/4` at the sliver, and the whole band lies inside the leaf's own
  bracket `[-Rq, 0]`.
* §4 **the consequence for the phase's architecture.**  With the campaign's own `ok`-lane data
  (`hbit`, `hok`, `hdiag`) at `paramsKbc2`, the third stratum is *uninhabitable* at `(G₁, t₁)`:
  `¬PinchFeasible` forces `o G₁ t₁ = false`, while `BallM2.no_runParts_of_ball` (the sliver body
  carries the campaign ball) forces `o G₁ t₁ = true` for any `RunParts`.  So no `dq`/`ε` tuning that
  keeps the campaign's centre shape empties the stratum — the band is real, and the design question
  is not (a).

* §5 **the general-`n` floor** (`frob_pinned_floor`): every member on the pinned diagonal has
  objective at least `-(1 + dq/4)·Aoff`, `Aoff = ∑_{i≠j} A i j` — the pair bound
  `Q i j + Q j i ≥ -(2 + dq/2)` from `psd_margin` at `e_i+e_j`, plus `A` symmetric so the pairing
  only sees the symmetric part.  `not_pinchFeasible_of_level_lt` is its contrapositive.
* §6 **the campaign instance at every input** (`not_pinchFeasible_campaign`, with `wMatrixQ_symm`,
  `wMatrixQ_nonneg`): the pinch-free zone is `t < ε + (1+dq/4)·Aoff - dq/2 ≈ -Rq + ε`, i.e. the
  bottom `Rq/2` of the leaf's bracket `[-Rq,0]` — which is why the fix is the bracket, not `dq`/`ε`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom audits at the end of every section.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QMCLeafB.PinchM1

open QuantumMaxCutEnergy

/-! ## 1.  The pinch's member criterion, as an iff

`RelaxMem A cX u dq` has four slots: `0 < dq`, the quadratic-form margin `-(dq/2)‖x‖² ≤ qf cX x`,
the diagonal band `|cX i i - 1| ≤ dq/4`, and the objective ceiling `frob A cX ≤ u + dq/2`.  At
`cX = diagPinch Q dq` the first three are base-independent on their face (the diagonal is
overwritten, the off-diagonals inherited), so the whole criterion reduces to two conditions on `Q`. -/

/-- **The exact member criterion of the pinched centre** (diagonal-free weight matrix, `dq ≤ 4`).

`diagPinch Q dq` is a `RelaxMem` member at level `u` **iff** `0 < dq`, the base `Q` carries the
quadratic-form margin `-(dq/2)‖x‖²` *after* the `dq/4` diagonal drop is charged, and the base's own
objective is at most `u + dq/2`.  Nothing about `Q`'s diagonal is assumed: it is not read. -/
theorem relaxMem_diagPinch_iff {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hA : ∀ i, A i i = 0) (hdq4 : dq ≤ 4) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q dq) u dq ↔
      (0 < dq ∧
        (∀ x : Fin n → ℚ, -(dq / 2) * (∑ i, x i ^ 2)
          ≤ QMCLeafB.SepOracle.qf Q x
            + ∑ i, ((1 - dq / 4) - Q i i) * x i ^ 2) ∧
        QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) := by
  constructor
  · rintro ⟨hpos, hpsd, _hdiag, htr⟩
    refine ⟨hpos, ?_, ?_⟩
    · intro x
      have h := hpsd x
      rw [QMCLeafB.CentreAdm.qf_diagPinch] at h
      exact h
    · rw [QMCLeafB.CentreAdm.frob_diagPinch hA] at htr
      exact htr
  · rintro ⟨hpos, hpsd, htr⟩
    exact ⟨hpos, (fun x => by rw [QMCLeafB.CentreAdm.qf_diagPinch]; exact hpsd x),
      QMCLeafB.CentreAdm.abs_diagPinch Q hpos hdq4,
      (by rw [QMCLeafB.CentreAdm.frob_diagPinch hA]; exact htr)⟩

#print axioms QMCLeafB.PinchM1.relaxMem_diagPinch_iff

/-- **The unit-diagonal base**: the `dq/4` diagonal drop is charged once, so the pinched centre is a
member iff the base is PSD up to `dq/4` (not up to `dq/2`, and not necessarily exactly PSD) and the
base's objective is at most `u + dq/2`.  This is the sharp form of the banked
`CentreAdm.relaxMem_diagPinch`, whose hypothesis is exact PSD. -/
theorem relaxMem_diagPinch_iff_unitDiag {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hA : ∀ i, A i i = 0) (hdq4 : dq ≤ 4) (hQ : ∀ i, Q i i = 1) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q dq) u dq ↔
      (0 < dq ∧
        (∀ x : Fin n → ℚ, -(dq / 4) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf Q x) ∧
        QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) := by
  rw [relaxMem_diagPinch_iff hA hdq4]
  have hshift : ∀ x : Fin n → ℚ,
      ∑ i, ((1 - dq / 4) - Q i i) * x i ^ 2 = (-(dq / 4)) * (∑ i, x i ^ 2) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
    rw [hQ i]
    ring
  constructor
  · rintro ⟨hpos, hpsd, htr⟩
    refine ⟨hpos, (fun x => ?_), htr⟩
    have h := hpsd x
    rw [hshift x] at h
    linarith
  · rintro ⟨hpos, hpsd, htr⟩
    refine ⟨hpos, (fun x => ?_), htr⟩
    have h := hpsd x
    rw [hshift x]
    linarith

#print axioms QMCLeafB.PinchM1.relaxMem_diagPinch_iff_unitDiag

/-- **An exactly PSD base**: the criterion collapses to the programme's own `ok` test
(`frob A Q ≤ u + dq/2`).  Both directions: the pinch is available exactly when the `ok` test fires
at the state, so `PinchFeasible` is the `ok` lane's reachability condition and nothing more. -/
theorem relaxMem_diagPinch_iff_psd {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hA : ∀ i, A i i = 0) (hdq4 : dq ≤ 4) (hQ : ∀ i, Q i i = 1)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q dq) u dq ↔
      (0 < dq ∧ QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) := by
  rw [relaxMem_diagPinch_iff_unitDiag hA hdq4 hQ]
  constructor
  · rintro ⟨hpos, _hm, htr⟩
    exact ⟨hpos, htr⟩
  · rintro ⟨hpos, htr⟩
    refine ⟨hpos, (fun x => ?_), htr⟩
    have h0 : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    nlinarith [hpsd x, h0, hpos]

#print axioms QMCLeafB.PinchM1.relaxMem_diagPinch_iff_psd

/-! ## 2.  The pinch is forced by the conduit, not chosen by it

The conduit (`DriftExact`) asks for `hmem` at the queried centre and `hTrc : ∑ i, cX i i ≤
n(1 − dq/4)` at every centre.  `CentreAdm.pinch_of_trace` turns the pair into the entrywise statement
`cX i i = 1 − dq/4`.  So the `ok` lane's centre class is *exactly* the pinned-diagonal members:
`PinchFeasible` is not a design choice but the only thing an `ok` round can hand over. -/

/-- **A member meeting the trace ceiling is a member on the pinned diagonal, and conversely.** -/
theorem exists_mem_htrc_iff_pinned {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ} :
    (∃ Q : Matrix (Fin n) (Fin n) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem A Q u dq ∧ (∑ i, Q i i) ≤ (n : ℚ) * (1 - dq / 4))
      ↔ (∃ Q : Matrix (Fin n) (Fin n) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem A Q u dq ∧ ∀ i, Q i i = 1 - dq / 4) := by
  constructor
  · rintro ⟨Q, hM, htr⟩
    exact ⟨Q, hM, QMCLeafB.CentreAdm.pinch_of_trace hM htr⟩
  · rintro ⟨Q, hM, hdiag⟩
    refine ⟨Q, hM, ?_⟩
    have h1 : (∑ i, Q i i) = (n : ℚ) * (1 - dq / 4) := by
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hdiag i), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h1]

#print axioms QMCLeafB.PinchM1.exists_mem_htrc_iff_pinned

/-! ## 3.  The sliver, exact in `t`

At `G₁` (`n = 2`, one edge of weight `1`, `Rq = 2`, `ε = 1/20000`, `dq = 1/380000`) both thresholds
are exactly computable, because at `n = 2` the two extremal points are explicit:

* a **pinned** matrix has `psd_margin` at `x = (1,1)`: `Q₀₁ + Q₁₀ ≥ −(2 + dq/2)`, and `frob` *is*
  `Q₀₁ + Q₁₀` — so `PinchFeasible` needs `−(2 + dq/2) ≤ u + dq/2`, i.e. `t ≥ ε − 2 − dq`;
  the bound is attained by `Qpin` (off-diagonal `−(1 + dq/4)`).
* a **δ-tolerant** matrix has `psd_margin` at `x = (1,1)`: `X₀₁ + X₁₀ ≥ −dq − X₀₀ − X₁₁ ≥
  −(2 + 3dq/2)` using the top of the diagonal band `Xᵢᵢ ≤ 1 + dq/4` — so the body is nonempty iff
  `−(2 + 3dq/2) ≤ u + dq/2`, i.e. `t ≥ ε − 2 − 2dq`; attained by `Xbody`.

The gap between the two thresholds is exactly `dq`: the **third stratum is the band
`[ε − 2dq, ε − dq)` above `−2`**, and the sliver's `t₁` sits at three quarters of it. -/

/-- The sliver's tolerance, at the literal numbers. -/
abbrev dq₁ : ℚ := 1 / 380000

/-- The sliver's `ε` at the literal numbers (`ε = Rq/40000 = 2/40000`). -/
abbrev eps₁ : ℚ := 1 / 20000

/-- **The extremal pinned-diagonal matrix at `G₁`**: diagonal `1 − dq/4`, both off-diagonals
`−(1 + dq/4)`.  It attains the pinched floor `frob = −(2 + dq/2)`. -/
def Qpin : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => if i = j then 1 - dq₁ / 4 else -(1 + dq₁ / 4)

theorem Qpin_diag (i : Fin 2) : Qpin i i = 1 - dq₁ / 4 := by simp [Qpin]

theorem Qpin_01 : Qpin 0 1 = -(1 + dq₁ / 4) := by simp [Qpin]

theorem Qpin_10 : Qpin 1 0 = -(1 + dq₁ / 4) := by simp [Qpin]

theorem Qpin_qf (x : Fin 2 → ℚ) :
    QMCLeafB.SepOracle.qf Qpin x
      = (1 - dq₁ / 4) * (x 0 ^ 2 + x 1 ^ 2) + 2 * (-(1 + dq₁ / 4)) * (x 0 * x 1) := by
  simp [QMCLeafB.SepOracle.qf, Qpin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The pinched extremal's quadratic form is PSD up to exactly `dq/2` (it is the `dq/2` boundary
point of the band). -/
theorem Qpin_qf_lb (x : Fin 2 → ℚ) :
    -(dq₁ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf Qpin x := by
  rw [Qpin_qf, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 - x 1)]

theorem Qpin_frob :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) Qpin
      = -(2 + dq₁ / 2) := by
  rw [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01,
    QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11]
  rw [Qpin_01, Qpin_10]
  ring

/-- **The exact `PinchFeasible` threshold at `G₁`.**  A pinned-diagonal member exists at level
`t − ε` **iff** `t ≥ ε − 2 − dq`.  Below it the ok lane is unreachable at every centre choice,
above it `Qpin` realises the `ok` test at equality. -/
theorem pinchFeasible_G₁_iff (t : ℚ) :
    QMCLeafB.ThriceM3.PinchFeasible QMCLeafB.EmptyBodyM5.G₁ t QMCLeafB.AnchorFactsM2.P₁
      ↔ -(2 : ℚ) + eps₁ - dq₁ ≤ t := by
  have hdq : QMCLeafB.AnchorFactsM2.P₁.dq = dq₁ := QMCLeafB.EmptyBodyM5.dq₁_eq
  have heps : QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁ = eps₁ :=
    QMCLeafB.EmptyBodyM5.eps_G₁
  show (∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) Q
        (t - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁) QMCLeafB.AnchorFactsM2.P₁.dq
      ∧ ∀ i, Q i i = 1 - QMCLeafB.AnchorFactsM2.P₁.dq / 4) ↔ _
  simp only [hdq, heps]
  constructor
  · rintro ⟨Q, hM, hdiag⟩
    have hge := QMCLeafB.EmptyBodyM5.frob_ge_of_pinched (c := 1) (δ := dq₁) (u := t - eps₁)
      (by norm_num) QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00 QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01
      QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10 QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11 hdiag hM
    have hle := hM.trace_le
    simp only [dq₁, eps₁] at hge hle ⊢
    linarith
  · intro h
    refine ⟨Qpin, ⟨by norm_num, (fun x => Qpin_qf_lb x),
      (fun i => by rw [Qpin_diag i]; norm_num), ?_⟩, (fun i => Qpin_diag i)⟩
    rw [Qpin_frob]
    simp only [dq₁, eps₁] at h ⊢
    linarith

#print axioms QMCLeafB.PinchM1.pinchFeasible_G₁_iff

/-- **The extremal `dq`-tolerant real point at `G₁`**: diagonal `1 + dq/4` (top of the band), both
off-diagonals `−(1 + 3dq/4)`.  It attains the body floor `frob = −(2 + 3dq/2)`. -/
def Xbody : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then 1 + ((dq₁ : ℚ) : ℝ) / 4 else -(1 + 3 * ((dq₁ : ℚ) : ℝ) / 4)

theorem Xbody_diag (i : Fin 2) : Xbody i i = 1 + ((dq₁ : ℚ) : ℝ) / 4 := by simp [Xbody]

theorem Xbody_01 : Xbody 0 1 = -(1 + 3 * ((dq₁ : ℚ) : ℝ) / 4) := by simp [Xbody]

theorem Xbody_10 : Xbody 1 0 = -(1 + 3 * ((dq₁ : ℚ) : ℝ) / 4) := by simp [Xbody]

theorem Xbody_qf (x : Fin 2 → ℝ) :
    QMCLeafB.BallFloor.qfR Xbody x
      = (1 + ((dq₁ : ℚ) : ℝ) / 4) * (x 0 ^ 2 + x 1 ^ 2)
        + 2 * (-(1 + 3 * ((dq₁ : ℚ) : ℝ) / 4)) * (x 0 * x 1) := by
  simp [QMCLeafB.BallFloor.qfR, Xbody, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem Xbody_qf_lb (x : Fin 2 → ℝ) :
    -(((dq₁ : ℚ) : ℝ) / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR Xbody x := by
  rw [Xbody_qf, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 - x 1)]

theorem Xbody_frob :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁) Xbody
      = -(2 + 3 * ((dq₁ : ℚ) : ℝ) / 2) := by
  rw [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
    QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
  rw [Xbody_01, Xbody_10]
  ring

/-- **The exact body threshold at `G₁`.**  The real relaxed body is nonempty **iff**
`t ≥ ε − 2 − 2dq`: `Xbody` is in it at equality, and every point of it has `frob ≥ −(2 + 3dq/2)`
(the `(1,1)` inequality with the top of the diagonal band). -/
theorem not_bodyEmpty_G₁_iff (t : ℚ) :
    ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.EmptyBodyM5.G₁ t QMCLeafB.AnchorFactsM2.P₁
      ↔ -(2 : ℚ) + eps₁ - 2 * dq₁ ≤ t := by
  have hdq : QMCLeafB.AnchorFactsM2.P₁.dq = dq₁ := QMCLeafB.EmptyBodyM5.dq₁_eq
  have hRq : QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ = 2 :=
    QMCLeafB.EmptyBodyM5.Rq_G₁
  show (¬ ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁)
        (((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ)) : ℝ)))
        (((QMCLeafB.AnchorFactsM2.P₁.dq : ℚ)) : ℝ) X) ↔ _
  rw [hdq, hRq]
  constructor
  · intro h
    push_neg at h
    obtain ⟨X, hpsd, hdiag, hlev⟩ := h
    have hq := hpsd (fun _ : Fin 2 => (1 : ℝ))
    have hqf : QMCLeafB.BallFloor.qfR X (fun _ : Fin 2 => (1 : ℝ))
        = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
      simp [QMCLeafB.BallFloor.qfR, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hqf] at hq
    have hs : (∑ i : Fin 2, ((1 : ℝ)) ^ 2) = 2 := by norm_num
    rw [hs] at hq
    have h0 := abs_le.mp (hdiag 0)
    have h1 := abs_le.mp (hdiag 1)
    have hf : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁) X
        = X 0 1 + X 1 0 := by
      rw [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      rw [QMCLeafB.AnchorFactsM2.wMatrix_G₁_00, QMCLeafB.AnchorFactsM2.wMatrix_G₁_01,
        QMCLeafB.AnchorFactsM2.wMatrix_G₁_10, QMCLeafB.AnchorFactsM2.wMatrix_G₁_11]
      ring
    rw [hf] at hlev
    have h1' : ((1 / 380000 : ℚ) : ℝ) = 1 / 380000 := by norm_num
    rw [h1'] at hq h0 h1 hlev
    have h40000 : ((2 / 40000 : ℚ) : ℝ) = (1 / 20000 : ℝ) := by norm_num
    rw [h40000] at hlev
    have key : ((-(2 : ℚ) + 1 / 20000 - 2 * (1 / 380000) : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ) := by
      push_cast
      linarith [hq, h0.2, h1.2, hlev]
    have keyQ := Rat.cast_le (K := ℝ).mp key
    simpa [dq₁, eps₁] using keyQ
  · intro h hc
    refine hc Xbody ⟨Xbody_qf_lb, (fun i => by rw [Xbody_diag i]; norm_num), ?_⟩
    rw [Xbody_frob]
    have hr : (-(2 : ℚ) + 1 / 20000 - 2 * (1 / 380000) : ℚ) ≤ t := h
    have hr' : (-(2 : ℝ) + 1 / 20000 - 2 * (1 / 380000) : ℝ) ≤ (t : ℝ) := by
      have hc := Rat.cast_le (K := ℝ).mpr hr
      simpa using hc
    have hcast : ((dq₁ : ℚ) : ℝ) = 1 / 380000 := by norm_num [dq₁]
    have h40000 : ((2 / 40000 : ℚ) : ℝ) = 1 / 20000 := by norm_num
    rw [hcast, h40000]
    linarith

#print axioms QMCLeafB.PinchM1.not_bodyEmpty_G₁_iff

/-- **The third stratum at `G₁`, exactly**: a point of the leaf's bracket with a nonempty real body
and no pinched member is precisely a `t` in the band `[ε − 2dq, ε − dq)` above `−2`.  The band has
width `dq`; nothing in the campaign's slack split can make it empty, because `dq > 0`. -/
theorem thirdStratum_band_G₁ (t : ℚ) :
    (¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.EmptyBodyM5.G₁ t QMCLeafB.AnchorFactsM2.P₁
        ∧ ¬ QMCLeafB.ThriceM3.PinchFeasible QMCLeafB.EmptyBodyM5.G₁ t
            QMCLeafB.AnchorFactsM2.P₁)
      ↔ (-(2 : ℚ) + eps₁ - 2 * dq₁ ≤ t ∧ t < -(2 : ℚ) + eps₁ - dq₁) := by
  rw [not_bodyEmpty_G₁_iff, pinchFeasible_G₁_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, not_le.1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, not_le.2 h2⟩

#print axioms QMCLeafB.PinchM1.thirdStratum_band_G₁

/-- The band's three quarters point — the campaign's `t₁` — is inside it. -/
theorem t₁_in_band :
    -(2 : ℚ) + eps₁ - 2 * dq₁ ≤ QMCLeafB.AnchorFactsM2.t₁
      ∧ QMCLeafB.AnchorFactsM2.t₁ < -(2 : ℚ) + eps₁ - dq₁ := by
  unfold QMCLeafB.AnchorFactsM2.t₁
  constructor <;> norm_num [dq₁, eps₁]

#print axioms QMCLeafB.PinchM1.t₁_in_band

/-- Every `t` of the band is inside the leaf's own bracket `[-Rq, 0)` — so the band is not an
artefact of where the bracket happens to start. -/
theorem band_subset_bracket {t : ℚ}
    (h1 : -(2 : ℚ) + eps₁ - 2 * dq₁ ≤ t) (h2 : t < -(2 : ℚ) + eps₁ - dq₁) :
    -QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ ≤ t
      ∧ (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ)) : ℝ) := by
  rw [QMCLeafB.EmptyBodyM5.Rq_G₁]
  constructor
  · simp only [dq₁, eps₁] at h1 ⊢
    linarith
  · have h2' : (t : ℝ) < ((-(2 : ℚ) + 1 / 20000 - 1 / 380000 : ℚ) : ℝ) := by exact_mod_cast h2
    have h3 : ((-(2 : ℚ) + 1 / 20000 - 1 / 380000 : ℚ) : ℝ) < -((2 / 40000 : ℚ) : ℝ) := by
      norm_num
    push_cast at h2' h3
    linarith

#print axioms QMCLeafB.PinchM1.band_subset_bracket

/-! ## 4.  The consequence for the phase's architecture

The two machine-checked halves of the tension, composed.  At `(G₁, t₁)`:

* the run's own `ok` lane (`hbit`, `hok`, and the pinned centres `hdia` that
  `exists_mem_htrc_iff_pinned` shows the conduit forces) **cannot fire**, because `t₁` lies below the
  exact pinched threshold `ε − dq` (§3) — so the bit reads `false`
  (`ThriceM3.bit_false_at_exemplar`);
* `BallM2.no_runParts_of_ball` says the sliver body carries the campaign's ball, so **any**
  `RunParts` there reads `true`.

Hence no `RunParts` exists at the exemplar at all, the third stratum
(`ThriceM3.ThirdStratum`) is uninhabited, and `TripleSupply` at `paramsKbc2` is uninhabited — for
*every* `dq`/`ε`-tuned campaign whose ok lane is a member at a pinned centre.  This is the phase's
central question answered in the negative for branch (a). -/

/-- **The bit is forced `false` at the sliver and `true` for any `RunParts` there.**  Composing
`ThriceM3.bit_false_at_exemplar` with `BallM2.sliver_bit_true` kills the exemplar's run records
outright, under the campaign's own ok-lane data. -/
theorem no_runParts_at_sliver_of_campaign_oklane
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : o QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁
      = QMCLeafB.SimLoop.anyOk rb
        (QMCLeafB.AnchorFactsM2.P₁.K * QMCLeafB.AnchorFactsM2.P₁.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) (cX k)
        (QMCLeafB.AnchorFactsM2.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        QMCLeafB.AnchorFactsM2.P₁.dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2), cX k i i = 1 - QMCLeafB.AnchorFactsM2.P₁.dq / 4) :
    ¬ Nonempty (QMCLeafB.FinalStroke.RunParts o QMCLeafB.EmptyBodyM5.G₁
      QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.P₁) := by
  rintro ⟨B⟩
  have hfalse : o QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁ = false :=
    QMCLeafB.ThriceM3.bit_false_at_exemplar hbit hok hdia
  have htrue := QMCLeafB.BallM2.sliver_bit_true B
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

#print axioms QMCLeafB.PinchM1.no_runParts_at_sliver_of_campaign_oklane

/-- **The third stratum is uninhabited at the campaign.**  `ThriceM3.ThirdStratum` demands `RunParts`
at `(G₁,t₁)` (nonempty body, forced-`false` bit), and §4's dichotomy forbids it. -/
theorem not_thirdStratum_campaign
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : o QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁
      = QMCLeafB.SimLoop.anyOk rb
        (QMCLeafB.AnchorFactsM2.P₁.K * QMCLeafB.AnchorFactsM2.P₁.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) (cX k)
        (QMCLeafB.AnchorFactsM2.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        QMCLeafB.AnchorFactsM2.P₁.dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2), cX k i i = 1 - QMCLeafB.AnchorFactsM2.P₁.dq / 4) :
    QMCLeafB.ThriceM3.ThirdStratum o QMCLeafB.UnionShallow.paramsKbc2 → False := by
  intro H
  have hfalse : o QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁ = false :=
    QMCLeafB.ThriceM3.bit_false_at_exemplar hbit hok hdia
  have hne : ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁
      QMCLeafB.AnchorFactsM2.P₁ := by
    intro hb
    obtain ⟨X, hX⟩ := QMCLeafB.AnchorFactsM2.realBody_G₁
    exact hb X hX
  have hR := H QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
    QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1 QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2 hne hfalse
  have htrue := QMCLeafB.BallM2.sliver_bit_true hR
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

#print axioms QMCLeafB.PinchM1.not_thirdStratum_campaign

/-- **`TripleSupply` is uninhabited at the campaign** under the campaign's own ok-lane data.  The
thrice-split stroke `ThriceM3.runParts_of_triple` therefore has an inconsistent hypothesis set: its
`H.third` field cannot be filled, and its `trueBit` field is not the problem (`(G₀,−1/2)` fires). -/
theorem not_tripleSupply_campaign
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : o QMCLeafB.EmptyBodyM5.G₁ QMCLeafB.AnchorFactsM2.t₁
      = QMCLeafB.SimLoop.anyOk rb
        (QMCLeafB.AnchorFactsM2.P₁.K * QMCLeafB.AnchorFactsM2.P₁.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) (cX k)
        (QMCLeafB.AnchorFactsM2.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        QMCLeafB.AnchorFactsM2.P₁.dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2), cX k i i = 1 - QMCLeafB.AnchorFactsM2.P₁.dq / 4) :
    QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2 → False := by
  intro H
  exact not_thirdStratum_campaign o rb cX hbit hok hdia H.third

#print axioms QMCLeafB.PinchM1.not_tripleSupply_campaign

/-! ## 5.  The general-`n` pinched floor

`frob_ge_of_pinched` (phase 24) is the `n = 2`, `c = 1` instance.  The mechanism is general: a
pinned member can only be bad on the **pair sums** `Q i j + Q j i`, because `A` is symmetric and
diagonal-free, so `⟪A,Q⟫ = ⟪A, sym Q⟫`.  Each pair sum is floored at `−(2 + dq/2)` by `psd_margin`
at `e_i + e_j`.  So every pinned member has objective at least `−(1 + dq/4)·Aoff`, with
`Aoff = ∑_{i≠j} A i j` (for the campaign's `A = wMatrixQ G`, `Aoff` is twice the total weight, i.e.
`Rq G`).  Read contrapositively: **no pinched member exists at any level below the floor**. -/

/-- `qf` at the indicator of a two-point set: the four corners of the `{i,j}` block. -/
theorem qf_two_ones {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) {i j : Fin n} (hij : i ≠ j) :
    QMCLeafB.SepOracle.qf M (fun k => if k = i then (1 : ℚ) else if k = j then 1 else 0)
      = M i i + M i j + M j i + M j j := by
  have key : ∀ k, ∑ l, (if k = i then (1 : ℚ) else if k = j then 1 else 0)
      * (M k l * (if l = i then (1 : ℚ) else if l = j then 1 else 0))
      = (if k = i then (1 : ℚ) else if k = j then 1 else 0) * (M k i + M k j) := by
    intro k
    have h1 : ∑ l, M k l * (if l = i then (1 : ℚ) else if l = j then 1 else 0)
        = M k i + M k j := by
      have hsupp : ∀ l, l ∉ ({i, j} : Finset (Fin n)) →
          M k l * (if l = i then (1 : ℚ) else if l = j then 1 else 0) = 0 := by
        intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
        simp [hl.1, hl.2]
      rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))
        (fun l _ hl => hsupp l hl), Finset.sum_pair hij]
      simp [hij, Ne.symm hij]
    rw [← h1, Finset.mul_sum]
  rw [QMCLeafB.SepOracle.qf_eq_sum]
  simp only [key]
  have hsupp2 : ∀ k, k ∉ ({i, j} : Finset (Fin n)) →
      (if k = i then (1 : ℚ) else if k = j then 1 else 0) * (M k i + M k j) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [hk.1, hk.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))
    (fun k _ hk => hsupp2 k hk), Finset.sum_pair hij]
  simp [hij, Ne.symm hij]
  ring

#print axioms QMCLeafB.PinchM1.qf_two_ones

theorem sum_sq_two_ones {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (∑ k, (fun k => if k = i then (1 : ℚ) else if k = j then 1 else 0) k ^ 2) = 2 := by
  have hsupp : ∀ k, k ∉ ({i, j} : Finset (Fin n)) →
      (fun k => if k = i then (1 : ℚ) else if k = j then 1 else 0) k ^ 2 = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [hk.1, hk.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin n)))
    (fun k _ hk => hsupp k hk), Finset.sum_pair hij]
  simp [hij, Ne.symm hij]
  norm_num

#print axioms QMCLeafB.PinchM1.sum_sq_two_ones

/-- **The pair-sum floor**: at a pinned member, `Q i j + Q j i ≥ −(2 + dq/2)` for every `i ≠ j`. -/
theorem pair_sum_floor {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdiag : ∀ i, Q i i = 1 - dq / 4)
    (hM : QMCLeafB.RelaxOracle.RelaxMem A Q u dq) {i j : Fin n} (hij : i ≠ j) :
    -(2 + dq / 2) ≤ Q i j + Q j i := by
  have h := hM.psd_margin (fun k => if k = i then (1 : ℚ) else if k = j then 1 else 0)
  rw [qf_two_ones Q hij, sum_sq_two_ones hij, hdiag i, hdiag j] at h
  linarith

#print axioms QMCLeafB.PinchM1.pair_sum_floor

/-- **The off-diagonal sum pairs up with its own transpose** — the identity that makes the
`A`-pairing see only the symmetric part of `Q`. -/
theorem offdiag_sum_symm {n : ℕ} (A Q : Matrix (Fin n) (Fin n) ℚ)
    (hAsym : ∀ i j, A i j = A j i) :
    (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * Q i j)
      = ∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * ((Q i j + Q j i) / 2) := by
  have htr : (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * Q j i)
      = ∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * Q i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases h : i = j
    · simp [h]
    · rw [if_neg (Ne.symm h), if_neg h, hAsym j i]
  have hrow : ∀ i, (∑ j, if i = j then (0 : ℚ) else A i j * ((Q i j + Q j i) / 2))
      = (∑ j, if i = j then (0 : ℚ) else A i j * Q i j) / 2
        + (∑ j, if i = j then (0 : ℚ) else A i j * Q j i) / 2 := by
    intro i
    have hpt : ∀ j, (if i = j then (0 : ℚ) else A i j * ((Q i j + Q j i) / 2))
        = (if i = j then (0 : ℚ) else A i j * Q i j) / 2
          + (if i = j then (0 : ℚ) else A i j * Q j i) / 2 := by
      intro j
      by_cases h : i = j
      · simp [h]
      · simp only [if_neg h]; ring
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_div,
      Finset.sum_div]
  have hsplit : (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * ((Q i j + Q j i) / 2))
      = (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * Q i j) / 2
        + (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * Q j i) / 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_add_distrib, Finset.sum_div,
      Finset.sum_div]
  rw [hsplit, htr]
  ring

#print axioms QMCLeafB.PinchM1.offdiag_sum_symm

/-- **The general-`n` pinched floor.**  Every member on the pinned diagonal has objective at least
`−(1 + dq/4)·Aoff`, `Aoff = ∑_{i≠j} A i j`. -/
theorem frob_pinned_floor {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hA0 : ∀ i, A i i = 0) (hAsym : ∀ i j, A i j = A j i)
    (hAnn : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hdiag : ∀ i, Q i i = 1 - dq / 4)
    (hM : QMCLeafB.RelaxOracle.RelaxMem A Q u dq) :
    -(1 + dq / 4) * (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j)
      ≤ QMCLeafB.SepOracle.frob A Q := by
  have hfrob : QMCLeafB.SepOracle.frob A Q
      = ∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * Q i j := by
    rw [QMCLeafB.SepOracle.frob]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases h : i = j
    · subst h; rw [if_pos rfl, hA0 i]; ring
    · rw [if_neg h]
  rw [hfrob, offdiag_sum_symm A Q hAsym]
  have hstep : (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j * (-(2 + dq / 2) / 2))
      = (-(2 + dq / 2) / 2) * (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i = j
    · simp [h]
    · simp only [if_neg h]; ring
  have hc : -(1 + dq / 4) = (-(2 + dq / 2)) / 2 := by ring
  rw [hc, ← hstep]
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  by_cases h : i = j
  · simp [h]
  · simp only [if_neg h]
    have hp := pair_sum_floor hdiag hM h
    have hnn := hAnn i j h
    nlinarith

#print axioms QMCLeafB.PinchM1.frob_pinned_floor

/-- **No pinched member below the floor.**  If the level's ceiling is under the floor,
`PinchFeasible` fails outright — at every `G` and every pinned-diagonal centre shape. -/
theorem not_pinchFeasible_of_level_lt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hA0 : ∀ i, A i i = 0) (hAsym : ∀ i j, A i j = A j i)
    (hAnn : ∀ i j, i ≠ j → 0 ≤ A i j)
    (h : u + dq / 2 < -(1 + dq / 4) * (∑ i, ∑ j, if i = j then (0 : ℚ) else A i j)) :
    ¬ ∃ Q : Matrix (Fin n) (Fin n) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem A Q u dq ∧ ∀ i, Q i i = 1 - dq / 4 := by
  rintro ⟨Q, hM, hdiag⟩
  have hfl := frob_pinned_floor hdq hA0 hAsym hAnn hdiag hM
  have hce := hM.trace_le
  linarith

#print axioms QMCLeafB.PinchM1.not_pinchFeasible_of_level_lt

/-! ## 6.  The campaign instance: a hard floor at every input

`Aoff G = ∑_{i≠j} wMatrixQ G i j` is twice the total weight, i.e. `Rq G` (the identification is the
elementary pair/edge reindexing; only the sum itself is used below).  The floor of §5 therefore
reads: below `ε + (1 + dq/4)·Rq − dq/2` no pinched member exists at `G` — for **every** input `G`
and every centre.  The campaign's `dq ≈ ε/(9Rq)` makes that threshold `≈ −Rq + ε`, i.e. below
`−Rq/2 = −W`; the leaf's bracket `[−Rq, 0]` therefore has a full `Rq/2` of its bottom in the
pinch-free zone, while the natural bracket `[−W, 0]` misses it entirely. -/

/-- The off-diagonal weight sum at `G` (`= Rq G`, twice the total weight). -/
def Aoff (G : QuantumMaxCutEnergy.Input) : ℚ :=
  ∑ i, ∑ j, if i = j then (0 : ℚ) else QMCLeafB.Finalization.wMatrixQ G i j

/-- The weight matrix is symmetric. -/
theorem wMatrixQ_symm (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    QMCLeafB.Finalization.wMatrixQ G i j = QMCLeafB.Finalization.wMatrixQ G j i := by
  by_cases hij : i = j
  · rw [hij]
  · by_cases hlt : i < j
    · have hji : ¬ j < i := not_lt.mpr (le_of_lt hlt)
      simp only [QMCLeafB.Finalization.wMatrixQ_apply, dif_pos hlt, dif_neg hji]
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simp only [QMCLeafB.Finalization.wMatrixQ_apply, dif_neg hlt, dif_pos hji]

#print axioms QMCLeafB.PinchM1.wMatrixQ_symm

/-- The weight matrix has nonnegative off-diagonals. -/
theorem wMatrixQ_nonneg (G : QuantumMaxCutEnergy.Input) {i j : Fin G.n} (h : i ≠ j) :
    (0 : ℚ) ≤ QMCLeafB.Finalization.wMatrixQ G i j := by
  by_cases hlt : i < j
  · rw [QMCLeafB.Finalization.wMatrixQ_apply, dif_pos hlt]
    positivity
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)
    rw [QMCLeafB.Finalization.wMatrixQ_apply, dif_neg hlt, dif_pos hji]
    positivity

#print axioms QMCLeafB.PinchM1.wMatrixQ_nonneg

/-- **The campaign's pinch floor, at every input.**  Below
`ε + (1 + dq/4)·Aoff − dq/2` there is no pinched member at `G`: the `ok` lane of the campaign can
never fire there, whatever the run's centre stream. -/
theorem not_pinchFeasible_campaign (G : QuantumMaxCutEnergy.Input) {t : ℚ}
    (h : t - QMCLeafB.RundataCert.eps G + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2
      < -(1 + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) * Aoff G) :
    ¬ QMCLeafB.ThriceM3.PinchFeasible G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  rintro ⟨Q, hM, hdiag⟩
  exact not_pinchFeasible_of_level_lt (A := QMCLeafB.Finalization.wMatrixQ G)
    (u := t - QMCLeafB.RundataCert.eps G) (dq := (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (QMCLeafB.UnionShallow.paramsKbc2 G).hdq
    (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq)
    (fun i j => wMatrixQ_symm G i j)
    (fun i j h => wMatrixQ_nonneg G h)
    (by simpa [Aoff] using h) ⟨Q, hM, hdiag⟩

#print axioms QMCLeafB.PinchM1.not_pinchFeasible_campaign

end QMCLeafB.PinchM1


