-- Prove2me | Definitions.Def_QMCLeafB_orient
-- name    : QMCLeafB_orient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:45:59.022585+00:00
-- url     : https://prove2.me/theorems/6320d38a-de6e-4bcc-a5ba-a9933935e9a9
-- title:
--   QMCLeafB orient
-- statement:
--   # leaf B phase 23 — the `dM = −1` orientation of the drift machinery is DEAD at every
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_btwins
import Definitions.Def_QMCLeafB_emptybody
/-
# leaf B phase 23 — the `dM = −1` orientation of the drift machinery is DEAD at every
nonempty real body (swarm `smw1qbrnt`, member m1, direction d1 `dm1-reorientation`)

## What the direction asked

The one open stratum of the leaf is the interior point `(G, t)` with a **nonempty real** relaxed
body and **no pinched member** (exemplar `(G₁, t₁)`: `Check_emptybody2_m5` /
`Check_audit2_m5` §5).  There every round below the horizon is a cut round, so
`runParts_of_dilated`'s drift pair is owed in full, and at `dM = 1` the pair is
`tr (Cat k) ≤ tr (cX k) ≤ n(1 − dq/4)` — the ceiling `CraterM2.not_coreDataG` kills by positive
accumulation (round 20, `K·m ≥ 279`).  Phase 22's m1 finding f11 named the third candidate route:
the `dM = −1` orientation, where `hdriftd` *reverses* to `tr (cX k) ≤ diagSum (Cat k)`
(`Check_btwins_m1.hdriftd_neg_one_iff`), an inequality satisfied by the very overflow that kills
`dM = 1`.  This file is the falsification run on that route, as the direction requires.

## The answer: the reversed orientation dies at **round 0**, before any dynamics

`EngineIterates.Cat N 0 cd 0 = 0`: the engine starts at the origin.  Hence at the *first* cut
round the `hdriftd` slot of `runParts_of_dilated`/`_b` reads

    ⟨dM, 0 − cX 0⟩ ≤ 0   i.e.   0 ≤ ⟨dM, cX 0⟩,

while `hbody` reads `0 ≤ ⟨dM, X⟩ − ⟨dM, cX 0⟩` for every body point `X`.  So the two slots force

    **0 ≤ ⟨dM, cX 0⟩ ≤ ⟨dM, X⟩ for every body point X**     (`permit_gate`, §2)

— the direction and the round-0 query centre are pinned to the body's own side.  For the reversed
direction `dM = −1` this is

    0 ≤ −∑ᵢ (cX 0)ᵢᵢ   and   −∑ᵢ (cX 0)ᵢᵢ ≤ −∑ᵢ Xᵢᵢ,

i.e. `∑ᵢ Xᵢᵢ ≤ ∑ᵢ (cX 0)ᵢᵢ ≤ 0`.  But a nonempty real relaxed body has `Xᵢᵢ ≥ 1 − δ/4`
(`relaxBodyLE`'s `diag_near`), so `∑ᵢ Xᵢᵢ ≥ n(1 − δ/4) > 0`.  Contradiction
(`neg_one_dead`, §3).  Nothing here is asymptotic: no margin, no multiplier, no depth ledger, no
stream choice can rescue it, and the *same* argument kills every negative multiple `−q•1`, `q > 0`
(the slots at `−q•1` and at `−1` are the same pair of inequalities, `neg_smul_one_iff`), which is
exactly the `λ`-rescue `Check_cutbudget_m8.drift_overflow_scaled` used to save `dM = 1`.

At the producer level (§4) the bit supplies the last premise: `hverdict` plus `o G t = false`
makes `ok 0 = false` (`anyOk_eq_false_iff`), so round 0 *is* a cut round.  Hence the bounded
producer `runParts_of_dilated_b` has **no instantiation at `dM = −1`** at any point of the stratum
(§4 `not_dilated_neg_one`), and the anchor `(G₁, t₁)` is such a point (§5, the real body point is
explicit).

## What this does and does not say

* It kills route "reversed drift orientation" *as the shelf's producer states it*: `β = 0`
  (`RunPartsDilate.dilCut` passes `β := 0`, margin unchanged).  With `β > 0` (`RelaxCut.dilate`'s
  full form) `hbody` would read `⟨dM, X − cX⟩ ≥ −β` and the round-0 gate would only force
  `tr X ≤ β`; that is a *differently shaped* producer, and its price is the margin `λ·β` in the
  depth ledger — not this file's subject.
* It does **not** touch `dM = 1`, and it does not touch the nonempty stratum's other route
  (genuine separation streams at `dM = 1` with a centre that is not the pinched one).  What it does
  give that route is `permit_gate`: a necessary condition at round 0 that any direction proposal
  must pass, and whose `dM = 1` instance is the weak `0 ≤ tr (cX 0) ≤ inf_body tr`.

House discipline: `set_option autoImplicit false`; no proof-escape token; `#print axioms` after
every declaration (all `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.OrientM1

open QuantumMaxCutEnergy

/-! ## 1.  Three prerequisites: `Cat` at the origin, the empty diagonal read-out, the body's trace
floor, and the flat/cast bridge -/

/-- **The engine starts at the origin**: `Cat`'s initial centre at round `0` is `a0`. -/
theorem cat_zero (N : ℕ) (a0 : Fin N → ℝ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) :
    QMCLeafB.EngineIterates.Cat N a0 cd 0 = a0 := rfl

#print axioms QMCLeafB.OrientM1.cat_zero

/-- The diagonal read-out of the zero centre. -/
theorem diagSum_zero (n : ℕ) :
    QMCLeafB.DriftExact.diagSum (0 : Fin (n * n) → ℝ) = 0 := by
  simp [QMCLeafB.DriftExact.diagSum]

#print axioms QMCLeafB.OrientM1.diagSum_zero

/-- **The flat/cast bridge**: the real flat vector used by the drift slots is the flat of the cast
matrix.  (The drift slots write `fun i => ((flatQ dM i : ℚ) : ℝ)`; `hbody` writes `castMat dM`.) -/
theorem flat_castMat_cast (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    (fun i => ((QMCLeafB.RelaxOracle.flatQ Q i : ℚ) : ℝ))
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q) := by
  funext k
  simp [QMCLeafB.RelaxOracle.flatQ, QMCLeafB.AnswerProducer.flat,
    QMCLeafB.SepOracle.castMat_apply]

#print axioms QMCLeafB.OrientM1.flat_castMat_cast

/-- **A nonempty real relaxed body has positive trace**: `diag_near` gives `Xᵢᵢ ≥ 1 − δ/4`. -/
theorem trace_lower_of_body {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    (n : ℝ) * (1 - δ / 4) ≤ ∑ i, X i i := by
  obtain ⟨-, hdiag, -⟩ := hX
  have h : ∀ i : Fin n, 1 - δ / 4 ≤ X i i := by
    intro i
    have := (abs_le.mp (hdiag i)).1
    linarith
  calc (n : ℝ) * (1 - δ / 4) = ∑ _i : Fin n, (1 - δ / 4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i, X i i := Finset.sum_le_sum (fun i _ => h i)

#print axioms QMCLeafB.OrientM1.trace_lower_of_body

/-- The trace floor is strictly positive for `1 ≤ n` and `δ < 4` — the numerical content. -/
theorem trace_floor_pos {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : δ < 4) :
    (0 : ℝ) < (n : ℝ) * (1 - δ / 4) := by
  have h1 : (0 : ℝ) < 1 - δ / 4 := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos h2 h1

#print axioms QMCLeafB.OrientM1.trace_floor_pos

end QMCLeafB.OrientM1


namespace QMCLeafB.OrientM1

open QuantumMaxCutEnergy

/-! ## 2.  The round-0 orientation gate (any direction `dM`)

At the first round the engine's centre is the origin, so the `hdriftd` slot of the dilated
producer is a *half-space condition on the query centre alone*, and `hbody` puts the whole body on
the far side of it.  This is the one structural constraint every direction proposal has to pass. -/

/-- **The pairing bridge**: the drift slot's dot product against `flatQ dM` is `frob` against
`castMat dM`.  (Both sides are `∑ i, · * ·` — the two `frob`/`flat` conventions of the library.) -/
theorem frob_eq_dot {n : ℕ} (dM : Matrix (Fin n) (Fin n) ℚ) (Z : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM) Z
      = (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
          ⬝ᵥ QMCLeafB.AnswerProducer.flat Z := by
  rw [QMCLeafB.RelaxOracle.frob_eq_flat_dot, ← flat_castMat_cast n dM]
  rfl

#print axioms QMCLeafB.OrientM1.frob_eq_dot

/-- **The round-0 orientation gate.**  Suppose the `hdriftd` slot of the dilated producer holds at
the direction `dM` at round `0` (where the engine's centre is `0`), and `hbody` holds at the same
direction and round for a body point `X`.  Then

    0 ≤ ⟨dM, cX 0⟩ ≤ ⟨dM, X⟩,

i.e. the query centre's projection is nonnegative and dominated by every body point's.  Any
direction proposal for the crater has to pass this test, and the query centre it forces is on the
body's side. -/
theorem permit_gate {n : ℕ} (dM : Matrix (Fin n) (Fin n) ℚ) (Q : Matrix (Fin n) (Fin n) ℚ)
    (hd : (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ
        ((0 : Fin (n * n) → ℝ)
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) ≤ 0)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hb : 0 ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
      (X - QMCLeafB.SepOracle.castMat Q)) :
    (0 ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ
          QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
      ∧ ((fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ
            QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)
          ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ
              QMCLeafB.AnswerProducer.flat X) := by
  have h1 : 0 ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ
      QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q) := by
    have h := hd
    rw [dotProduct_sub, dotProduct_zero] at h
    linarith
  refine ⟨h1, ?_⟩
  have h2 : 0 ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ
      QMCLeafB.AnswerProducer.flat
        (X - QMCLeafB.SepOracle.castMat Q) := by
    have h := hb
    rw [frob_eq_dot] at h
    exact h
  rw [QMCLeafB.Boundary.flat_sub, dotProduct_sub] at h2
  linarith

#print axioms QMCLeafB.OrientM1.permit_gate

/-- **The normal slot is orientation-locked.**  `hdriftc` at round `0` reads
`−marg 0 / 2 ≤ ⟨c₀, cX 0⟩`: the recorded normal's projection of the query centre is bounded
*below*.  Unlike `hdriftd` this does not flip with `dM` (the recorded normal is the oracle's, not
the dilation direction), so "both budgets reversed" is not a coherent package: only the trace slot
has a reversed reading. -/
theorem driftc_zero_reading {n : ℕ} (c z : Fin (n * n) → ℝ) (m : ℝ)
    (hd : c ⬝ᵥ ((0 : Fin (n * n) → ℝ) - z) ≤ m / 2) :
    -(m / 2) ≤ c ⬝ᵥ z := by
  rw [dotProduct_sub, dotProduct_zero] at hd
  linarith

#print axioms QMCLeafB.OrientM1.driftc_zero_reading

/-! ## 3.  The reversed orientation `dM = −1` is dead at a nonempty real body -/

/-- **The reversed drift slot at round 0 is `tr (cX 0) ≤ 0`** — `Check_btwins_m1.hdriftd_neg_one_iff`
at the origin, where `diagSum 0 = 0`. -/
theorem neg_one_gate {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (hd : (fun i => ((QMCLeafB.RelaxOracle.flatQ (-1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ))
        ⬝ᵥ ((0 : Fin (n * n) → ℝ)
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) ≤ 0) :
    ∑ i, ((Q i i : ℚ) : ℝ) ≤ 0 := by
  have h := (QMCLeafB.BTwins_M1.hdriftd_neg_one_iff (0 : Fin (n * n) → ℝ) Q).1 hd
  rwa [diagSum_zero n] at h

#print axioms QMCLeafB.OrientM1.neg_one_gate

/-- **The reversed body slot at round 0 puts the query centre above the whole body in trace.** -/
theorem neg_one_body_le {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hb : 0 ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q)) :
    ∑ i, X i i ≤ ∑ i, ((Q i i : ℚ) : ℝ) := by
  have h := hb
  rw [QMCLeafB.BTwins_M1.frob_neg_one_sub] at h
  linarith

#print axioms QMCLeafB.OrientM1.neg_one_body_le

/-- **THE REFUTATION (core).**  At any point whose relaxed body has a real point `X`
(`δ < 4`, `1 ≤ n` — the body's diagonal floor `1 − δ/4` is then positive), the two `dM = −1` slots
of the dilated producer at round `0` are contradictory: they force `tr X ≤ tr (cX 0) ≤ 0` while
`tr X ≥ n(1 − δ/4) > 0`.  No margin, multiplier, depth or stream choice enters. -/
theorem neg_one_dead {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    (hδ : δ < 4) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X)
    (Q : Matrix (Fin n) (Fin n) ℚ)
    (hd : (fun i => ((QMCLeafB.RelaxOracle.flatQ (-1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ))
        ⬝ᵥ ((0 : Fin (n * n) → ℝ)
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) ≤ 0)
    (hb : 0 ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q)) :
    False := by
  have h1 := neg_one_gate Q hd
  have h2 := neg_one_body_le Q X hb
  have h3 := trace_lower_of_body hX
  have h4 : (0 : ℝ) < (n : ℝ) * (1 - δ / 4) := trace_floor_pos hn hδ
  linarith

#print axioms QMCLeafB.OrientM1.neg_one_dead

end QMCLeafB.OrientM1

namespace QMCLeafB.OrientM1

open QuantumMaxCutEnergy

/-! ## 4.  The producer cannot be instantiated at `dM = −1`

`runParts_of_dilated_b`'s conclusion is `RunParts`, so its other slots are not needed to reach the
contradiction: the block below — the run's bit, the two drift slots and the horizon — is already
inconsistent.  A subset of a hypothesis list being unsatisfiable makes the whole list
unsatisfiable, so the producer has no instantiation at the reversed orientation.  The bit supplies
the last premise: `hverdict` plus `o G t = false` makes `ok 0 = false`
(`SimLoop.anyOk_eq_false_iff`), i.e. round `0` *is* a cut round — which is exactly the stratum's
situation (no pinched member ⇒ no `ok` round below the horizon). -/

/-- **No `dM = −1` run with a false bit at a nonempty real body.**  The hypotheses are
`runParts_of_dilated_b`'s at `dM := −1` restricted to the three slots the contradiction reads
(`hbody`, `hdriftd`, `hverdict`), plus the point's own data (false bit, nonempty horizon, nonempty
real body, `dq < 4`). -/
theorem neg_one_producer_inconsistent
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hbit : o G t = false)
    (hT : 1 ≤ P.K * P.m) (hdq4 : P.dq < 4)
    (hne : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE
        (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
        (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) (((P.dq : ℚ)) : ℝ) X)
    (ok : ℕ → Bool)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbody : ∀ k, k < P.K * P.m → ok k = false →
      ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE
          (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
          (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) (((P.dq : ℚ)) : ℝ) X →
        -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob
          (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin G.n) (Fin G.n) ℚ))
          (X - QMCLeafB.SepOracle.castMat (cX k)))
    (hdriftd : ∀ k, k < P.K * P.m → ok k = false →
      (fun i => ((QMCLeafB.RelaxOracle.flatQ
          (-1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    False := by
  have hany : QMCLeafB.SimLoop.anyOk ok (P.K * P.m) = false := by
    rw [← hverdict]
    exact hbit
  have hK : 0 < P.K * P.m := lt_of_lt_of_le Nat.zero_lt_one hT
  have hok0 : ok 0 = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff ok (P.K * P.m)).1 hany 0 hK
  obtain ⟨X, hX⟩ := hne
  refine neg_one_dead (n := G.n)
    (A := QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
    (u := ((t - QMCLeafB.RundataCert.eps G : ℚ) : ℝ)) (δ := ((P.dq : ℚ) : ℝ))
    (le_trans (by norm_num : (1 : ℕ) ≤ 2) hn) ?_ hX (cX 0) ?_ ?_
  · exact_mod_cast hdq4
  · exact hdriftd 0 hK hok0
  · have h := hbody 0 hK hok0 X hX
    simpa using h

#print axioms QMCLeafB.OrientM1.neg_one_producer_inconsistent

/-! ## 5.  The stratum's exemplar `(G₁, t₁)` passes those premises

`G₁` is the single-edge graph of weight `1` (`Rq = 2`), `t₁ = −2 + 71/1520000`; the rational sliver
point `Q₁ = !![1, −(1 + 3/3040000); −(1 + 3/3040000), 1]` is a member but no pinched matrix is
(`Check_emptybody_m5`).  The real body point used here is `Q₁` itself: exactly PSD up to the
`δ/2` margin (`λ_min = −3/3040000 ≥ −δ/2 = −4/3040000`), unit diagonal, and its objective sits
*exactly* on the level `u + δ/2` — which is why the sliver exists at all. -/

/-- The sliver's graph. -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- The sliver's rational body point. -/
abbrev Q₁ : Matrix (Fin 2) (Fin 2) ℚ := QMCLeafB.EmptyBodyM5.Q₁

/-- The sliver's tolerance. -/
theorem dq_G₁ : (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq = 1 / 380000 :=
  QMCLeafB.EmptyBodyM5.dq₁_eq

/-- The sliver's `ε`. -/
theorem eps_G₁ : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 :=
  QMCLeafB.EmptyBodyM5.eps_G₁

#print axioms QMCLeafB.OrientM1.dq_G₁
#print axioms QMCLeafB.OrientM1.eps_G₁

/-- `Q₁`'s real quadratic form clears the `δ/2` margin: `2·(1 + 3/3040000)·x₀x₁` is at most
`(2 + 1/760000)(x₀² + x₁²)`, i.e. `λ_min = −3/3040000 ≥ −1/760000`. -/
theorem qfR_Q₁_bound (x : Fin 2 → ℝ) :
    -((1 : ℝ) / 760000) * (∑ i : Fin 2, x i ^ 2)
      ≤ QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat Q₁) x := by
  have h1 : 2 * x 0 * x 1 ≤ x 0 ^ 2 + x 1 ^ 2 := by
    nlinarith [sq_nonneg (x 0 - x 1)]
  have h2 : (0 : ℝ) ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
  have h3 : (2 * (1 + 3 / 3040000) : ℝ) * (x 0 * x 1)
      ≤ (2 + 1 / 760000) * (x 0 ^ 2 + x 1 ^ 2) := by
    nlinarith [h1, h2]
  rw [QMCLeafB.BallFloor.qfR_eq_sum]
  simp [Q₁, QMCLeafB.SepOracle.castMat_apply, Fin.sum_univ_two]
  nlinarith [h1, h2, h3]

#print axioms QMCLeafB.OrientM1.qfR_Q₁_bound

/-- `Q₁`'s diagonal is exactly `1`. -/
theorem diag_G₁_Q₁ (i : Fin 2) :
    |QMCLeafB.SepOracle.castMat Q₁ i i - 1|
      ≤ (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) / 4 := by
  rw [dq_G₁]
  fin_cases i <;>
    · simp [QMCLeafB.SepOracle.castMat_apply, Q₁]
      norm_num

#print axioms QMCLeafB.OrientM1.diag_G₁_Q₁

/-- **The objective of `Q₁` sits exactly on the level**: `⟪A, Q₁⟫ = u + dq/2`.
(`relaxBodyLE`'s trace clause is `BallFloor.frob`, not `SepOracle.frob` — the two constants are the
same sum, but the statement below is the one the body predicate reads.) -/
theorem frob_G₁_Q₁ :
    QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G₁))
      (QMCLeafB.SepOracle.castMat Q₁) = -(2 + 3 / 1520000) := by
  simp [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, QMCLeafB.SepOracle.castMat_apply, Q₁,
    QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01,
    QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11]
  norm_num

#print axioms QMCLeafB.OrientM1.frob_G₁_Q₁

/-- **`Q₁` is a point of the real relaxed body at `(G₁, t₁)`** (same three clauses, at the
rational member itself). -/
theorem body_mem_G₁_Q₁ :
    QMCLeafB.BallFloor.relaxBodyLE
      (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G₁))
      (((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps G₁ : ℚ) : ℝ)
      (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) (QMCLeafB.SepOracle.castMat Q₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hq : (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) / 2 = 1 / 760000 := by
      rw [dq_G₁]
      norm_num
    rw [hq]
    exact qfR_Q₁_bound x
  · exact diag_G₁_Q₁
  · have hf := frob_G₁_Q₁
    have hu : (((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps G₁ : ℚ) : ℝ)
        + (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) / 2
        = -(2 + 3 / 1520000) := by
      rw [eps_G₁, dq_G₁]
      norm_num
    rw [hf]
    rw [hu]

#print axioms QMCLeafB.OrientM1.body_mem_G₁_Q₁

/-- **The real relaxed body at `(G₁, t₁)` is nonempty** — the stratum's defining property, at its
exemplar, in the exact shape `neg_one_producer_inconsistent` asks for. -/
theorem body_nonempty_G₁_real :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE
        (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G₁))
        (((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps G₁ : ℚ) : ℝ)
        (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) X :=
  ⟨QMCLeafB.SepOracle.castMat Q₁, body_mem_G₁_Q₁⟩

#print axioms QMCLeafB.OrientM1.body_nonempty_G₁_real

/-- The sliver's horizon is nonempty. -/
theorem one_le_K_mul_G₁ :
    1 ≤ (QMCLeafB.UnionShallow.paramsKbc2 G₁).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G₁).m := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K_mul_m]
  exact QMCLeafB.UnionShallow.one_le_Kbc2_mul G₁

#print axioms QMCLeafB.OrientM1.one_le_K_mul_G₁

/-- The sliver's tolerance clears `4` (so the body's diagonal floor `1 − dq/4` is positive). -/
theorem dq_G₁_lt_four : (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq < 4 := by
  rw [dq_G₁]
  norm_num

#print axioms QMCLeafB.OrientM1.dq_G₁_lt_four

/-- **The exemplar passes every premise of §4**: at `(G₁, t₁)` the reversed-orientation producer is
inconsistent for every bit reading `false` there — and the run's bit *is* false there, since no
pinched matrix is a member (`Check_emptybody_m5.no_pinched_member_G₁`). -/
theorem anchor3_neg_one_premises :
    (∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE
          (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G₁))
          (((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps G₁ : ℚ) : ℝ)
          (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) X)
      ∧ 1 ≤ (QMCLeafB.UnionShallow.paramsKbc2 G₁).K
            * (QMCLeafB.UnionShallow.paramsKbc2 G₁).m
      ∧ (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq < 4 :=
  ⟨body_nonempty_G₁_real, one_le_K_mul_G₁, dq_G₁_lt_four⟩

#print axioms QMCLeafB.OrientM1.anchor3_neg_one_premises


/-! ## 6.  The price of the one escape hatch: a `β > 0` dilation is not free

`RunPartsDilate.dilCut` puts `β := 0` (`RelaxCut.dilate`'s margin stays the oracle's).  The general
`RelaxCut.dilate` allows `β > 0`, which *weakens* the body slot to
`frob dM (X − cX) ≥ −β` and *raises* the cut's margin to `marg + λβ`.  For the reversed direction
this weakens the round-0 gate from `tr X ≤ tr (cX 0)` to `tr X ≤ β + tr (cX 0)`, and since
`tr (cX 0) ≤ 0` the price is exact: **`β ≥ tr X ≥ n(1 − δ/4)` for every body point**.  At the
exemplar that is `β ≥ 2 − 1/760000`, i.e. `β` of the order of `n` — a quantity the depth ledger
`del² ≤ rho²·σ`, `rho ≤ rmax` has to pay for through the `λβ` margin.  So a reversal with `β > 0`
is not the shelf's producer and is not free; pricing it is the algorithmic lane's call, and this
section only fixes the floor it cannot go below. -/

/-- **A `β > 0` reversal must pay `β ≥ n(1 − δ/4)`.**  With the body slot relaxed to `−β`, the two
round-0 slots force `tr X − tr (cX 0) ≤ β` with `tr (cX 0) ≤ 0`, hence the body's trace floor bounds
`β` from below. -/
theorem neg_one_beta_price {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ β : ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X)
    (Q : Matrix (Fin n) (Fin n) ℚ)
    (hd : (fun i => ((QMCLeafB.RelaxOracle.flatQ (-1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ))
        ⬝ᵥ ((0 : Fin (n * n) → ℝ)
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) ≤ 0)
    (hb : -β ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q)) :
    (n : ℝ) * (1 - δ / 4) ≤ β := by
  have h1 := neg_one_gate Q hd
  have h2 := hb
  rw [QMCLeafB.BTwins_M1.frob_neg_one_sub] at h2
  have h3 := trace_lower_of_body hX
  linarith

#print axioms QMCLeafB.OrientM1.neg_one_beta_price

/-- **The price at the exemplar**: `β ≥ 2 − 1/760000` at `(G₁, t₁)`, for any query centre. -/
theorem beta_price_G₁ (β : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℚ)
    (hd : (fun i => ((QMCLeafB.RelaxOracle.flatQ (-1 : Matrix (Fin 2) (Fin 2) ℚ) i : ℚ) : ℝ))
        ⬝ᵥ ((0 : Fin (2 * 2) → ℝ)
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) ≤ 0)
    (hb : -β ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin 2) (Fin 2) ℚ))
      (QMCLeafB.SepOracle.castMat Q₁ - QMCLeafB.SepOracle.castMat Q)) :
    2 - (1 : ℝ) / 760000 ≤ β := by
  have h := neg_one_beta_price (n := 2) body_mem_G₁_Q₁ Q hd hb
  rw [dq_G₁] at h
  norm_num at h
  linarith

#print axioms QMCLeafB.OrientM1.beta_price_G₁

end QMCLeafB.OrientM1


