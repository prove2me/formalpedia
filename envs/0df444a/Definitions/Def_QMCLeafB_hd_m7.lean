-- Prove2me | Definitions.Def_QMCLeafB_hd_m7
-- name    : QMCLeafB_hd_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:51:44.788522+00:00
-- url     : https://prove2.me/theorems/2751f258-1f1d-4a83-a465-ab5dc92cb353
-- title:
--   QMCLeafB hd_m7
-- statement:
--   # leaf B phase 30 — `hd` (template input 5): the bit-keyed two-class family, member m7
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_refuted_m3
import Definitions.Def_QMCLeafB_oklevel
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 30 — `hd` (template input 5): the bit-keyed two-class family, member m7

`SubM1.solution` consumes exactly one `hd`:

    ∀ (G t), 2 ≤ G.n → -Rq G ≤ t → (t:ℝ) < -(Rq G/40000) →
      RunParts (loopBit init round verdict Tbc2) G t (paramsKbc2 G)

This file reduces that obligation **at the program's own bit** to two class productions, one per
value of the bit, and machine-checks both class constructions.  Nothing here analyses
`RunParts.hcut`'s transcript pairing against `Cat k`: on the `false` side the recorded body is empty,
so `hcut` is vacuous; on the `true` side no cut is ever recorded (`ok ≡ true`).

* §1 `anyOk` at an all-`true` stream.
* §2 **the witness class**: ONE real unit-diagonal PSD point at the leaf's own level `t + Rq/40000`
  yields the all-`ok` record.  No `RelaxMem`, no drift, no pinch, no separation, no diagonal
  normalisation — `hcert`'s existential is served by the same point at every round.
* §3 **the empty class** (banked, re-exported at the template's family): `RefutedM3.runParts_of_emptyBody`.
* §4 `hd_of_bit_classes` — the family: `hd` follows from
  (W) bit `true` ⇒ a witness exists at `t + Rq/40000`, and
  (E) bit `false` ⇒ the relaxed body at the engine's level is empty.
  The split is exhaustive by `Bool` case analysis, so (W)+(E) is exactly `hd`.
* §5 the same at `SubM1`'s verbatim `hd` (with the template's `Tbc2`).
* §6 **non-vacuity**: at the phase-21 anchor `(G₀, t₀)` both classes are inhabited — a witness
  exists (`!![1,-1;-1,1]`, trace `-1`) and the body is empty — so neither lane of §4 is a vacuous
  hypothesis, and `hd` is inhabited at a genuine interior point for both constant bits.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.HdM7

open QuantumMaxCutEnergy

/-! ## 1.  `anyOk` on an all-`true` stream -/

theorem anyOk_true_fun (T : ℕ) (hT : 0 < T) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) T = true := by
  cases T with
  | zero => exact absurd hT (lt_irrefl 0)
  | succ k => rfl

#print axioms QMCLeafB.HdM7.anyOk_true_fun

theorem okTrue_ne_false (k : ℕ) : (fun _ : ℕ => true) k ≠ false := by simp

#print axioms QMCLeafB.HdM7.okTrue_ne_false

/-! ## 2.  The witness class: one real point at the leaf's level serves every round -/

/-- **The `true`-bit record.**  If the program's bit reads `true` at `(G,t)` and there is a real
unit-diagonal PSD point whose objective at the weight matrix is at most the leaf's own level
`t + Rq G/40000`, then the whole `RunParts` bundle exists at that bit: no round ever records a cut,
so the witness, the depth ledger, the separation contract and the transcript pairing are all
untouched.  `hcert`'s existential is discharged by the same point at every round below the horizon.
-/
noncomputable def runParts_okStream
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hKm : 0 < P.K * P.m)
    (hbit : o G t = true)
    (hW : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.FinalStroke.RunParts o G t P where
  ok := fun _ => true
  cd := fun _ => ⟨fun _ => 0, fun _ => 0, 0⟩
  del := fun _ => 0
  hcert := by
    intro k _hk _hok
    exact hW
  hwit := by
    intro k _hk hok
    exact absurd hok (okTrue_ne_false k)
  hrho := by
    intro k _hk hok
    exact absurd hok (okTrue_ne_false k)
  hcne := by
    intro k _hk hok
    exact absurd hok (okTrue_ne_false k)
  hdel0 := by
    intro k _hk hok
    exact absurd hok (okTrue_ne_false k)
  hcheck := by
    intro k _hk hok
    exact absurd hok (okTrue_ne_false k)
  hle := by
    intro k _hk hok
    exact absurd hok (okTrue_ne_false k)
  hcut := by
    intro k _hk hok
    exact absurd hok (okTrue_ne_false k)
  hverdict := by
    rw [hbit, anyOk_true_fun _ hKm]

#print axioms QMCLeafB.HdM7.runParts_okStream

/-! ## 3.  The empty class, at the template's family (banked)

`RefutedM3.runParts_of_emptyBody` is the all-`cut` record at an empty relaxed body: the depth ledger
is the shelf's `runCut`/`sigmaQ` positivity, the margins are `0`, and `hcut` is vacuous because the
ball it must separate is empty (`RefutedM3.not_relaxBall_of_emptyBody`).  It carries **no**
parameter side condition.  Re-exported here at `paramsKbc2` so that the family's two lanes live in
one namespace. -/

/-- **The `false`-bit record** at the campaign's parameter family. -/
noncomputable def runParts_botStream
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hbit : o G t = false)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  QMCLeafB.RefutedM3.runParts_of_emptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn hbit hempty

#print axioms QMCLeafB.HdM7.runParts_botStream

/-! ## 4.  The family: `hd` from the two bit-keyed class productions

The split is by the value of the program's own bit at `(G,t)`, so it is exhaustive with no
geometric side condition left over.  Both lanes conclude at the same `o` — the record's `ok` stream
is `fun _ => true` on the upper lane and `fun _ => false` on the lower one, and `hverdict` is the
bit equation in each case. -/

/-- **`hd` at a generic bit, from the two class productions.**

* `hW` (the *witness* class): where the bit reads `true`, a real unit-diagonal PSD point at the
  leaf's level `t + Rq/40000` exists.  Nothing else is asked — in particular not a `RelaxMem`
  certificate, not a pinned diagonal, not a depth ledger.
* `hE` (the *empty* class): where the bit reads `false`, the engine's relaxed body at level
  `t - Rq/40000` and tolerance `dqShallow G` is empty.  This is the only place genuine separation
  would be needed, and emptiness removes it. -/
noncomputable def hd_of_bit_classes (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hW : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace
            ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hE : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = false →
      ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  cases hbit : o G t with
  | true =>
      exact runParts_okStream o G t (QMCLeafB.UnionShallow.paramsKbc2 G)
        (by
          rw [QMCLeafB.UnionShallow.paramsKbc2_K_mul_m]
          exact lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul G))
        hbit (hW G t hn hlo hhi hbit)
  | false =>
      exact runParts_botStream o G t hn hbit (hE G t hn hlo hhi hbit)

#print axioms QMCLeafB.HdM7.hd_of_bit_classes

/-! ## 5.  The template's verbatim `hd`

`Solutions/solution_m1.lean` states `hd` with the round count `Tbc2` and the family `paramsKbc2`.
`loopBit` takes the program as an opaque triple, so §4 is already the whole of `hd`; the wrapper
below is only there so that the shape a consumer sees is the template's, character for character. -/

/-- The campaign's round count, at the campaign factor (as in `solution_m1`). -/
abbrev Tbc2 : QuantumMaxCutEnergy.Input → ℚ → ℕ :=
  fun G' _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
    * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)

/-- **`hd` for `SubM1.solution`'s program form**, from the two bit-keyed classes. -/
noncomputable def hd_loopBit {σ : Type} [OAI.MetricKMedian.Binary.Automatic.Coding σ]
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hW : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace
            ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hE : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  hd_of_bit_classes _ hW hE

#print axioms QMCLeafB.HdM7.hd_loopBit

/-! ## 6.  Non-vacuity: both lanes are inhabited at interior points, and they are exclusive

The class split of §4 is not a vacuous division:

* at `(G₀, t₀)` (`two vertices, one edge of weight 1/2`, `t₀ = -99999/100000`) the relaxed body at
  the engine's level is **empty**, so the `false` lane is available — and it is the *only* lane
  then, since an empty body cannot contain an ok certificate (`hcert` would exhibit a body point at
  the leaf's level, which is above the engine's);
* at `(G₁, t₁)` (`two vertices, one edge of weight 1`, `t₁ = -2 + 71/1520000`) the relaxed body is
  **nonempty** (`EmptyBodyM5.body_nonempty_G₁`), so the `false` lane owes genuine separation there,
  while the `true` lane is available outright: `!![1,-1;-1,1]` is a unit-diagonal PSD point at the
  leaf's level `t₁ + Rq/40000`.

So the residual of §4 is exactly the pair `{bit true ∧ no witness}` and `{bit false ∧ body
nonempty}`; the second is the campaign's thin band, the first is the flag-soundness direction. -/

theorem paramsKbc2_K_mul_m_pos (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K_mul_m]
  exact lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul G)

#print axioms QMCLeafB.HdM7.paramsKbc2_K_mul_m_pos

/-- The `false` lane at the phase-21/22 anchor `(G₀, t₀)`, at the campaign's family. -/
noncomputable def runParts_false_G₀ :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => false)
      QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  runParts_botStream (fun _ _ => false) QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀
    (by decide) rfl (fun X => QMCLeafB.RefutedM3.body_empty_G₀ X)

#print axioms QMCLeafB.HdM7.runParts_false_G₀

/-- The anchor is an interior point of the template's bracket. -/
theorem interior_G₀ :
    -QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ ≤ QMCLeafB.EmptyBodyM5.t₀ ∧
      (QMCLeafB.EmptyBodyM5.t₀ : ℝ)
        < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ) :=
  QMCLeafB.EmptyBodyM5.t₀_mem_bracket

#print axioms QMCLeafB.HdM7.interior_G₀

/-- The `true` lane at the sliver `(G₁, t₁)`, at the campaign's family: one witness, no cuts. -/
noncomputable def runParts_true_G₁ :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => true)
      QMCLeafB.EmptyBodyM5.G₁ ((-(2 : ℚ) + 71 / 1520000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) :=
  runParts_okStream (fun _ _ => true) QMCLeafB.EmptyBodyM5.G₁ ((-(2 : ℚ) + 71 / 1520000))
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁)
    (paramsKbc2_K_mul_m_pos _) rfl
    (QMCLeafB.OkLevelM5.hcert_G₁_of_threshold (t := (-(2 : ℚ) + 71 / 1520000)) (by
      rw [QMCLeafB.EmptyBodyM5.Rq_G₁]; norm_num))

#print axioms QMCLeafB.HdM7.runParts_true_G₁

/-- The sliver is an interior point of the template's bracket. -/
theorem interior_G₁ :
    -QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ ≤ (-(2 : ℚ) + 71 / 1520000) ∧
      ((-(2 : ℚ) + 71 / 1520000 : ℚ) : ℝ)
        < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ)) : ℝ) :=
  QMCLeafB.EmptyBodyM5.t₁_mem_bracket

#print axioms QMCLeafB.HdM7.interior_G₁

/-- The body at the same sliver point is **nonempty**, so the `false` lane is not for free there. -/
theorem body_nonempty_G₁ :
    ∃ X : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) X
        ((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq :=
  ⟨QMCLeafB.EmptyBodyM5.Q₁, QMCLeafB.EmptyBodyM5.body_nonempty_G₁⟩

#print axioms QMCLeafB.HdM7.body_nonempty_G₁

/-! ## 7.  What the two classes really are

§2 and §4 are sharp, not merely sufficient:

* **`nonempty_runParts_true_iff`**: at *any* `(G,t)` and any parameter family with a nonempty
  horizon, the constant-`true` bit admits a `RunParts` **iff** a real unit-diagonal PSD point at the
  leaf's level `t + Rq/40000` exists.  So the whole `RunParts` bundle at a `true` bit is a purely
  geometric lower-bound statement — engine, drift ledger, pinch and transcript pairing are all
  absent from it.  (Forwards: `hverdict` + `anyOk`'s `∃`-form names an ok round, whose `hcert` is
  the point.  Backwards: §2.)
* **`body_empty_of_le`**: emptiness at one threshold propagates *down* in `t`, so the empty stratum
  is an interval, not a point.

The residual of §4 is therefore exactly
`{bit true ∧ no witness}` ∪ `{bit false ∧ body nonempty}`:
the first is the flag-soundness direction of the program, the second is the campaign's thin band. -/

/-- `relaxBodyLE` is monotone in the threshold. -/
theorem relaxBodyLE_mono_u {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u u' δ : ℝ}
    (h : u ≤ u') {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    QMCLeafB.BallFloor.relaxBodyLE A u' δ X :=
  ⟨hX.1, hX.2.1, le_trans hX.2.2 (by linarith)⟩

#print axioms QMCLeafB.HdM7.relaxBodyLE_mono_u

/-- **The all-`true` bit's `hd` is exactly the witness condition.** -/
theorem nonempty_runParts_true_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hKm : 0 < P.K * P.m) :
    Nonempty (QMCLeafB.FinalStroke.RunParts (fun _ _ => true) G t P) ↔
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace
            ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  constructor
  · rintro ⟨B⟩
    have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = true := by
      rw [← B.hverdict]
    obtain ⟨k, hk, hok⟩ :=
      (QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (P.K * P.m)).mp hany
    exact B.hcert k hk hok
  · rintro hW
    exact ⟨runParts_okStream (fun _ _ => true) G t P hKm rfl hW⟩

#print axioms QMCLeafB.HdM7.nonempty_runParts_true_iff

/-! ### The empty stratum is an interval -/

/-- The body is empty below the anchor `t₀` at `G₀` as well. -/
theorem body_empty_G₀_of_le {t : ℚ} (ht : t ≤ QMCLeafB.EmptyBodyM5.t₀)
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ))
      (((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq : ℚ) : ℝ) X := by
  intro hbody
  refine QMCLeafB.RefutedM3.body_empty_G₀ X ?_
  refine relaxBodyLE_mono_u ?_ hbody
  have h : (t : ℝ) ≤ (QMCLeafB.EmptyBodyM5.t₀ : ℝ) := by exact_mod_cast ht
  exact sub_le_sub_right h _

#print axioms QMCLeafB.HdM7.body_empty_G₀_of_le

/-- **The `false` lane at `G₀` on the whole bottom interval** `t ≤ t₀`, at the campaign's family. -/
noncomputable def runParts_false_G₀_of_le (t : ℚ) (ht : t ≤ QMCLeafB.EmptyBodyM5.t₀) :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => false)
      QMCLeafB.ResidRefute.G₀ t
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  runParts_botStream (fun _ _ => false) QMCLeafB.ResidRefute.G₀ t (by decide) rfl
    (fun X => body_empty_G₀_of_le ht X)

#print axioms QMCLeafB.HdM7.runParts_false_G₀_of_le

/-! ### The `true` lane covers the whole bracket at `G₁`

At `G₁` (two vertices, one edge of weight `1`, `Rq = 2`) the SDP body reaches down to `-Rq`, so
`!![1,-1;-1,1]` is a witness at *every* threshold of the interior bracket
(`OkLevelM5.hcert_G₁_of_threshold`).  Hence `hd` at the constant-`true` bit holds on the entire
bracket at that input: the template's `hd` slot is inhabited pointwise on a real input, at a real
bit, and not by an empty-`ok` trick.  (`G₁` is also the input where the body is nonempty but no
*pinched* matrix is a member, so the `false` lane is *not* free there — §6.) -/

/-- **`hd` at the constant-`true` bit at `G₁`, on the whole interior bracket.** -/
noncomputable def runParts_true_G₁_of (t : ℚ)
    (hlo : -QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ ≤ t) :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => true)
      QMCLeafB.EmptyBodyM5.G₁ t
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) :=
  runParts_okStream (fun _ _ => true) QMCLeafB.EmptyBodyM5.G₁ t
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁)
    (paramsKbc2_K_mul_m_pos _) rfl
    (QMCLeafB.OkLevelM5.hcert_G₁_of_threshold (t := t) (by
      rw [QMCLeafB.EmptyBodyM5.Rq_G₁] at hlo ⊢; linarith))

#print axioms QMCLeafB.HdM7.runParts_true_G₁_of

/-! ## 8.  The top slice: free, by the identity witness

The leaf's slack is `Rq G/40000`, and `tr (wMatrix G · 1) = Σᵢ wMatrix G i i = 0` (the weight matrix
has zero diagonal).  So `X = 1` is a unit-diagonal PSD point at the leaf's level **exactly on the top
slice** `t ≥ -Rq G/40000` — the region `htop` speaks about:

* `hd` at the constant-`true` bit is free there (no round ever cuts, `hcert` is the identity);
* `htop` asks precisely that the program's bit read `true` there.

So inputs (4) and (5) of the submission template are *consistent* on the top slice, and that region
costs no separation content at all.  The whole content of `hd` is the interior `-Rq G ≤ t < -Rq G/40000`. -/

theorem trace_wMatrix_zero (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.wMatrix G).trace = 0 := by
  rw [Matrix.trace]
  exact Finset.sum_eq_zero fun i _ => QMCLeafB.wMatrix_apply_of_eq

#print axioms QMCLeafB.HdM7.trace_wMatrix_zero

theorem isUnitDiagPSD_one (n : ℕ) :
    QMCLeafB.AnswerProducer.IsUnitDiagPSD (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨Matrix.PosSemidef.one, fun i => by simp⟩

#print axioms QMCLeafB.HdM7.isUnitDiagPSD_one

/-- The identity is a witness at the leaf's level as soon as the level is nonnegative. -/
theorem witness_one (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (h : 0 ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  refine ⟨1, isUnitDiagPSD_one _, ?_⟩
  rw [Matrix.mul_one, trace_wMatrix_zero]
  linarith

#print axioms QMCLeafB.HdM7.witness_one

/-- **`hd` at the constant-`true` bit on the whole top slice** — the region where `htop` demands the
bit be `true`.  No hypothesis on `G.n`, `Rq`, or the bracket's floor. -/
noncomputable def runParts_true_topSlice (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => true) G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  runParts_okStream (fun _ _ => true) G t (QMCLeafB.UnionShallow.paramsKbc2 G)
    (paramsKbc2_K_mul_m_pos G) rfl (witness_one G t (by linarith))

#print axioms QMCLeafB.HdM7.runParts_true_topSlice

end QMCLeafB.HdM7


