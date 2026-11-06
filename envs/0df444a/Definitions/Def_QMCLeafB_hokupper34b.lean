-- Prove2me | Definitions.Def_QMCLeafB_hokupper34b
-- name    : QMCLeafB_hokupper34b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:15:10.266464+00:00
-- url     : https://prove2.me/theorems/ba3e6b12-fbda-479e-b549-a2181c93c3db
-- title:
--   QMCLeafB hokupper34b
-- statement:
--   # `Check_hokupper34b_m8` — phase 34, member m8, direction d9 `upper-side` (integration receipt)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_hokupper34
import Definitions.Def_QMCLeafB_pbit33
/-
# `Check_hokupper34b_m8` — phase 34, member m8, direction d9 `upper-side` (integration receipt)

`Check_hokupper34_m8` proves the upper side in published-`Definitions`-only form:
the released gate at an `ok` round yields `HokShape G t` — the *verbatim* conclusion of `hok`
(`∃ cX, cXᵀ = cX ∧ RelaxMem (wMatrixQ G) cX (t − eps G) (dqShallow G)`).

This file is the receipt that it **plugs into the banked chain with no adaptation**:

* `hd33_of_hokShape` — `Pbit33.Hd33` from {upper side in `HokShape` form, `hfalse`}, i.e. the banked
  `Pbit33.Hd33_of_relaxMem` with its `∃ cX` shape recognised as `HokShape`;
* `solution33_of_hokShape` / `solution_of_hokShape` — the leaf as `FinishLine.SolutionStatement`
  and as the verbatim `d9f601e5` sentence (through `Pbit33.solution33`/`solution33_statement`,
  whose `Automatic.Poly` bit `ho33` and count `hKm33` are already proved there);
* `solution33_of_releasedGate` — the whole leaf from the *released gate's own data* along a stream
  whose `anyOk` read-out is the campaign bit, plus `hfalse`.  The only link left on the upper side
  is the bit-agreement `hbit`; no `RelaxMem`, no member certificate, no level/tolerance work remains.

Cone: this file imports `Solutions.Check_pbit33_m6` (and hence the published `Definitions` cone), so
it is a *campaign* file.  The submission frame (`Check_sub34_*.lean`) must take the kernel
`Check_hokupper34_m8` plus the banked `Pbit33` route, both published-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace HokUpper34M8

open QuantumMaxCutEnergy

/-! ## 1.  `HokShape` is the `hok` slot of the banked split -/

/-- **`Pbit33.Hd33` from the upper side in `HokShape` form.**  `Pbit33.Hd33_of_relaxMem`'s `hok`
argument is literally `HokShape`, so this is an application, not a re-derivation: the phase-33
upper-side slot is now a *proved* implication from the released gate's state data. -/
noncomputable def hd33_of_hokShape
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true → HokShape G t)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = false →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Pbit33.o33 G t (QMCLeafB.Pbit33.P33 G)) :
    QMCLeafB.Pbit33.Hd33 :=
  QMCLeafB.Pbit33.Hd33_of_relaxMem hok hfalse

#print axioms HokUpper34M8.hd33_of_hokShape

/-- **The leaf from `{upper side, hfalse}`** — `FinishLine.SolutionStatement`; the `Poly` bit and the
count are `Pbit33.ho33`/`Pbit33.hKm33`, already proved. -/
theorem solution33_of_hokShape (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true → HokShape G t)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = false →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Pbit33.o33 G t (QMCLeafB.Pbit33.P33 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Pbit33.solution33 k hk (hd33_of_hokShape hok hfalse)

#print axioms HokUpper34M8.solution33_of_hokShape

/-- **The leaf in the verbatim `d9f601e5` type** from `{upper side, hfalse}`. -/
theorem solution_of_hokShape (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = true → HokShape G t)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = false →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Pbit33.o33 G t (QMCLeafB.Pbit33.P33 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.Pbit33.solution33_statement k hk (hd33_of_hokShape hok hfalse)

#print axioms HokUpper34M8.solution_of_hokShape

/-! ## 2.  The leaf from the released gate's own data -/

/-- **The whole leaf, from the released gate and `hfalse`.**  The `ok` test of the stream is
arbitrary (`okT`); all that is required of it is (i) its `anyOk` read-out *is* the campaign bit
`o33` (`hbit` — the one remaining link, and a definitional one for any programme whose flag stream
is `o33`'s) and (ii) the gate data of `Check_hokupper34_m8`'s §4 at every `ok`-reporting round.  The
member, the level transport, the symmetry and the pinch are then supplied by the kernel. -/
theorem solution33_of_releasedGate (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (okT : QMCLeafB.RoundProgram.RSt → Bool)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Pbit33.o33 G t = QMCLeafB.SimLoop.anyOk (fun j => okT (σ G t j)) (T G))
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdat : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okT (σ G t j) = true →
      QMCLeafB.RoundProgram.stN (σ G t j) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ G t j)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ G t j)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ G t j))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j', QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t j)) i j'
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t j)) j' i))
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okT (σ G t j) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (σ G t j)), acc)).1 = false)
    (hdv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okT (σ G t j) = true →
      QMCLeafB.RoundProgram.dvR (σ G t j) ≤ QMCLeafB.RundataParams.dqShallow G / 4)
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okT (σ G t j) = true →
      QMCLeafB.RoundProgram.fvR (σ G t j)
        ≤ QMCLeafB.RoundProgram.stT (σ G t j) - QMCLeafB.RoundT.epsOf (σ G t j)
          + QMCLeafB.OkLower.dqOf (σ G t j) / 2)
    (hlev : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okT (σ G t j) = true →
      QMCLeafB.RoundProgram.stT (σ G t j) - QMCLeafB.RoundT.epsOf (σ G t j)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okT (σ G t j) = true →
      QMCLeafB.OkLower.dqOf (σ G t j) = QMCLeafB.RundataParams.dqShallow G)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = false →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Pbit33.o33 G t (QMCLeafB.Pbit33.P33 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution33_of_hokShape k hk
    (fun G t _ _ _ hb =>
      hokShape_of_releasedGate (hRq G) (hbit G t) hb
        (fun j hj hok => hdat G t j hj hok) (fun j hj hok => hpiv G t j hj hok)
        (fun j hj hok => hdv G t j hj hok) (fun j hj hok => hfv G t j hj hok)
        (fun j hj hok => hlev G t j hj hok) (fun j hj hok => hdqv G t j hj hok))
    hfalse

#print axioms HokUpper34M8.solution33_of_releasedGate


/-! ## 3.  The consumer side, and the level the released test has to read -/

/-- **`HokShape` is exactly what the witness class `hcert` wants.**  `Asm2M8.memberAt_of_relaxMem`
consumes `hok` verbatim: a symmetric rational `RelaxMem` at `(t − eps G, dqShallow G)` is a genuine
unit-diagonal PSD point at `t + Rq/40000`.  So the released gate's member feeds `RunParts.hcert`
with no further work — the "consumer side is done" of the phase-33 note, machine-checked. -/
theorem memberAt_of_hokShape {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hn : 2 ≤ G.n) (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (h : HokShape G t) : AsmM8.MemberAt G t :=
  Asm2M8.memberAt_of_relaxMem (G := G) (t := t) hn ⟨hlo, hlt⟩ h

#print axioms HokUpper34M8.memberAt_of_hokShape

/-- **The upper and lower levels are separated by more than the tolerance.**  At every positive
weight input the campaign's tolerance is at most a ninth of `eps` (`dqShallow = eps/(9Rq+1)`), so

    (t − eps) + dqShallow/2  <  t + eps

with room to spare.  Consequence for the release: an `ok` test that fires on the *upper* event
`frob ≤ t + eps` (the campaign `roundGT` flag's feasibility branch) is **not** sound for the lower
relaxed body at `t − eps`, whose trace bound is `(t − eps) + dq/2`; the released test must read the
lower level.  This is the machine-checked reason the upper side cannot be obtained from `o33`'s
feasibility branch alone. -/
theorem dqShallow_half_lt_two_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G / 2 < 2 * QMCLeafB.RundataCert.eps G := by
  have heps : 0 < QMCLeafB.RundataCert.eps G :=
    QMCLeafB.RundataCert.eps_pos G hRq
  rw [QMCLeafB.RundataParams.dqShallow, if_neg (ne_of_gt hRq),
    QMCLeafB.RundataParams.dqShallowCore, QMCLeafB.RundataCert.eps, div_div]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hRq, heps]

#print axioms HokUpper34M8.dqShallow_half_lt_two_eps

/-- The separation in the form the `ok` tests are written: the lower relaxed level is strictly below
the upper feasibility level, by more than the tolerance. -/
theorem lower_trace_bound_lt_upper (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (t - QMCLeafB.RundataCert.eps G) + QMCLeafB.RundataParams.dqShallow G / 2
      < t + QMCLeafB.RundataCert.eps G := by
  have h := dqShallow_half_lt_two_eps G hRq
  linarith

#print axioms HokUpper34M8.lower_trace_bound_lt_upper


/-! ## 4.  The leaf from the CONCRETE released test -/

/-- **The whole leaf from the compiled released test (`okRel`: certified exact run + `dvR ≤ dqOf/4`
+ exact pivot + lower-body trace) and `hfalse`.**  The stream is arbitrary; the only link on the
upper side is the bit agreement `hbit`, and the only other hypothesis is the stream's state
coherence (`hdat`, `hlev`, `hdqv`) — the orbit invariants a released programme must carry. -/
theorem solution33_of_okRelStream (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Pbit33.o33 G t = QMCLeafB.SimLoop.anyOk (fun j => okRel (σ G t j)) (T G))
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdat : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okRel (σ G t j) = true →
      QMCLeafB.RoundProgram.stN (σ G t j) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ G t j)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ G t j)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ G t j))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j', QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t j)) i j'
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t j)) j' i))
    (hlev : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okRel (σ G t j) = true →
      QMCLeafB.RoundProgram.stT (σ G t j) - QMCLeafB.RoundT.epsOf (σ G t j)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (j : ℕ), j < T G →
      okRel (σ G t j) = true →
      QMCLeafB.OkLower.dqOf (σ G t j) = QMCLeafB.RundataParams.dqShallow G)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.Pbit33.o33 G t = false →
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Pbit33.o33 G t (QMCLeafB.Pbit33.P33 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution33_of_hokShape k hk
    (fun G t _ _ _ hb =>
      exists_relaxMem_of_okRelStream (hbit G t) hb
        (fun j hj hok => hdat G t j hj hok) (fun j hj hok => hlev G t j hj hok)
        (fun j hj hok => hdqv G t j hj hok) (hRq G))
    hfalse

#print axioms HokUpper34M8.solution33_of_okRelStream

end HokUpper34M8


