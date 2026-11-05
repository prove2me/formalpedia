-- Prove2me | Definitions.Def_QMCLeafB_solution_m1
-- name    : QMCLeafB_solution_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:47:30.736822+00:00
-- url     : https://prove2.me/theorems/844eeadd-cab8-451f-a4fd-e594b504c7fd
-- title:
--   QMCLeafB solution_m1
-- statement:
--   # `solution_m1` — the submission file (phase 29, member m1, direction `submission-file`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_audit25
/-
# `solution_m1` — the submission file (phase 29, member m1, direction `submission-file`)

The leaf's verbatim `d9f601e5` sentence, from the **published** stroke, importing nothing of this
campaign's working tree.

* Imports: `Mathlib`, `Definitions.Def_QMCLeafB_unionShallow`, `Definitions.Def_QMCLeafB_audit25`.
  Both bundles are live (`packaging/STATE.json`: `Check_union_shallow_m5 -> QMCLeafB_unionShallow`,
  `Check_audit25_m8 -> QMCLeafB_audit25`).  Nothing from `Solutions.*`; in particular the two
  unpublished modules of the phase-28 chain (`QMCLeafB_traj_m3`, `QMCLeafB_fal28`) are **not**
  needed — `TestRun` does not have to appear in a submission at all.
* `SubM1.solution` is the sentence written out; `SubM1.solution_lock` is `Audit25M8.Target`, the
  campaign's own name for it (the ascription typechecks, so the lock is definitional).
* Both fire `UnionShallow.solution_union_shallow_final`, whose leaf-side input is exactly one
  `RunParts` per interior point at the program's **own** loop bit.  `campaignBit` appears nowhere:
  the phase-29 spec's family at `campaignBit` is empty (`gate_m1.lean`), so the stroke is re-keyed.

Residual (all of it, nothing hidden): the repaired program `(init, round, verdict)` with its three
`Poly` slots, its size ledger `(M, C₀, c, kr, hMinv, hstep, hM)`, `hinitTape`, `htop` on the top
slice, and `hd` — `RunParts` at every interior point.  Note `RunParts.hcert` asks for a genuine
unit-diagonal PSD point at `t + Rq/40000`, so the spec's rational-member soundness `hsound` is *not*
part of this residual.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` receipts at the end (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace SubM1

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding (the campaign's local instance, re-declared: the library's is `local`). -/
local instance instRequestCodingSub : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 2.  The submission file -/

/-- The campaign's round count, at the campaign factor. -/
abbrev Tbc2 : QuantumMaxCutEnergy.Input → ℚ → ℕ :=
  fun G' _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
    * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)

/-- **The submission file's theorem: `d9f601e5`, verbatim, from the live stroke.**

Residual hypotheses, and nothing else:
* the repaired program `(init, round, verdict)` and its three `Poly` slots;
* its one-step size ledger `(hMinv, hstep, hM)`, `1 ≤ kr`, and tape-freeness of `init`;
* `htop`: the bit reads `true` on the top slice;
* `hd`: ONE `RunParts` per interior `(G,t)`, at the program's **own** loop bit (`campaignBit` is
  nowhere in this statement — that is the re-keying). -/
theorem solution {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
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
  QMCLeafB.UnionShallow.solution_union_shallow_final k hk init round verdict
    hinit hr hv M C₀ c kr hkr hMinv hstep hM hinitTape htop hd

#print axioms SubM1.solution

/-- **Statement lock**: the same sentence written as `Audit25M8.Target`, definitionally. -/
theorem solution_lock {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.Audit25M8.Target :=
  solution k hk init round verdict hinit hr hv M C₀ c kr hkr hMinv hstep hM hinitTape htop hd

#print axioms SubM1.solution_lock

end SubM1


