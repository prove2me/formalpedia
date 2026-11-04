-- Prove2me | Definitions.Def_QMCLeafB_hspec_assembly_m4
-- name    : QMCLeafB_hspec_assembly_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:48:35.441741+00:00
-- url     : https://prove2.me/theorems/505a094a-ae1b-43db-8d29-3077a9e43cad
-- title:
--   QMCLeafB hspec_assembly_m4
-- statement:
--   # leaf B phase 13 — brick `hspec-assembly` (swarm `smw17fqzz`, member m4, direction d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_hspec_m4
import Definitions.Def_QMCLeafB_brick_init_verdict_m8
/-
# leaf B phase 13 — brick `hspec-assembly` (swarm `smw17fqzz`, member m4, direction d7)

`Check_hspec_m4` proves `hspec` and pins `o`.  This file *applies* that at the pinned `σ`
(`QMCLeafB.InitVerdict.St`, m8's driver) and at the pinned stroke (`VerdictSound.solution_of_loop_via_runData`,
via m7's `FinalStroke.loopBit`), so that the residual of the endgame is explicit and small.

The point of the exercise is the **overshoot route** (§3g of `Check_hspec_m4`): `hspec` does not need
the fuel's length to equal the round count.  It needs

  (a) `Poly fuel` — any fuel, e.g. the untruncated `Fuel.fuel k`, whose length `L^(2^k)` is
      tape-dependent and harmless;
  (b) `Tstar G t ≤ (fuel p).length` — `Tstar` is the count `o` is defined with and may be
      `RunData`'s `K * m`, a `clog`-based number that no `Poly` program computes;
  (c) no new `ok` after `Tstar`: `okOf (round^[k] (inits G t)) = false` for `k ≥ Tstar G t`.

(c) replaces the exact-count obligation `hfuelLen` of `InitVerdict.endgame_of_loop_hn_class`, which
forces the round count to be a `Poly` function — impossible for `K * m` with a `clog` in it.  Both
routes are available; this one needs no new mathematics about the budget, only (c) about the round.

Contents: §1 the coupling at `InitVerdict.St` (`hspec_InitVerdict`), §2 the endgame with an arbitrary
fuel (`endgame_of_overshoot_InitVerdict`), §3 the same at the untruncated squaring fuel
(`endgame_of_overshoot_fuel`, where (b) is discharged by `hTle_fuel_of_length_monomial`), §4 audit.

Dependency note: this file imports `Solutions.Check_brick_init_verdict_m8` (and through it
`Check_final_stroke_m7`); it introduces no new mathematics and touches no existing file.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.HspecAssembly

open QuantumMaxCutEnergy

/-- The request coding of the leaf (same local instance as every module of the library). -/
local instance instRequestCodingHspecAsm : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The run's start states, tape forgotten**: `InitVerdict.init` at the empty tape.  This is the
`inits` of `Check_hspec_m4` at the concrete driver. -/
noncomputable def inits (G : QuantumMaxCutEnergy.Input) (t : ℚ) : QMCLeafB.InitVerdict.St :=
  QMCLeafB.InitVerdict.init (QMCLeafB.FinalStroke.noTape G t)

/-- The start states have no recorded flags. -/
@[simp] theorem inits_flags (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.InitVerdict.sFlags (inits G t) = [] := rfl

/-- **`hspec` at `InitVerdict.init`/`verdict`, from a fuel that merely reaches `Tstar` and a run
that stops reporting `ok` at `Tstar`.**  The right-hand side is m7's `loopBit`, i.e. the `o` that
`RunParts`/`RunData` are stated at. -/
theorem hspec_InitVerdict (round : QMCLeafB.InitVerdict.St → QMCLeafB.InitVerdict.St)
    (okOf : QMCLeafB.InitVerdict.St → Bool)
    (hstep : ∀ s : QMCLeafB.InitVerdict.St,
      QMCLeafB.InitVerdict.sFlags (round s) = okOf s :: QMCLeafB.InitVerdict.sFlags s)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (Tstar : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), Tstar p.1.1 p.2 ≤ (fuel p).length)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ),
      Tstar G t ≤ k → okOf (round^[k] (inits G t)) = false) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      QMCLeafB.InitVerdict.verdict (round^[(fuel p).length] (QMCLeafB.InitVerdict.init p))
        = QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round
            QMCLeafB.InitVerdict.verdict Tstar p.1.1 p.2 := by
  intro p
  refine QMCLeafB.Hspec.hspec_of_overshoot inits QMCLeafB.InitVerdict.init fuel round
    QMCLeafB.InitVerdict.verdict Tstar QMCLeafB.InitVerdict.init_tape hTle ?_ p
  intro G t T hT
  rw [QMCLeafB.InitVerdict.verdict_iterate_eq_anyOk round okOf hstep (inits G t) (inits_flags G t) T,
    QMCLeafB.InitVerdict.verdict_iterate_eq_anyOk round okOf hstep (inits G t) (inits_flags G t)
      (Tstar G t)]
  exact QMCLeafB.Hspec.anyOk_congr_of_false (fun k => okOf (round^[k] (inits G t))) hT
    (fun k hk _ => hfalse G t k hk)

/-- **The endgame with an arbitrary fuel**: `SolutionStatement` from the round, the fuel, the count
`Tstar`, the no-new-`ok` fact, the size accounting and the run bundle.  Nothing about `o`, `hspec`
or the fuel's exact length is left. -/
theorem endgame_of_overshoot_InitVerdict
    (round : QMCLeafB.InitVerdict.St → QMCLeafB.InitVerdict.St)
    (okOf : QMCLeafB.InitVerdict.St → Bool)
    (hstep : ∀ s : QMCLeafB.InitVerdict.St,
      QMCLeafB.InitVerdict.sFlags (round s) = okOf s :: QMCLeafB.InitVerdict.sFlags s)
    (hr : Automatic.Poly round)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (Tstar : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), Tstar p.1.1 p.2 ≤ (fuel p).length)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ),
      Tstar G t ≤ k → okOf (round^[k] (inits G t)) = false)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : QMCLeafB.InitVerdict.St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : QMCLeafB.InitVerdict.St × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
          Tstar) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.VerdictSound.solution_of_loop_via_runData QMCLeafB.InitVerdict.init fuel round
    QMCLeafB.InitVerdict.verdict QMCLeafB.InitVerdict.poly_init hfuel hr
    QMCLeafB.InitVerdict.poly_verdict sizes hsize hsize0
    (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict Tstar)
    (hspec_InitVerdict round okOf hstep fuel Tstar hTle hfalse) hd

/-! ## 3.  At the untruncated squaring fuel

`fuel := Fuel.fuel k` is `Poly` for free (`Fuel.poly_fuel`), and its length is `L^(2^k)` at the
input's own request word, tape and all.  So (b) becomes a monomial bound on `Tstar` in `L`, which
`hTle_fuel_of_length_monomial` discharges. -/

/-- **The endgame at `fuel := Fuel.fuel k`.**  Residual: the round with its flag discipline and its
`Poly` proof, the size accounting, the count `Tstar` with a monomial bound in the request word's
length (`C + 2d ≤ 2^k`, plus the `L = 1` case), the no-new-`ok` fact, and the run bundle. -/
theorem endgame_of_overshoot_fuel
    (round : QMCLeafB.InitVerdict.St → QMCLeafB.InitVerdict.St)
    (okOf : QMCLeafB.InitVerdict.St → Bool)
    (hstep : ∀ s : QMCLeafB.InitVerdict.St,
      QMCLeafB.InitVerdict.sFlags (round s) = okOf s :: QMCLeafB.InitVerdict.sFlags s)
    (hr : Automatic.Poly round)
    (k C d : ℕ) (hkd : C + 2 * d ≤ 2 ^ k)
    (Tstar : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      Tstar p.1.1 p.2
        ≤ C * ((QuantumMaxCutEnergy.encodeRequest p.1).length + 1) ^ d)
    (hsmall : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (QuantumMaxCutEnergy.encodeRequest p.1).length = 1 → Tstar p.1.1 p.2 ≤ 1)
    (hfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k' : ℕ),
      Tstar G t ≤ k' → okOf (round^[k'] (inits G t)) = false)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : QMCLeafB.InitVerdict.St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : QMCLeafB.InitVerdict.St × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitVerdict.init round QMCLeafB.InitVerdict.verdict
          Tstar) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_overshoot_InitVerdict round okOf hstep hr (QMCLeafB.Fuel.fuel k)
    (QMCLeafB.Fuel.poly_fuel k) Tstar
    (fun p => QMCLeafB.Hspec.hTle_fuel_of_length_monomial k C d hkd
      (fun p => Tstar p.1.1 p.2) hT hsmall p)
    hfalse sizes hsize hsize0 hd

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.HspecAssembly.inits_flags
#print axioms QMCLeafB.HspecAssembly.hspec_InitVerdict
#print axioms QMCLeafB.HspecAssembly.endgame_of_overshoot_InitVerdict
#print axioms QMCLeafB.HspecAssembly.endgame_of_overshoot_fuel

#check @QMCLeafB.HspecAssembly.endgame_of_overshoot_fuel

end QMCLeafB.HspecAssembly


