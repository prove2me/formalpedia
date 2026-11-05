-- Prove2me | Definitions.Def_QMCLeafB_asm2
-- name    : QMCLeafB_asm2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:02:08.558236+00:00
-- url     : https://prove2.me/theorems/225fba98-811f-4f96-8244-eac39b0a1711
-- title:
--   QMCLeafB asm2
-- statement:
--   `Check_asm2_m8` — phase 30, m8 (assembly): **the composite stroke.**
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_asm_m8
import Definitions.Def_QMCLeafB_fal30
/-
  `Check_asm2_m8` — phase 30, m8 (assembly): **the composite stroke.**

  `Check_asm_m8` reduced the template's `hd` to classes; `Check_fal30_m4` (m4's accepted
  falsification lane) reduced the size ledger to ONE one-step length bound and machine-checked

    `Fal30.hcert_from_relaxMem :  RelaxMem (wMatrixQ G) cX (t - eps G) (dqShallow G)  +  cXᵀ = cX`
    `  ⟹  ∃ unit-diagonal PSD X with tr (wMatrix G · X) ≤ t + eps G`

  (the rounding is `RelaxOracle.relaxMem_witness` + the banked `paramsKbc2_budget`).

  This file composes the two.  The leaf's remaining content becomes, in one machine-checked
  statement:

    (1) the three `Poly` slots of `(init, round, verdict)`;
    (2) `hstepLen : (enc (round s)).length ≤ (enc s).length + c`     (m4's ledger collapse);
    (3) `hinitTape`, `htop`;
    (4) `hbit :  on the interior, the bit is `false` exactly at the empty-body points;
    (5) `hok  :  bit `true` ⟹ a symmetric `RelaxMem` at the program's OWN centre, at level
                `t - eps` and the campaign tolerance `dqShallow` — i.e. `ok` must MEAN the loop's
                membership test at its own centre (soundness is what the template consumes);
    (6) `hC   :  body non-empty and bit `false` ⟹ `RunParts` (the thin band; `CruxM1.allFalseParts`
                produces it from a `Cut0` family + the enclosure inequality).

  Everything else — the `hcert` witness, the all-`ok` record, the empty-body record, the ledger
  `(M, C₀, kr, hMinv, hstep, hM)` — is discharged here from the lanes' bricks.

  Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section

namespace Asm2M8

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingAsm2 : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The interior bracket forces positive total weight**: `-Rq ≤ t < -Rq/40000` is empty
unless `Rq > 0`. -/
theorem Rq_pos_of_interior {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hint : AsmM8.Interior G t) : 0 < QMCLeafB.EngineRuntime.Rq G := by
  have h1 : ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ) ≤ (t : ℝ) := by
    have h := hint.1
    exact_mod_cast h
  have h2 : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := hint.2
  push_cast at h1 h2
  have h3 : ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) / 40000
      < ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by linarith
  have h4 : (0 : ℝ) < ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by nlinarith
  exact_mod_cast h4

/-- **`RelaxMem` at the loop's own centre gives the `hd` witness class.** -/
theorem memberAt_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hint : AsmM8.Interior G t)
    (hok : ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    AsmM8.MemberAt G t := by
  obtain ⟨cX, hsym, h⟩ := hok
  exact QMCLeafB.Fal30.hcert_from_relaxMem G t cX hn (Rq_pos_of_interior hint) hsym h

/-- **The composite stroke**: `d9f601e5` from the residual list above. -/
theorem solution_of_residual {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ, (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2) G t
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  refine QMCLeafB.Fal30.solution_of_step_le k hk init round verdict hinit hr hv c hstepLen
    hinitTape htop ?_
  intro G t hn hlo hhi
  have hdall := AsmM8.hd_of_classes
    (o := QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2)
    (fun G t hn hint he => (hbit G t hn hint).mpr he)
    (fun G t hn hint hb => memberAt_of_relaxMem hn hint (hok G t hn hint hb))
    hC
  exact hdall G t hn hlo hhi

#print axioms Asm2M8.Rq_pos_of_interior
#print axioms Asm2M8.memberAt_of_relaxMem
#print axioms Asm2M8.solution_of_residual

end Asm2M8


