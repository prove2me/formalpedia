-- Prove2me | Definitions.Def_QMCLeafB_emptybottom
-- name    : QMCLeafB_emptybottom
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:29:41.827647+00:00
-- url     : https://prove2.me/theorems/9eaba950-68bf-49c0-b230-83f08976da0d
-- title:
--   QMCLeafB emptybottom
-- statement:
--   # leaf B phase 21 — the ENDPOINT form of the refutation: uniform in the input, and the
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_records_m2
import Definitions.Def_QMCLeafB_sliver2
/-
# leaf B phase 21 — the ENDPOINT form of the refutation: uniform in the input, and the
  no-horizon-can-be-repaired theorem   (swarm `smw1m5nkm`, member m1, direction d8 `campaign-falsify`)

## What this file adds

The phase-21 refutation candidate (`Check_emptybody_m5`, `RecordsM2.CoreDataF`/`ResidFinite`
unsatisfiable at `(G₀, -99999/100000)`) is a statement about **one** input.  A refutation that
depended on `G₀` being the two-vertex single-edge graph would leave the door open: "restrict the
residual to `n ≥ 3`, or to inputs with many edges, and `hcutfin` is fine".  This file closes that
door, and identifies *where* in the bracket the obstruction lives:

* §1  **the bracket's bottom endpoint is always empty.**  `Sliver2M8.no_relaxMem_at_bottom`
  (phase 20, m8, compiled and axiom-audited) says that at `t = -Rq G` *no* rational centre is a
  member, for **every** input with `Rq G > 0` and the campaign's `dq = dqShallow G`.  Here that is
  turned into `flagOf … k = false` for *every* round and *every* state family, hence into
  `¬ CoreDataF o G (-Rq G) P hn` for **every** verdict bit `o`, every `P` with `P.dq = dqShallow G`
  and every `G` with `2 ≤ G.n`, `0 < Rq G`.
* §2  **no horizon clause can be repaired at that point.**  The unsatisfiable slot is not
  `hcutfin` at the specific index `K·m`: for *every* `H : ℕ`,
  `¬ ∀ k, flagOf … k = false → k < H`.  So the repair cannot be "keep `hcutfin`, enlarge the
  horizon"; the field has to go, and the horizon-bounded restatement must bound only the *drift*
  slots (which is what `simulate_refuted_sound`'s `K·m` window needs).
* §3  **the empty slice has positive width, for every input.**  `dqShallow G · (3·Rq G/4 + 1/2) < ε G`
  (`Sliver2M8.dqShallow_mul_lt_eps'`) gives the exact interval
  `t < -Rq G + ε G - dq/2 - (3/4)·dq·Rq G` on which the body is empty — an interval of width
  `> 0` at *every* input, so the obstruction is not a boundary artefact of `t = -Rq G`.
* §4  **what the bottom still obliges** (the positive side, for the rebuilt residual): every
  `CoreDataF`-shaped record at the bottom forces the programme's verdict bit to be `false`
  (`hverdict` reads off the all-`false` stream), so the bottom's entire content is the cut side
  below the horizon — no PSD certificate, no `ok` record.
* §5  **the residual is empty**, at the campaign family and at every family whose tolerance at some
  input with `Rq > 0` is the campaign's `dqShallow`: `¬ Nonempty (ResidFinite o Pfam)` for every
  `o`.  In particular the hypothesis of `RecordsM2.solution_of_finite` is unsatisfiable.

Nothing here is new analysis: §1 and §4 are the phase-20 brick `Check_sliver2_m8` read at the
`CoreDataF` interface, and §2 is the sharp form of what `hcutfin` demands.  The point is that the
refutation is **input-independent**, so no restriction of the residual's domain of quantification
can save the `∀k`-shaped slot.

`set_option autoImplicit false`; no placeholder proofs, no extra axioms, no kernel escapes, no
machine-evaluation shortcuts; `#print axioms` audits close every section.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.EmptyBottomM1

open QuantumMaxCutEnergy

/-! ## 1.  An empty body makes every canonical flag `false`

`FlagsM5.flagOf` decides the round's flag by membership of the queried centre, so on a threshold
where no centre at all is a member, every flag is `false` — for every state family, at every index.
-/

/-- Every flag is `false` when the body is empty. -/
theorem flagOf_false_of_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    QMCLeafB.FlagsM5.flagOf G t P cX k = false :=
  QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P cX k (hempty (cX k))

#print axioms QMCLeafB.EmptyBottomM1.flagOf_false_of_emptyBody

/-- **An empty body refutes the finite-cut residual** — for every verdict bit, every round count and
every state family.  `hcutfin` asks for member centres beyond the horizon; on an empty body there are
no members at all, at any index. -/
theorem not_coreDataF_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn) : False := by
  have hf : QMCLeafB.FlagsM5.flagOf G t P
      (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) (P.K * P.m) = false :=
    flagOf_false_of_emptyBody hempty (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) (P.K * P.m)
  exact absurd (D.hcutfin (P.K * P.m) hf) (lt_irrefl _)

#print axioms QMCLeafB.EmptyBottomM1.not_coreDataF_of_emptyBody

/-- **No horizon clause survives an empty body.**  The failing field is not `hcutfin` at the single
index `K·m`: at an empty-body threshold, *no* bound `k < H` can be met by an all-`false` flag stream.
So `hcutfin` cannot be repaired by enlarging the horizon — the field has to be dropped, and the
horizon-bounded restatement must condition the *drift* slots only. -/
theorem no_horizon_of_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (H : ℕ) :
    ¬ (∀ k, QMCLeafB.FlagsM5.flagOf G t P cX k = false → k < H) := by
  intro h
  have hH : QMCLeafB.FlagsM5.flagOf G t P cX H = false :=
    flagOf_false_of_emptyBody hempty cX H
  exact absurd (h H hH) (lt_irrefl H)

#print axioms QMCLeafB.EmptyBottomM1.no_horizon_of_emptyBody

/-! ## 2.  The bottom endpoint is empty — for every input

Phase 20's `Sliver2M8.no_relaxMem_at_bottom`: at `t = -Rq G` and tolerance `dqShallow G`, no rational
matrix is a member, for every input with positive total weight.  `t = -Rq G` *is* in the residual's
bracket (`-Rq G ≤ t` is closed there), because `-Rq G < -Rq G/40000` for `Rq G > 0`. -/

/-- **Every flag is `false` at the bracket's bottom**, by the phase-20 sliver brick. -/
theorem flagOf_false_at_bottom {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : P.dq = QMCLeafB.RundataParams.dqShallow G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    QMCLeafB.FlagsM5.flagOf G (-QMCLeafB.EngineRuntime.Rq G) P cX k = false :=
  QMCLeafB.Sliver2M8.flagOf_false_at_bottom P hRq hdq cX k

#print axioms QMCLeafB.EmptyBottomM1.flagOf_false_at_bottom

/-- **`CoreDataF` is uninhabited at the bracket's bottom, for every input and every verdict bit.** -/
theorem not_coreDataF_at_bottom {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : P.dq = QMCLeafB.RundataParams.dqShallow G) :
    ¬ Nonempty (QMCLeafB.RecordsM2.CoreDataF o G (-QMCLeafB.EngineRuntime.Rq G) P hn) := by
  rintro ⟨D⟩
  have hf : QMCLeafB.FlagsM5.flagOf G (-QMCLeafB.EngineRuntime.Rq G) P
      (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) (P.K * P.m) = false :=
    flagOf_false_at_bottom P hRq hdq (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) (P.K * P.m)
  exact absurd (D.hcutfin (P.K * P.m) hf) (lt_irrefl _)

#print axioms QMCLeafB.EmptyBottomM1.not_coreDataF_at_bottom

/-- The bottom endpoint lies in the residual's interior bracket. -/
theorem bottom_mem_bracket {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    -QMCLeafB.EngineRuntime.Rq G ≤ -QMCLeafB.EngineRuntime.Rq G ∧
      ((-QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
        < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  refine ⟨le_refl _, ?_⟩
  have hRqR : (0 : ℝ) < (QMCLeafB.EngineRuntime.Rq G : ℝ) := by exact_mod_cast hRq
  have : (QMCLeafB.EngineRuntime.Rq G : ℝ) / 40000 < (QMCLeafB.EngineRuntime.Rq G : ℝ) := by
    linarith
  push_cast
  linarith

#print axioms QMCLeafB.EmptyBottomM1.bottom_mem_bracket

/-- **The residual is empty at every family whose tolerance is the campaign's `dqShallow`**, at any
input with `2 ≤ n` and positive total weight.  No restriction of the input class escapes it. -/
theorem not_residFinite_of_dqShallow (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : (Pfam G).dq = QMCLeafB.RundataParams.dqShallow G) :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite o Pfam) := by
  rintro ⟨H⟩
  have hb := bottom_mem_bracket hRq
  exact not_coreDataF_at_bottom (o := o) (G := G) (P := Pfam G) (hn := hn) hRq hdq
    ⟨H G (-QMCLeafB.EngineRuntime.Rq G) hn hb.1 hb.2⟩

#print axioms QMCLeafB.EmptyBottomM1.not_residFinite_of_dqShallow

/-- **`ResidFinite` is uninhabited at the campaign family `paramsKbc2`, for every verdict bit.** -/
theorem residFinite_empty_kbc2 (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite o QMCLeafB.UnionShallow.paramsKbc2) := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ := by
    rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num
  exact not_residFinite_of_dqShallow o QMCLeafB.UnionShallow.paramsKbc2
    (le_refl 2) hRq (QMCLeafB.UnionShallow.paramsKbc2_dq _)

#print axioms QMCLeafB.EmptyBottomM1.residFinite_empty_kbc2

/-! ## 3.  The empty slice has positive width, at every input

`trace_le` caps `⟪A, Q⟫` by `t - ε + δ/2`; `Sliver2M8.frob_lower_bound_margin` floors it by
`-(1 + 3δ/4)·Rq`.  The two are incompatible for every `t` below
`-Rq + ε - δ/2 - (3/4)·δ·Rq`, and `Sliver2M8.dqShallow_mul_lt_eps'` says that threshold is *strictly
above* `-Rq` at the campaign's `δ = dqShallow`.  So the obstruction is an interval, not a point. -/

/-- The width of the empty slice at the campaign's tolerance is positive. -/
theorem slice_width_pos {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    0 < QMCLeafB.RundataCert.eps G
        - QMCLeafB.RundataParams.dqShallow G / 2
        - (3 / 4) * QMCLeafB.RundataParams.dqShallow G * QMCLeafB.EngineRuntime.Rq G := by
  have h := QMCLeafB.Sliver2M8.dqShallow_mul_lt_eps' G hRq
  nlinarith [h]

#print axioms QMCLeafB.EmptyBottomM1.slice_width_pos

/-- **No member on the empty slice** — the body is empty for every threshold strictly below
`-Rq G + ε G - dq/2 - (3/4)·dq·Rq G`. -/
theorem no_relaxMem_of_lt {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (t : ℚ)
    (ht : t < -QMCLeafB.EngineRuntime.Rq G + QMCLeafB.RundataCert.eps G
      - P.dq / 2 - (3 / 4) * P.dq * QMCLeafB.EngineRuntime.Rq G)
    (Q : Matrix (Fin G.n) (Fin G.n) ℚ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq := by
  intro hM
  have hlow := QMCLeafB.Sliver2M8.frob_lower_bound_margin Q hM.δ_pos.le hM.diag_near hM.psd_margin
  have hle := hM.trace_le
  nlinarith [hlow, hle, ht]

#print axioms QMCLeafB.EmptyBottomM1.no_relaxMem_of_lt

/-- **The residual is empty on a whole slice of interior thresholds**, at every input: for every
`t` in the slice that is also inside the bracket, `CoreDataF` has no inhabitant. -/
theorem not_coreDataF_of_lt {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G) {hn : 2 ≤ G.n}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (t : ℚ)
    (ht : t < -QMCLeafB.EngineRuntime.Rq G + QMCLeafB.RundataCert.eps G
      - P.dq / 2 - (3 / 4) * P.dq * QMCLeafB.EngineRuntime.Rq G) :
    ¬ Nonempty (QMCLeafB.RecordsM2.CoreDataF o G t P hn) :=
  fun ⟨D⟩ => not_coreDataF_of_emptyBody (fun Q => no_relaxMem_of_lt P hRq t ht Q) D

#print axioms QMCLeafB.EmptyBottomM1.not_coreDataF_of_lt

/-! ## 4.  What the bottom still obliges

`hverdict` reads the programme's bit off the canonical flag stream; an all-`false` stream makes it
`false`.  So at an empty-body threshold any record must have `o G t = false`, and the residual's
remaining content there is the cut side below the horizon — the two drift slots and the trace
budget.  (This is the positive constraint every rebuilt residual has to respect at the bottom; it is
also the reason the bottom cannot be handled by `hverdict` alone.) -/

/-- **An all-`false` flag stream forces the programme's verdict bit to be `false`.** -/
theorem bit_false_of_allFalse {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn)
    (hall : ∀ k, QMCLeafB.FlagsM5.flagOf G t P
      (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k = false) :
    o G t = false := by
  rw [D.hverdict]
  exact (QMCLeafB.SimLoop.anyOk_eq_false_iff _ _).mpr (fun k _ => hall k)

#print axioms QMCLeafB.EmptyBottomM1.bit_false_of_allFalse

/-- **The verdict bit at every bottom is `false`**, for any hypothetical record. -/
theorem bit_false_at_bottom {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : P.dq = QMCLeafB.RundataParams.dqShallow G)
    (D : QMCLeafB.RecordsM2.CoreDataF o G (-QMCLeafB.EngineRuntime.Rq G) P hn) :
    o G (-QMCLeafB.EngineRuntime.Rq G) = false :=
  bit_false_of_allFalse D
    (fun k => flagOf_false_at_bottom P hRq hdq (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k)

#print axioms QMCLeafB.EmptyBottomM1.bit_false_at_bottom

/-- **The hypothesis of `RecordsM2.solution_of_finite` is empty.**  The phase-20 closing stroke
consumes exactly `ResidFinite (loopBit init0 round verdict Tbc2) paramsKbc2`; that type has no
inhabitant, so `solution_of_finite` is true but vacuous and cannot be the leaf's closing stroke. -/
theorem solution_of_finite_hypothesis_empty :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :=
  residFinite_empty_kbc2 _

#print axioms QMCLeafB.EmptyBottomM1.solution_of_finite_hypothesis_empty


end QMCLeafB.EmptyBottomM1

/-! ## 5.  The repaired shape is not refuted by the same argument

`hcutfin` is the only slot that fails at an empty body (§1, §2).  To make that precise, and to give
the horizon-bounded restatement a machine-checked inhabitant at the very point where the old shape
dies, this section defines the twin `CoreDataHb` — `CoreDataF` with `hcutfin` deleted and the two
drift slots unchanged (they already carry the `k < K·m` guard) — proves that the old shape restricts
to it, and *constructs* it at the bracket's bottom from exactly two things: the programme's bit being
`false` there and the two drift inequalities below the horizon.  Nothing else is needed: no member, no
PSD certificate, no `ok` record.  So the refutation is a property of `hcutfin`, not of the record idea,
and the bottom's production problem is exactly the cut side that `lamstream`/`traceBudget` own.
-/

namespace QMCLeafB.RecordsM2

open QMCLeafB.FlagsM5 (flagOf)

/-- **The horizon-bounded twin of `CoreDataF`**: `hcutfin` deleted, every flag-conditioned slot
guarded by `k < K·m`.  (This is the local form of the restatement; `RecordsM2.CoreDataF`'s fields are
unchanged, so the ok-side production loses nothing — `coreDataHb_of_coreDataF` restricts.) -/
structure CoreDataHb (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  X : ℕ → List ℚ
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  hdriftc : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    (fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ ((margOf G t P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  hdriftd : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ 0
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)

#print axioms QMCLeafB.RecordsM2.CoreDataHb

/-- **The old shape restricts to the repaired one** — deleting `hcutfin` loses nothing on the ok
side, so every anchor the phase-20 shape has is an anchor of the twin. -/
def coreDataHb_of_coreDataF {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataF o G t P hn) : CoreDataHb o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.RecordsM2.coreDataHb_of_coreDataF

/-- **The repaired shape is inhabited at the bracket's bottom** as soon as (i) the programme's bit is
`false` there and (ii) the two drift inequalities hold below the horizon.  At an empty body the
`ok`-side slots are vacuous by necessity (`EmptyBottomM1.flagOf_false_at_bottom` above), so these are
the *whole* content of the residual at a refuted point: no member, no PSD margin, no `ok` record.
This is what the `∀k`-shaped `CoreDataF` could not have, and it names the bottom's production route
exactly. -/
def coreDataHb_at_bottom {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : P.dq = QMCLeafB.RundataParams.dqShallow G)
    (hv : o G (-QMCLeafB.EngineRuntime.Rq G) = false)
    (X : ℕ → List ℚ)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hc : ∀ k, k < P.K * P.m →
      (fun i => ((nrmOf G (-QMCLeafB.EngineRuntime.Rq G) P
          (cXst G.n X P.dq) k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (cutStream G (-QMCLeafB.EngineRuntime.Rq G) P hn (cXst G.n X P.dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
        ≤ ((margOf G (-QMCLeafB.EngineRuntime.Rq G) P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2)
    (hd : ∀ k, k < P.K * P.m →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (cutStream G (-QMCLeafB.EngineRuntime.Rq G) P hn (cXst G.n X P.dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
        ≤ 0) :
    CoreDataHb o G (-QMCLeafB.EngineRuntime.Rq G) P hn := by
  refine ⟨X, hsym, ?_, ?_, ?_⟩
  · intro k hk _
    exact hc k hk
  · intro k hk _
    exact hd k hk
  · rw [hv]
    exact ((QMCLeafB.SimLoop.anyOk_eq_false_iff _ _).mpr
      (fun k _ => QMCLeafB.EmptyBottomM1.flagOf_false_at_bottom P hRq hdq
        (cXst G.n X P.dq) k)).symm

#print axioms QMCLeafB.RecordsM2.coreDataHb_at_bottom

/-- **The verdict bit of a repaired record at the bottom is `false`** — `hverdict` alone, no drift
slot and no `hcutfin`. -/
theorem coreDataHb_bit_false_at_bottom {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : P.dq = QMCLeafB.RundataParams.dqShallow G)
    (D : CoreDataHb o G (-QMCLeafB.EngineRuntime.Rq G) P hn) :
    o G (-QMCLeafB.EngineRuntime.Rq G) = false := by
  rw [D.hverdict, QMCLeafB.SimLoop.anyOk_eq_false_iff]
  intro k _
  exact QMCLeafB.EmptyBottomM1.flagOf_false_at_bottom P hRq hdq _ k

#print axioms QMCLeafB.RecordsM2.coreDataHb_bit_false_at_bottom

/-- **A necessary condition on any programme that closes through the record family**: if a
horizon-bounded record exists at every interior threshold, then the programme's verdict bit is
`false` at the bottom of the bracket at *every* input with positive total weight.  So a programme
whose read-out is `true` at `t = -Rq G` for some `G` cannot be closed by the record route at all —
this is the checksum the verdict side (`hverdict`) has to meet. -/
theorem bit_false_at_all_bottoms {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      CoreDataHb o G t (Pfam G) hn)
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hdq : (Pfam G).dq = QMCLeafB.RundataParams.dqShallow G) :
    o G (-QMCLeafB.EngineRuntime.Rq G) = false := by
  have hb := QMCLeafB.EmptyBottomM1.bottom_mem_bracket (G := G) hRq
  exact coreDataHb_bit_false_at_bottom (P := Pfam G) hRq hdq
    (H G (-QMCLeafB.EngineRuntime.Rq G) hn hb.1 hb.2)

#print axioms QMCLeafB.RecordsM2.bit_false_at_all_bottoms


end QMCLeafB.RecordsM2


