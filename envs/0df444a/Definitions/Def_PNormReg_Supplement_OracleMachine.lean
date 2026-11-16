-- Prove2me | Definitions.Def_PNormReg_Supplement_OracleMachine
-- name    : PNormReg_Supplement_OracleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:51:50.618529+00:00
-- url     : https://prove2.me/theorems/f8ff8a63-22b4-4bec-822f-2c7dd8b643a6
-- title:
--   The randomized real RAM with a randomized oracle
-- statement:
--   The base mission's randomized exact-arithmetic real RAM is extended by one instruction, an **oracle call**. A call reads a query $q$ from fixed memory cells, writes the oracle's answer into fixed cells, and advances the program counter; it costs no work, and the number of calls and the list of queries made are recorded separately. Every other instruction runs exactly as on the base machine.
--
--   An oracle is a function $O(q,\omega')$ of the query and of a private fair-coin tape $\omega'$; call number $k$ uses its own tape $\Omega_k$, independent of the program's tape $\omega$ and of the other calls. The probability space is the product of the program's tape and all oracle tapes, so queries may depend on earlier answers. An oracle is **valid** for a specification with failure parameter $\phi(q)$ if, for every query $q$, its answer meets the specification on a measurable set of private tapes of probability at least $1-\phi(q)$, and $O$ is jointly measurable.
--
--   This is the model behind running times "plus the cost of the oracle" (Theorems 4 and 6): the program's own work, the number of calls and the parameters of each call are bounded separately.
--
--   **Formalization Note** The joint measurability of the oracle is the standing convention that makes "with probability at least $1-\delta$" meaningful when queries are adaptive.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 4, p.9, and Theorem 6, p.11 (oracle-relative running times)

import Mathlib
import Definitions.Def_PNormReg_Machine

namespace PNormReg

namespace Supplement

/-!
# The randomized real RAM with a randomized oracle

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 4 (p.9) and Theorem 6 (p.11), whose
running times are stated relative to the cost of an oracle: "time `Õ(… + T^Imp_{4/ϵ} + T^Imp_4)`, where
`T^Imp_η` is the cost of querying an `η`-improvement oracle", and "`Õ(n^{ω(1,a,a)})` time plus the time to
compute … an `η^{−1}`-additive approximate solution to (5)".

**Formalization Note.**
* The base machine `PNormReg.Machine` is extended by one instruction, `oracle`. Every other instruction
  is executed by the published `PNormReg.step` on the program's base image (an `oracle` slot becomes a
  placeholder there and is never dispatched to `step`).
* An oracle call reads a query `q : Q` from the state through the interface `I.query`, and writes
  the answer's first `I.ansLen q` entries into real memory from cell `I.ansBase s` on. Nothing else
  changes except the program counter. The call costs `0` units of `work`, so `work` counts the
  non-oracle steps; the theorems bound the number of calls (`calls`) and the queries (`log`, in call
  order) separately.
* An oracle is a function `O q ω'` of the query and a private fair-coin tape; call number `k` uses
  tape `Ω k`, independent of the program's tape `ω` and of the other calls' tapes. The probability
  space is `jointTape`, the product of the program's tape and all oracle tapes. Queries may depend on
  earlier answers (adaptivity).
* `ValidOracle spec fail O`: for every query `q`, the answer meets `spec q` on a measurable set of
  private tapes of probability at least `1 − fail q`; and `O` is jointly measurable, the standing
  measurability convention that makes "with probability at least" meaningful for adaptive queries.
-/

/-- An instruction of the oracle machine: a base instruction or an oracle call. -/
inductive OInstr where
  | base (instruction : Instr)
  | oracle

/-- An oracle program: one finite list of instructions. -/
abbrev OProgram := List OInstr

/-- The base image: `oracle` slots become the placeholder `r[0] := 0`; it is never executed. -/
def baseImage (P : OProgram) : Program :=
  P.map fun op => match op with
    | .base i => i
    | .oracle => .core (.const 0 0)

/-- Admissibility: the base image is admissible (rational literals, no core `accept`/`reject`). -/
def OAdmissible (P : OProgram) : Prop := Admissible (baseImage P)

/-- An oracle interface: how a query is read from the state, and where and how long the answer
written to real memory is. -/
structure OracleIface (Q : Type) where
  query : State → Q
  ansBase : State → ℤ
  ansLen : Q → ℕ

/-- A state of the oracle machine: the base state, the number of oracle calls so far, and the
queries made, in order. -/
structure OState (Q : Type) where
  base : State
  calls : ℕ
  log : List Q

/-- Real memory after writing `a 0, …, a (len − 1)` to cells `z₀, …, z₀ + len − 1`. -/
def writeBlock (mem : ℤ → ℝ) (z₀ : ℤ) (len : ℕ) (a : ℕ → ℝ) : ℤ → ℝ :=
  fun z => if z₀ ≤ z ∧ z < z₀ + len then a (z - z₀).toNat else mem z

/-- One step. A halted state stutters. At an `oracle` instruction the query `q` is read, the answer
`O q (Ω calls)` is written, the program counter advances and `calls`, `log` are updated, at no `work`
cost. Every other instruction is one step of the base machine on the base image. -/
noncomputable def ostep {Q : Type} (P : OProgram) (I : OracleIface Q)
    (O : Q → (ℕ → Bool) → (ℕ → ℝ)) (ω : ℕ → Bool) (Ω : ℕ → ℕ → Bool) (s : OState Q) :
    OState Q :=
  if s.base.halted then s else
    match P[s.base.core.pc]? with
    | some .oracle =>
        let q := I.query s.base
        ⟨{ s.base with core := { s.base.core with
              pc := s.base.core.pc + 1
              mem := writeBlock s.base.core.mem (I.ansBase s.base) (I.ansLen q)
                (O q (Ω s.calls)) } },
          s.calls + 1, s.log ++ [q]⟩
    | _ => { s with base := step (baseImage P) ω s.base }

/-- The state after `t` steps from the input state `s₀` (no calls made yet). -/
noncomputable def orun {Q : Type} (P : OProgram) (I : OracleIface Q)
    (O : Q → (ℕ → Bool) → (ℕ → ℝ)) (s₀ : State) (ω : ℕ → Bool) (Ω : ℕ → ℕ → Bool) (t : ℕ) :
    OState Q :=
  (ostep P I O ω Ω)^[t] ⟨s₀, 0, []⟩

instance coinTape_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure coinTape := by
  unfold coinTape; infer_instance

/-- The joint probability space: the program's fair-coin tape and one independent fair-coin tape
per oracle call. -/
noncomputable def jointTape : MeasureTheory.Measure ((ℕ → Bool) × (ℕ → ℕ → Bool)) :=
  coinTape.prod (MeasureTheory.Measure.infinitePi fun _ : ℕ => coinTape)

/-- A valid randomized oracle for the specification `spec` with failure parameter `fail q`. -/
def ValidOracle {Q : Type} [MeasurableSpace Q] (spec : Q → (ℕ → ℝ) → Prop) (fail : Q → ℝ)
    (O : Q → (ℕ → Bool) → (ℕ → ℝ)) : Prop :=
  Measurable (Function.uncurry O) ∧
    ∀ q : Q, ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - fail q ≤ (coinTape E).toReal ∧
      ∀ ω' ∈ E, spec q (O q ω')

end Supplement

end PNormReg


