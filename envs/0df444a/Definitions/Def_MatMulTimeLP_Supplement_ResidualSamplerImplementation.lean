-- Prove2me | Definitions.Def_MatMulTimeLP_Supplement_ResidualSamplerImplementation
-- name    : MatMulTimeLP_Supplement_ResidualSamplerImplementation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:56:21.403727+00:00
-- url     : https://prove2.me/theorems/a5df3f5e-3f25-4502-bb24-1ff91680ebdc
-- title:
--   Stateful exact-real-RAM implementation interface for the residual sampler
-- statement:
--   A **residual-sampler implementation** of dimension $n$ consists of three persistent exact-real-RAM programs—initialization, coordinate update and sampling—together with the first halting time of every call. The fixed matrix $H$ and vector $h$ occupy the initial real-memory prefix, the maintained vector $z$ occupies a disjoint block, and operation arguments and answers use reserved cells.
--
--   Calls reset only the program counter and write their explicit arguments; every other cell persists. Consequently, an update or query loader cannot perform cache maintenance or sampling work for free. A stream of independent real-RAM tapes drives initialization and successive calls, and `residualRun` records the chronological transcript and separately charged initialization, update and sampling work against an adaptive adversary.
--
--   This interface is the operational substrate used to state Theorem 5.12 without replacing running time by an unconstrained numerical field.
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…), Theorem 5.12, p.32 and Algorithm 6, pp.45–47

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_MatMulTimeLP_FixPoint
import Definitions.Def_MatMulTimeLP_Sampler

namespace MatMulTimeLP

namespace Supplement

set_option autoImplicit false

open MeasureTheory

/-!
# Stateful exact-real-RAM interface for the residual sampler

Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 5.12, p.32 and Algorithm 6,
pp.45–47.

**Formalization Note** The published `MatMulTimeLP.State`, `Program`, `Tape`, `step`, `tapeLaw`,
`residual`, sampler answers, adaptive adversaries, validity predicate, transcripts and ideal
transcript probabilities are reused.  A call resets only the program counter and writes its
arguments in reserved cells; all other cells, including the Gaussian sketch and cached root
sketch, persist.  Thus the loaders cannot perform the data structure's work for free.

The real input bank initially contains `H` row by row followed by `h`.  The maintained vector
`z` starts at address `n*n+n`; the next real cell is the scalar argument of `Update` or `Sample`.
Index cell `0` is the update coordinate.  After `Sample`, index cell `1` is the answer tag
(`0 = Fail`, `1 = ⊥`, `2 = coordinate`) and cell `2` is the coordinate.  Each operation receives
a fresh independent `Tape`; the state carries all randomness that must persist between calls.
-/

/-- A real-RAM state after `t` steps of `P`, starting from an arbitrary persistent state. -/
noncomputable def stateAtFrom (P : Program) (ω : Tape) (s : State) : ℕ → State
  | 0 => s
  | t + 1 => step P ω t (stateAtFrom P ω s t)

/-- `t` is the first halting time of a call started from the persistent state `s`. -/
def HaltsFromAt (P : Program) (ω : Tape) (s : State) (t : ℕ) : Prop :=
  IsHalted P (stateAtFrom P ω s t) ∧ ∀ u < t, ¬ IsHalted P (stateAtFrom P ω s u)

/-- Address of coordinate `i` of the maintained vector `z`. -/
def residualZAddr (n : ℕ) (i : Fin n) : ℕ := n * n + n + i

/-- Reserved real cell containing `z'_i` for `Update` or `U` for `Sample`. -/
def residualArgAddr (n : ℕ) : ℕ := n * n + 2 * n

/-- The initial state of the residual sampler: `H` and `h` are present in the input bank. -/
noncomputable def residualInitState {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) : State :=
  initState (matToList H ++ vecToList h)

/-- Load `Update(i,z'_i)`: reset the program counter and write only the two call arguments. -/
def loadResidualUpdate {n : ℕ} (s : State) (i : Fin n) (zi : ℝ) : State :=
  { s with
    pc := 0
    R := Function.update s.R (residualArgAddr n) zi
    N := Function.update s.N 0 i }

/-- Load `Sample(U)`: reset the program counter and write only `U`. -/
def loadResidualSample {n : ℕ} (s : State) (U : ℝ) : State :=
  { s with pc := 0, R := Function.update s.R (residualArgAddr n) U }

/-- Read the maintained vector from a persistent state. -/
def residualStateZ {n : ℕ} (s : State) : Fin n → ℝ :=
  fun i => s.R (residualZAddr n i)

/-- Read the sampler answer from its fixed output cells. -/
def decodeResidualAnswer {n : ℕ} (s : State) : Answer n :=
  if s.N 1 = 0 then Answer.fail
  else if s.N 1 = 1 then Answer.bot
  else if s.N 1 = 2 then
    if hi : s.N 2 < n then Answer.coord ⟨s.N 2, hi⟩ else Answer.fail
  else Answer.fail

/-- Three uniform programs and their first-halt-time witnesses for a residual sampler of size `n`.
The programs are chosen before `H`, `h`, the mutable state, and the adversary. -/
structure ResidualSamplerImplementation (n : ℕ) where
  initProgram : Program
  updateProgram : Program
  sampleProgram : Program
  initTime : Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → Tape → ℕ
  updateTime : State → Fin n → ℝ → Tape → ℕ
  sampleTime : State → ℝ → Tape → ℕ

/-- State after initialization. -/
noncomputable def ResidualSamplerImplementation.initResult {n : ℕ}
    (I : ResidualSamplerImplementation n) (H : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (ω : Tape) : State :=
  stateAtFrom I.initProgram ω (residualInitState H h) (I.initTime H h ω)

/-- State after one update call. -/
noncomputable def ResidualSamplerImplementation.updateResult {n : ℕ}
    (I : ResidualSamplerImplementation n) (s : State) (i : Fin n) (zi : ℝ) (ω : Tape) : State :=
  stateAtFrom I.updateProgram ω (loadResidualUpdate s i zi) (I.updateTime s i zi ω)

/-- State after one sample call. -/
noncomputable def ResidualSamplerImplementation.sampleResult {n : ℕ}
    (I : ResidualSamplerImplementation n) (s : State) (U : ℝ) (ω : Tape) : State :=
  stateAtFrom I.sampleProgram ω (loadResidualSample (n := n) s U) (I.sampleTime s U ω)

/-- A countable stream of independent call tapes; tape `0` initializes, and subsequent tapes serve
successive operations. -/
abbrev CallTapes := ℕ → Tape

/-- Law of the independent call-tape stream. -/
noncomputable def callTapesLaw : Measure CallTapes :=
  Measure.infinitePi fun _ => tapeLaw

instance : IsProbabilityMeasure callTapesLaw := by
  unfold callTapesLaw
  infer_instance

/-- Observable result and charged work of a run against an adaptive adversary.  The transcript is
chronological, while the adversary receives the same newest-first histories as `Adversary`. -/
structure ResidualRun (n : ℕ) where
  state : State
  transcript : Transcript n
  initWork : ℕ
  updateCount : ℕ
  sampleCount : ℕ
  updateWork : ℕ
  sampleWork : ℕ
  /-- Sum over sample calls of `(log(2+n))^4 * (1 + n*E/U)`, before the uniform constant. -/
  sampleScale : ℝ

/-- Positive logarithmic factor used to state the asymptotic bounds uniformly also for `n = 1`. -/
noncomputable def dsLog (n : ℕ) : ℝ := Real.log (2 + (n : ℝ))

noncomputable def residualRunAux {n : ℕ} (I : ResidualSamplerImplementation n)
    (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (adv : Adversary n) :
    ℕ → State → Transcript n → ℕ → CallTapes → ResidualRun n
  | 0, s, hist, _, _ =>
      { state := s, transcript := hist.reverse, initWork := 0, updateCount := 0,
        sampleCount := 0, updateWork := 0, sampleWork := 0, sampleScale := 0 }
  | m + 1, s, hist, q, Ω =>
      match adv hist with
      | none =>
          { state := s, transcript := hist.reverse, initWork := 0, updateCount := 0,
            sampleCount := 0, updateWork := 0, sampleWork := 0, sampleScale := 0 }
      | some (Op.update i zi) =>
          let w := I.updateTime s i zi (Ω q) + 1
          let s' := I.updateResult s i zi (Ω q)
          let out := residualRunAux I H h adv m s' (none :: hist) (q + 1) Ω
          { out with
            updateCount := out.updateCount + 1
            updateWork := out.updateWork + w }
      | some (Op.sample U) =>
          let r := residual H h (residualStateZ s)
          let scale := dsLog n ^ 4 * (1 + n * energyE r / U)
          let w := I.sampleTime s U (Ω q) + 1
          let s' := I.sampleResult s U (Ω q)
          let a := decodeResidualAnswer s'
          let out := residualRunAux I H h adv m s' (some a :: hist) (q + 1) Ω
          { out with
            sampleCount := out.sampleCount + 1
            sampleWork := out.sampleWork + w
            sampleScale := out.sampleScale + scale }

/-- Run the initialized implementation for at most `m` adaptive operations. -/
noncomputable def residualRun {n : ℕ} (I : ResidualSamplerImplementation n)
    (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (adv : Adversary n)
    (m : ℕ) (Ω : CallTapes) : ResidualRun n :=
  let s := I.initResult H h (Ω 0)
  let out := residualRunAux I H h adv m s [] 1 Ω
  { out with initWork := I.initTime H h (Ω 0) + 1 }

/-- A persistent state that arises after initialization and a finite adaptive call sequence. -/
def ResidualSamplerImplementation.Reachable {n : ℕ} (I : ResidualSamplerImplementation n)
    (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (s : State) : Prop :=
  ∃ (adv : Adversary n) (m : ℕ) (Ω : CallTapes), (residualRun I H h adv m Ω).state = s

end Supplement

end MatMulTimeLP


