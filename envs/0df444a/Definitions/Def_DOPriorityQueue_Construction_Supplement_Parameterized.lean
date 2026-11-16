-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_Supplement_Parameterized
-- name    : DOPriorityQueue_Construction_Supplement_Parameterized
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:55.923306+00:00
-- url     : https://prove2.me/theorems/64f81d23-c7e5-41da-a9b5-861819d86ef3
-- title:
--   Theorem 5.8 — varying-privacy RAM execution contract
-- statement:
--   Let $T>2$, $\varepsilon>0$, $0<\delta<1$, and let $c_{\rm priv}\ge1$ and $c>0$ be fixed polynomial exponents. Write
--   $$\ell=\lceil\log_2T\rceil,\quad \bar\varepsilon=\min(\varepsilon,1),\quad R=\ell^2+\log_2(1/\delta),$$
--   $$M_*=\ell^{14}+\ell^7R/\bar\varepsilon,\quad g_*=1+\frac{\log_2(2+M_*)}{\log_2\ell},\quad L_T=1+\frac{\ell}{\log_2\ell}.$$
--   Admissibility requires $R/\bar\varepsilon\le T^{c_{\rm priv}}$. Public integer inputs are $c_\eta=\lceil2/\bar\varepsilon\rceil$ and $\nu=\lceil\log_2(3/\delta)\rceil$. They occupy two existing RAM registers; they give no oracle for real arithmetic.
--
--   The contract chooses one finite RAM program, positive fixed word-size factors, four positive resource constants and a fixed threshold, before $T,\varepsilon,\delta$ and every history. At every admissible horizon it requires exact stable answers and termination on every tape, normalized trace laws and complete-operation replacement privacy. Beyond the threshold it requires expected work $C_WtL_Tg_*$, pathwise probes $C_PtL_T$, peak private words $C_MM_*$ and peak server words $C_STL_T$. All these metrics are derived from the existing interpreter. Initial input delivery costs two additional words when a history is nonempty; all algorithmic setup runs as charged instructions. An empty history performs zero work.
--
--   This is the implementation interface for the varying-parameter companion theorem; it assumes no construction guarantee. Priorities are the integers $1$ through $\lfloor T^c\rfloor$. Constants depend only on the fixed exponents and primitive implementations. The resource threshold is uniform in the privacy parameters; exactness and privacy include every admissible $T>2$.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 27, Theorem 5.8; pp. 36–38, Appendices B–C

import Definitions.Def_DOPriorityQueue_Construction_Execution

set_option autoImplicit false

namespace DOPriorityQueue.Construction.Supplement

/-- Theorem 5.8, p. 27; these are external-horizon formulas, in bits. -/
noncomputable def privacyR (T : ℕ) (δ : ℝ) : ℝ :=
  (Nat.clog 2 T : ℝ) ^ 2 + Real.logb 2 (1 / δ)

noncomputable def privateBudget (T : ℕ) (ε δ : ℝ) : ℝ :=
  (Nat.clog 2 T : ℝ) ^ 14 + (Nat.clog 2 T : ℝ) ^ 7 * privacyR T δ / min ε 1

noncomputable def indexFactor (T : ℕ) (ε δ : ℝ) : ℝ :=
  1 + Real.logb 2 (2 + privateBudget T ε δ) / Real.logb 2 (Nat.clog 2 T : ℝ)

noncomputable def levelFactor (T : ℕ) : ℝ :=
  1 + (Nat.clog 2 T : ℝ) / Real.logb 2 (Nat.clog 2 T : ℝ)

noncomputable def etaInput (ε : ℝ) : ℕ := ⌈2 / min ε 1⌉₊
noncomputable def deltaInput (δ : ℝ) : ℕ := ⌈Real.logb 2 (3 / δ)⌉₊

def admissibleParameters (cpriv : ℝ) (T : ℕ) (ε δ : ℝ) : Prop :=
  2 < T ∧ 0 < ε ∧ 0 < δ ∧ δ < 1 ∧ privacyR T δ / min ε 1 ≤ (T : ℝ) ^ cpriv

/-- Only two additional public integer inputs; no exact-real privacy oracle.
The finite RAM program must perform every construction/setup computation itself. -/
def parameterInitial (w T U cη ν : ℕ) (Ball : Type) : RAM.State w Ball :=
  RAM.putRegister
    (RAM.putRegister (RAM.initialState w T U Ball) 5 (.word (BitVec.ofNat w cη)))
    6 (.word (BitVec.ofNat w ν))

/-- Delivering the two public inputs costs two words on the first invocation.
No invocation means no setup. All remaining work and space come from the interpreter. -/
def parameterRun {w : ℕ} {Ball : Type} (program : List RAM.Instruction)
    (T U cη ν fuel : ℕ) (coins : List (BitVec w)) (h : List (Operation Ball)) :
    Option (RAM.HistoryResult w Ball) := do
  let r ← RAM.runHistory program fuel (parameterInitial w T U cη ν Ball) coins h
  return { r with work := r.work + if h.isEmpty then 0 else 2 }

noncomputable def parameterCompleted {w : ℕ} {Ball : Type}
    (program : List RAM.Instruction) (T U cη ν : ℕ)
    (h : List (Operation Ball)) (coins : List (BitVec w)) :
    Option (RAM.HistoryResult w Ball) := by
  classical
  let returns := fun fuel => ∃ r,
    parameterRun program T U cη ν fuel coins h = some r ∧ r.remainingCoins = []
  exact if ht : ∃ fuel, returns fuel then
    parameterRun program T U cη ν (Nat.find ht) coins h else none

noncomputable def parameterProbability {w : ℕ} {Ball : Type}
    (program : List RAM.Instruction) (T U cη ν : ℕ)
    (h : List (Operation Ball)) (A : Set (RAM.Trace w)) : ENNReal := by
  classical
  exact ∑' coins : List (BitVec w),
    match parameterCompleted program T U cη ν h coins with
    | none => 0
    | some r => if r.traces ∈ A then RAM.coinPrefixMass w coins else 0

noncomputable def parameterWork {w : ℕ} {Ball : Type}
    (program : List RAM.Instruction) (T U cη ν : ℕ)
    (h : List (Operation Ball)) : ENNReal :=
  ∑' coins : List (BitVec w),
    match parameterCompleted program T U cη ν h coins with
    | none => 0
    | some r => RAM.coinPrefixMass w coins * (r.work : ENNReal)

def parameterExact {w : ℕ} {Ball : Type} (program : List RAM.Instruction)
    (T U cη ν : ℕ) (h : List (Operation Ball)) : Prop :=
  (∀ tape : ℕ → BitVec w, ∃ k fuel r,
    parameterRun program T U cη ν fuel (List.ofFn (fun i : Fin k => tape i.val)) h = some r ∧
      r.remainingCoins = []) ∧
  ∀ fuel coins r, parameterRun (w := w) program T U cη ν fuel coins h = some r →
    r.answers = exactAnswers h

noncomputable def parameterDO (w T U cη ν : ℕ) (program : List RAM.Instruction)
    (ε δ : ℝ) : Prop :=
  ∀ (Ball : Type) (h h' : List (Operation Ball)),
    validHistory T U h → validHistory T U h' → neighbors h h' →
    ∀ A : Set (RAM.Trace w),
      parameterProbability program T U cη ν h A ≤
        ENNReal.ofReal (Real.exp ε) * parameterProbability program T U cη ν h' A +
          ENNReal.ofReal δ

/-- A joint claim about actual finite code, not a record containing claimed costs
or certified guarantees. Constants, code, word scale and threshold precede ε, δ, T.
Exactness and privacy cover all admissible T > 2; resource bounds are asymptotic. -/
noncomputable def ParameterizedTarget (cpriv c : ℝ) : Prop :=
  ∃ (program : List RAM.Instruction) (scale offset threshold : ℕ)
    (Cwork Cprobe Cprivate Cserver : ℝ),
    0 < scale ∧ 0 < offset ∧ 3 ≤ threshold ∧
    0 < Cwork ∧ 0 < Cprobe ∧ 0 < Cprivate ∧ 0 < Cserver ∧
    ∀ (T : ℕ) (ε δ : ℝ), admissibleParameters cpriv T ε δ →
      let w := scale * Nat.clog 2 T + offset
      let U := ⌊(T : ℝ) ^ c⌋₊
      let cη := etaInput ε
      let ν := deltaInput δ
      T < 2 ^ w ∧ U < 2 ^ w ∧ cη < 2 ^ w ∧ ν < 2 ^ w ∧
      program.length + 1 < 2 ^ w ∧
      parameterDO w T U cη ν program ε δ ∧
      ∀ (Ball : Type) (h : List (Operation Ball)), validHistory T U h →
        parameterExact (w := w) program T U cη ν h ∧
        parameterProbability (w := w) program T U cη ν h Set.univ = 1 ∧
        (threshold ≤ T →
          parameterWork (w := w) program T U cη ν h ≤
            ENNReal.ofReal (Cwork * h.length * levelFactor T * indexFactor T ε δ) ∧
          ∀ fuel coins r, parameterRun (w := w) program T U cη ν fuel coins h = some r →
            (r.traces.flatten.length : ℝ) ≤ Cprobe * h.length * levelFactor T ∧
            (r.peakPrivate : ℝ) ≤ Cprivate * privateBudget T ε δ ∧
            (r.peakServer : ℝ) ≤ Cserver * T * levelFactor T)

end DOPriorityQueue.Construction.Supplement


