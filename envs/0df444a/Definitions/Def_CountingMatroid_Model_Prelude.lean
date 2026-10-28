-- Prove2me | Definitions.Def_CountingMatroid_Model_Prelude
-- name    : CountingMatroid_Model_Prelude
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T11:19:20.896988+00:00
-- url     : https://prove2.me/theorems/13a0d795-bbaf-495d-81b6-805d9fce206c
-- title:
--   Common-basis counting model and annealing data types
-- statement:
--   For $n\in\mathbb N$, write $E_n=\{0,\ldots,n-1\}$. A subset query is a Boolean function $q:E_n\to\{0,1\}$ representing $\{i:q(i)=1\}$, and an independence oracle is any Boolean function on such queries. Exactness for a matroid $M$ means that its answer is true precisely for independent represented subsets. For two matroids $M_1,M_2$ on $E_n$, the full-ground predicate requires both ground fields to equal $E_n$; the common-rank predicate requires both ranks to equal a specified $r\in\mathbb N$. The common-basis family and its count are $$\mathcal B(M_1,M_2)=\{B\subseteq E_n:B\text{ is a basis of both }M_1\text{ and }M_2\},\qquad Z(M_1,M_2)=|\mathcal B(M_1,M_2)|.$$
--
--   Input parameters are rationals $\varepsilon,\delta$ with $0<\varepsilon,\delta<1$. Define $\lambda(m)=\lfloor\log_2m\rfloor+1$, with $\lambda(0)=1$. For reduced $a/b\in\mathbb Q$ with $b>0$, set $\ell(a/b)=2+\lambda(|a|)+\lambda(b)$ and define the input length by $$\lambda(n)+\lambda(r)+\ell(\varepsilon)+\ell(\delta).$$ The paired ground is $E_n\times\{0,1\}$; a paired state is any finite subset of this ground. State labels are transversal, defect with two specified pair labels, and invalid. A defect index is an ordered pair $(i,k)$ with $i\ne k$. A multiplier table is a function from defect indices to $\mathbb Q$, and learned weights are a natural-number-indexed family of multiplier tables.
--
--   An annealing schedule stores natural parameters $b_\varepsilon,L,\tau,\mathrm{restartCap},\mathrm{observations},\mathrm{drawCalls},\mathrm{drawTrials},b_\delta,\mathrm{repetitions}$ and rational parameters $\rho,\eta$. The fields $b_\varepsilon,b_\delta$ record accuracy and confidence scales; $L$ is the phase count; $\tau$ is a time parameter; restartCap bounds restart steps; observations counts observations; drawCalls and drawTrials record draw and trial budgets; repetitions counts repeated runs; and $\rho,\eta$ record cooling and relative-error parameters. An execution-cost record stores three natural counters, named oracleCalls, bitOps, and randomBits. An execution result consists of a rational estimate $z\ge0$ together with such a cost record.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Model/Prelude.lean#L26-L141

import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Rat.Defs

section


set_option autoImplicit false

/-!
# Common-base counting vocabulary

Correspondence ledger: main.tex:69–83 uses `[n]`, represented here by `Fin n` via
`i ↦ i + 1`; its n-bit independence query is `Query n`. The paper's common-base
quantity `Z(M₁,M₂)` is `commonBaseCount`. The algorithmic parameters ε and δ
are rational fields of `InputParams`. The paper leaves their binary encoding and
its bit-cost machine unspecified. `binaryInputLength` fixes the former; a RAM
realization of nonoracle bit operations remains an open obligation.
main.tex:244–316 -> `PairedGround`, `PairedSet`, `StateKind`, `DefectIndex`;
main.tex:1105–1150 and 1392–1448 -> `AnnealingSchedule`. These types carry
the program's data; their rank and state-space correspondence is a proof
obligation. The set-based transport figure at main.tex:692 is analytical and
has no executable definition here (statement decision).
-/

namespace CountingMatroid.Model

/-! ## Vocabulary -/

/-- One n-bit subset indicator, with `Fin n` representing paper label `i+1`. -/
abbrev Query (n : ℕ) := Fin n → Bool

/-- The subset denoted by an n-bit oracle query. -/
def decode {n : ℕ} (q : Query n) : Set (Fin n) := {i | q i = true}

/-- A fixed Boolean independence oracle on the n-bit query interface. -/
abbrev IndependenceOracle (n : ℕ) := Query n → Bool

/-- The exact-oracle promise, stated against Mathlib's independence predicate. -/
noncomputable def ExactOracle {n : ℕ} (M : Matroid (Fin n))
    (o : IndependenceOracle n) : Prop := by
  classical
  exact ∀ q, o q = decide (M.Indep (decode q))

/-- The shared rank promise, using Mathlib's finite-valued `eRank` on `Fin n`. -/
noncomputable def CommonRank {n : ℕ} (r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) : Prop :=
  M₁.eRank = r ∧ M₂.eRank = r

/-- The paper supplies matroids on all of `[n]`, rather than matroids whose
Mathlib ground fields are proper subsets of `Fin n`. -/
def FullGround {n : ℕ} (M₁ M₂ : Matroid (Fin n)) : Prop :=
  M₁.E = Set.univ ∧ M₂.E = Set.univ

/-- Rational accuracy and confidence inputs, with their caller-side range promises. -/
structure InputParams where
  ε : ℚ
  δ : ℚ
  ε_pos : 0 < ε
  ε_lt_one : ε < 1
  δ_pos : 0 < δ
  δ_lt_one : δ < 1

/-- Unsigned binary length, with one digit for zero. -/
def binaryNatLength (m : ℕ) : ℕ := m.log2 + 1

/-- Canonical rational encoding: one sign bit, binary absolute numerator,
binary positive denominator, and one delimiter bit. -/
def binaryRatLength (q : ℚ) : ℕ :=
  2 + binaryNatLength q.num.natAbs + binaryNatLength q.den

/-- The input-length parameter under the preceding convention. -/
def binaryInputLength (n r : ℕ) (p : InputParams) : ℕ :=
  binaryNatLength n + binaryNatLength r +
    binaryRatLength p.ε + binaryRatLength p.δ

/-- Paper's paired ground set, with `false` marking x and `true` marking y. -/
abbrev PairedGround (n : ℕ) := Fin n × Bool

/-- A paired n-element state is recorded as a finite set. Its n-cardinality and
transversal-or-ordered-defect shape are guarded in the annealing program. -/
abbrev PairedSet (n : ℕ) := Finset (PairedGround n)

/-- Shape recognized by the executable paired-state scan. The off-diagonal
guard on a defect is checked by that scan; diagonal values are invalid. -/
inductive StateKind (n : ℕ) where
  | transversal
  | defect (emptyPair fullPair : Fin n)
  | invalid
  deriving DecidableEq

/-- Ordered defect type. The `i ≠ j` witness keeps n=1's type family empty. -/
structure DefectIndex (n : ℕ) where
  emptyPair : Fin n
  fullPair : Fin n
  distinct : emptyPair ≠ fullPair
  deriving DecidableEq

/-- The phase's learned positive rational multiplier for each ordered defect. -/
abbrev Multipliers (n : ℕ) := DefectIndex n → ℚ

/-- Stored learned multiplier tables, indexed by annealing phase. -/
abbrev LearnedWeights (n : ℕ) := ℕ → Multipliers n

/-- The exact rational and integral schedule of main.tex:1105–1150 and
1392–1448. It is computed by the charged `Program.schedule` below. -/
structure AnnealingSchedule where
  bε : ℕ
  ρ : ℚ
  L : ℕ
  η : ℚ
  τ : ℕ
  restartCap : ℕ
  observations : ℕ
  drawCalls : ℕ
  drawTrials : ℕ
  bδ : ℕ
  repetitions : ℕ

/-- Actual work counters: original-oracle calls, nonoracle bit operations, and
fair-bit reads are kept separate on each finite execution. -/
structure ExecutionCost where
  oracleCalls : ℕ
  bitOps : ℕ
  randomBits : ℕ

/-- One finite execution's rational answer and accumulated work. -/
structure ExecutionResult where
  estimate : ℚ
  nonnegative : 0 ≤ estimate
  cost : ExecutionCost

/-! ## The quantity -/

/-- The two Mathlib base families intersected on the explicit finite ground set.
There is no library common-base counter in this pin. -/
noncomputable def commonBases {n : ℕ} (M₁ M₂ : Matroid (Fin n)) : Finset (Finset (Fin n)) :=
  by
    classical
    exact Finset.univ.filter (fun B => M₁.IsBase (B : Set (Fin n)) ∧
      M₂.IsBase (B : Set (Fin n)))

/-- `Z(M₁,M₂)` from main.tex:75–83, including the empty ground set. -/
noncomputable def commonBaseCount {n : ℕ} (M₁ M₂ : Matroid (Fin n)) : ℕ :=
  (commonBases M₁ M₂).card

end CountingMatroid.Model

end


