-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_LocalProgram
-- name    : GibbsTransition_SizeCopies_LocalProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:54:00.442736+00:00
-- url     : https://prove2.me/theorems/4d751247-348f-485a-b4ed-db556c2d65de
-- title:
--   Effective local learners with charged binary-stack execution
-- statement:
--   An upper learner is finite code for binary stacks, with instructions to push or pop one bit, branch, draw a fair coin, measure one site of one fresh Gibbs cube, and return a rational estimate. Four input stacks contain the numerator and denominator of the positive rational accuracy and confidence inputs. There is no input describing the unknown interaction.
--
--   Each local quantum instruction has the actual Born probability $\operatorname{tr}(\rho^\beta_{u,L}(\phi)P_x)$, consumes one independently prepared cube, and retains only its binary measurement result. Its arguments encode a positive side length, dyadic field and site. Invalid encodings halt at the public midpoint and never provide an invalid state. All estimates lie in $[1/4,3/4]$.
--
--   Push, pop and fair-coin instructions are charged bit operations. Oracle arguments are charged their binary lengths, including the actual dyadic precision, and reading the rational output is charged its length. The input-read cost is included. The program's absorbing execution law determines its error, copy/size/spin bounds, and extended expected bit cost. Polynomial time means a fixed positive coefficient and fixed natural degree bounding that computed expectation in the input bit length. The code carries no fields asserting correctness or runtime.
--
--   The file also specifies the actual source learner: the exact overlapping search, $L_k=\lceil216/\gamma_k\rceil$, $\delta_k=\delta 2^{k-K}$, and sample counts from a finite rational atanh-series upper approximation to the logarithm. Its error is below $1/512$, so the integer sample counts lie in the complete interval (28). The reference round law uses the mean of a uniform random-site measurement on each independent cube. `ImplementsUpper` requires finite code to realize its joint output/query law on every admissible interaction and every positive temperature; accuracy and cost guarantees remain theorem conclusions.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), §5.1, Equation (28), printed p. 9 (PDF p. 11); §8, printed p. 18 (PDF p. 20); Appendix B.3 and scalar-log arithmetic in B.5, printed pp. 23, 25 (PDF pp. 25, 27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Experiment
import Definitions.Def_GibbsTransition_SizeCopies_Interval

set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GibbsTransition.SizeCopies

attribute [local instance] Classical.propDecidable

/-- A finite binary-stack machine. Stack heads are low bits. Push/pop are
charged bit operations; jumps are part of the instruction. A measurement
instruction consumes a fresh cube and measures P at just the encoded site. -/
inductive BitInstruction where
  | push (bit : Bool) (register next : ℕ)
  | pop (register empty onZero onOne : ℕ)
  | coin (register next : ℕ)
  | measure (side numerator exponent x y z result next : ℕ)
  | halt (numerator denominator : ℕ)
  deriving Countable

structure LocalProgram where
  code : List BitInstruction
  deriving Countable

structure ProgramRecord where
  pc : ℕ
  registers : List (List Bool)
  halted : Bool
  estimate : ℚ
  queries : List CubeQuery
  bitCost : ℕ
  deriving Countable

instance : MeasurableSpace ProgramRecord := ⊤

def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * binaryValue l

/-- A canonical, effective low-bit-first encoding, including zero. -/
def binaryDigits (n : ℕ) : List Bool := (Nat.digits 2 n).map (fun d => d = 1)

def readStack (r : ProgramRecord) (i : ℕ) : List Bool := r.registers[i]?.getD []
def readNumber (r : ProgramRecord) (i : ℕ) : ℕ := binaryValue (readStack r i)

def writeStack (r : ProgramRecord) (i : ℕ) (s : List Bool) : ProgramRecord :=
  let extended := r.registers ++ List.replicate (i + 1 - r.registers.length) []
  { r with registers := extended.set i s }

def advance (r : ProgramRecord) (pc charge : ℕ) : ProgramRecord :=
  { r with pc := pc, bitCost := r.bitCost + charge }

def finishProgram (r : ProgramRecord) (estimate : ℚ) (charge : ℕ) : ProgramRecord :=
  { r with halted := true, estimate := estimate, bitCost := r.bitCost + charge }

/-- Invalid oracle/estimate encodings terminate at the public midpoint.
They never grant access to an invalid field, site or side length. -/
def invalidProgram (r : ProgramRecord) : ProgramRecord := finishProgram r (1/2) 1

def decodeQuery (r : ProgramRecord) (s n e : ℕ) : Option CubeQuery :=
  let L := readNumber r s
  let m := readNumber r n
  let k := readNumber r e
  let phi : ℚ := (m : ℚ) / 2 ^ k
  if h : 1 ≤ L ∧ phi ∈ Set.Icc (0 : ℚ) 1 then
    some ⟨L, phi, h.1, h.2, m, k, rfl⟩
  else none

def decodeSite (r : ProgramRecord) (L x y z : ℕ) : Option (Site L) :=
  let v : Fin 3 → ℕ := ![readNumber r x, readNumber r y, readNumber r z]
  if h : ∀ i, v i < L then some (fun i => ⟨v i, h i⟩) else none

/-- Born probability of the single local P measurement on the fresh cube. -/
def localBorn (u : Interaction) (beta : ℚ) (q : CubeQuery) (x : Site q.side) : ℝ :=
  (Matrix.trace (gibbsDensity u q.side q.field beta * atSite publicP x)).re

def binaryBranch (p : ℝ) (yes no : ProgramRecord) : Measure ProgramRecord :=
  ENNReal.ofReal p • Measure.dirac yes + ENNReal.ofReal (1-p) • Measure.dirac no

/-- The oracle argument cost includes the actual dyadic precision, not just
the bit length of its exponent. Finite code has only fixed register addresses. -/
def queryBitCost (r : ProgramRecord) (s n e x y z : ℕ) : ℕ :=
  1 + (readStack r s).length + (readStack r n).length + readNumber r e +
    (readStack r x).length + (readStack r y).length + (readStack r z).length

def programStep (P : LocalProgram) (u : Interaction) (beta : ℚ)
    (r : ProgramRecord) : Measure ProgramRecord :=
  if r.halted then Measure.dirac r else
  match P.code[r.pc]? with
  | none => Measure.dirac (invalidProgram r)
  | some (.push b i pc) =>
      Measure.dirac (advance (writeStack r i (b :: readStack r i)) pc 1)
  | some (.pop i empty onZero onOne) =>
      match readStack r i with
      | [] => Measure.dirac (advance r empty 1)
      | b :: l => Measure.dirac (advance (writeStack r i l) (if b then onOne else onZero) 1)
  | some (.coin i pc) =>
      binaryBranch (1/2)
        (advance (writeStack r i (true :: readStack r i)) pc 1)
        (advance (writeStack r i (false :: readStack r i)) pc 1)
  | some (.measure s n e x y z result pc) =>
      match decodeQuery r s n e with
      | none => Measure.dirac (finishProgram r (1/2) (queryBitCost r s n e x y z))
      | some q =>
          match decodeSite r q.side x y z with
          | none => Measure.dirac (finishProgram r (1/2) (queryBitCost r s n e x y z))
          | some site =>
              let base := { r with queries := r.queries ++ [q] }
              let cost := queryBitCost r s n e x y z
              binaryBranch (localBorn u beta q site)
                (advance (writeStack base result (true :: readStack r result)) pc cost)
                (advance (writeStack base result (false :: readStack r result)) pc cost)
  | some (.halt n d) =>
      let estimate : ℚ := (readNumber r n : ℚ) / readNumber r d
      if 0 < readNumber r d ∧ estimate ∈ Set.Icc (1/4 : ℚ) (3/4) then
        Measure.dirac (finishProgram r estimate
          (1 + (readStack r n).length + (readStack r d).length))
      else Measure.dirac (finishProgram r (1/2)
        (1 + (readStack r n).length + (readStack r d).length))

/-- Binary lengths of the exact positive rational inputs. -/
def accuracyBits (epsilon delta : ℚ) : ℕ :=
  (binaryDigits epsilon.num.natAbs).length + (binaryDigits epsilon.den).length +
  (binaryDigits delta.num.natAbs).length + (binaryDigits delta.den).length + 1

def programInitial (epsilon delta : ℚ) : ProgramRecord where
  pc := 0
  registers := [binaryDigits epsilon.num.natAbs, binaryDigits epsilon.den,
    binaryDigits delta.num.natAbs, binaryDigits delta.den]
  halted := false
  estimate := 1/2
  queries := []
  bitCost := accuracyBits epsilon delta

def programRun (P : LocalProgram) (u : Interaction) (beta epsilon delta : ℚ) :
    ℕ → Measure ProgramRecord
  | 0 => Measure.dirac (programInitial epsilon delta)
  | t+1 => (programRun P u beta epsilon delta t).bind (programStep P u beta)

def programTerminates (P : LocalProgram) (u : Interaction) (beta epsilon delta : ℚ) : Prop :=
  (⨆ t, programRun P u beta epsilon delta t {r | r.halted = true}) = 1

def programError (P : LocalProgram) (u : Interaction) (beta epsilon delta : ℚ) : ℝ≥0∞ :=
  ⨆ t, programRun P u beta epsilon delta t {r |
    r.halted = true ∧ |(r.estimate : ℝ) - transitionPoint u| > epsilon}

def programCorrect (P : LocalProgram) (u : Interaction) (beta epsilon delta : ℚ) : Prop :=
  programTerminates P u beta epsilon delta ∧
    programError P u beta epsilon delta ≤ ENNReal.ofReal delta

/-- Deterministic resource bounds hold at every horizon, hence also at the
almost-sure stopping time. The time bound below is an extended expectation. -/
def programResources (P : LocalProgram) (u : Interaction) (beta epsilon delta : ℚ)
    (size : ℕ) (copies spins : ℝ) : Prop :=
  ∀ t, ∀ᵐ r ∂programRun P u beta epsilon delta t,
    (∀ q ∈ r.queries, q.side ≤ size) ∧
    (r.queries.length : ℝ) ≤ copies ∧
    (((r.queries.map (fun q => q.side ^ 3)).sum : ℕ) : ℝ) ≤ spins

def programTime (P : LocalProgram) (u : Interaction) (beta epsilon delta : ℚ) : ℝ≥0∞ :=
  ⨆ t, ∫⁻ r, (r.bitCost : ℝ≥0∞) ∂programRun P u beta epsilon delta t

/-- A single program with a uniform expected polynomial bit-operation bound.
The coefficient and degree are quantified outside all physical/input data. -/
def polynomialTimeAt (P : LocalProgram) (u : Interaction) (beta epsilon delta : ℚ)
    (coefficient : ℝ) (degree : ℕ) : Prop :=
  programTime P u beta epsilon delta ≤
    ENNReal.ofReal (coefficient * (accuracyBits epsilon delta : ℝ) ^ degree)

/-- Rational logarithm approximation used to choose the source's sample counts.
For q>=1, range reduction gives 1<=x<2. The positive atanh series truncated
at B+16 terms has error <1/512, including the m copies of log 2. Adding 1/512
therefore gives an upper approximation within 1/512. No real-log oracle is used. -/
def rationalLogSeries (x : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, ((x-1)/(x+1))^(2*i+1) / (2*i+1 : ℚ)

def rationalLogUpper (q : ℚ) : ℚ :=
  let B := (binaryDigits q.num.natAbs).length
  let m := ((List.range (B+1)).filter (fun k => (2 : ℚ)^k ≤ q)).foldl max 0
  let x := q / (2 : ℚ)^m
  (m : ℚ) * rationalLogSeries 2 (B+16) + rationalLogSeries x (B+16) + 1/512

def upperSampleCount (epsilon delta : ℚ) (k : ℕ) : ℕ :=
  let K := searchRounds epsilon
  let delta_k := delta / (2 : ℚ)^(K-k)
  ⌈128 * rationalLogUpper (2/delta_k)⌉₊

/-- The exact source query: L=ceil(216/gamma), with the midpoint dyadic.
The off-domain fallback makes this total; the interval recursion always takes
the first branch. Validity of the branch is a proof obligation, not an input. -/
def upperQuery (bits : List Bool) : CubeQuery :=
  let z : ℕ → Bool := fun k => bits[k]?.getD false
  let L := ⌈(216 : ℚ) / searchMargin z bits.length⌉₊
  let phi := searchField z bits.length
  if h : 1 ≤ L ∧ phi ∈ Set.Icc (0 : ℚ) 1 ∧
      ∃ m n : ℕ, phi = (m : ℚ) / 2^n then
    ⟨L, phi, h.1, h.2.1, h.2.2⟩
  else ⟨1, 0, by decide, by norm_num, 0, 0, by norm_num⟩

/-- Number of ones in n independent Bernoulli(p) samples. The parameter below
is precisely the mean of a uniform random-site P measurement. -/
def countLaw (p : ℝ) : ℕ → Measure ℕ
  | 0 => Measure.dirac 0
  | n+1 => (countLaw p n).bind fun c =>
      ENNReal.ofReal p • Measure.dirac (c+1) + ENNReal.ofReal (1-p) • Measure.dirac c

abbrev UpperHistory := List Bool × List CubeQuery

def upperRound (u : Interaction) (beta epsilon delta : ℚ) (h : UpperHistory) :
    Measure UpperHistory :=
  let q := upperQuery h.1
  let n := upperSampleCount epsilon delta h.1.length
  let p := (Matrix.trace (gibbsDensity u q.side q.field beta * magnetization q.side)).re /
    (q.side : ℝ)^3
  Measure.map (fun c : ℕ =>
    (h.1 ++ [decide (n ≤ 2*c)], h.2 ++ List.replicate n q)) (countLaw p n)

def upperSearchLaw (u : Interaction) (beta epsilon delta : ℚ) : ℕ → Measure UpperHistory
  | 0 => Measure.dirac ([], [])
  | k+1 => (upperSearchLaw u beta epsilon delta k).bind (upperRound u beta epsilon delta)

def upperOutputLaw (u : Interaction) (beta epsilon delta : ℚ) : Measure (ℚ × List CubeQuery) :=
  Measure.map (fun h : UpperHistory =>
    (searchOutput (fun k => h.1[k]?.getD false) (searchRounds epsilon), h.2))
    (upperSearchLaw u beta epsilon delta (searchRounds epsilon))

/-- Observable implementation specification for the actual source schedule.
Finite code must realize this law through its charged bit and local quantum
operations. Accuracy, resource and time bounds remain theorem conclusions.
The specification holds even for admissible interactions without a phase promise. -/
def ImplementsUpper (P : LocalProgram) : Prop :=
  ∀ (epsilon delta beta : ℚ),
    0 < epsilon → epsilon ≤ 1/16 → 0 < delta → delta ≤ 1/4 → 0 < beta →
    ∀ u, Admissible u → ∀ E : Set (ℚ × List CubeQuery), MeasurableSet E →
      (⨆ t, programRun P u beta epsilon delta t {r |
        r.halted = true ∧ (r.estimate, r.queries) ∈ E}) = upperOutputLaw u beta epsilon delta E

end GibbsTransition.SizeCopies


