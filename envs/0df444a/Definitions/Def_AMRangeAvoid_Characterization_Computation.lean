-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Computation
-- name    : AMRangeAvoid_Characterization_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:44.132546+00:00
-- url     : https://prove2.me/theorems/ad739042-3d48-499b-8106-29c9ff26bf64
-- title:
--   Uniform computation, promise reductions and Arthur–Merlin search
-- statement:
--   A promise problem consists of disjoint YES and NO sets of finite binary strings. A total function is polynomial-time when an actual deterministic Mathlib TM2 machine computes its binary output with a single polynomial clock. A decision many-one reduction preserves both promised sides. The source and target promise sets need not be decidable.
--
--   An Arthur–Merlin verifier has natural-valued rational-coefficient polynomial lengths $R,W$ and a total Boolean predicate $V(x,r,w)$. Its polynomial-time program processes framed triples. It witnesses $\mathrm{prAM}_{1,1/3}$ precisely when it is efficient, every challenge on a YES input admits a response, and on every NO input $x$,
--   $$3\,\bigl|\{r\in\{0,1\}^{R(|x|)}:\exists w\in\{0,1\}^{W(|x|)},\ V(x,r,w)=1\}\bigr|\le 2^{R(|x|)}.$$
--   Rational coefficients retain all natural-valued polynomials without rounding. A search problem specifies its promise, candidate length and relation; existence of solutions is a separate property. Avoid asks for a correctly sized non-image of an ordinary expanding circuit. A many-one reduction to Avoid has two total polynomial-time programs, outputs a circuit with one more output than input on every input, and correctly translates every non-image on promised inputs. Its translator always returns a candidate of the prescribed length, including off the promise. Targeted hitting search promises a NO input and requires one full challenge rejected by every full response. These are independent definitions of the computational notions in the characterization.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), §2 preamble, printed p.9 (PDF p.11); Definitions 2.2 and 2.7, printed p.10 (PDF p.12); §2.2, printed p.11 (PDF p.13); Definition 3.4, printed p.16 (PDF p.18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Circuits
import Definitions.Def_KarpLiptonOM_PromiseProblem

/-! Uniform machine semantics, promise problems and Arthur–Merlin verification.
Li, STOC 2027 submission #502, §2 preamble (printed p.9), Definition 2.2
(printed p.10) and §2.2 (printed pp.10–11). Every machine and polynomial is
chosen before its varying input. No oracle or uninterpreted efficiency predicate occurs.
-/
namespace AMRangeAvoid.Characterization

/-- A genuine deterministic TM2 transducer with a polynomial clock on binary input/output. -/
def PolyTime (f : Bits → Bits) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (fun b : Bits => b) (fun b : Bits => b) f)

/-- The published general pair of disjoint binary-string sets; no AM condition is bundled. -/
abbrev PromiseProblem := KarpLiptonOM.PromiseProblem

/-- Total deterministic many-one reduction, with no test for source promise membership. -/
def PromiseReduces (A B : PromiseProblem) : Prop :=
  ∃ f : Bits → Bits, PolyTime f ∧
    (∀ x ∈ A.yes, f x ∈ B.yes) ∧ (∀ x ∈ A.no, f x ∈ B.no)

/-- A polynomial taking natural values at natural arguments. Rational coefficients
allow integer-valued polynomials such as n(n−1)/2 without rounding or restriction
to nonnegative coefficients. `value` is uniquely fixed by `spec`.
-/
structure LengthPolynomial where
  polynomial : Polynomial ℚ
  value : ℕ → ℕ
  spec : ∀ n, (value n : ℚ) = polynomial.eval (n : ℚ)

/-- Operational predicate and length polynomials; efficiency and correctness are separate. -/
structure AMVerifier where
  random : LengthPolynomial
  response : LengthPolynomial
  run : Bits → Bits → Bits → Bool

/-- Tuples of arbitrary finite strings have fixed self-delimiting binary encodings. -/
def AMVerifier.program (V : AMVerifier) (b : Bits) : Bits :=
  match readFrames 3 b with
  | some ([x, r, w], []) => [V.run x r w]
  | _ => [false]

def AMVerifier.efficient (V : AMVerifier) : Prop := PolyTime V.program

/-- The exact number of challenges that admit at least one response. -/
noncomputable def AMVerifier.answerableCount (V : AMVerifier) (x : Bits) : ℕ :=
  (Finset.univ.filter (fun r : Word (V.random.value x.length) =>
    ∃ w : Word (V.response.value x.length),
      V.run x (wordBits r) (wordBits w) = true)).card

/-- Perfect completeness, and soundness at most 1/3, with Merlin after Arthur. -/
def WitnessesAM (problem : PromiseProblem) (V : AMVerifier) : Prop :=
  V.efficient ∧
    (∀ x ∈ problem.yes, ∀ r : Word (V.random.value x.length),
      ∃ w : Word (V.response.value x.length), V.run x (wordBits r) (wordBits w) = true) ∧
    (∀ x ∈ problem.no, 3 * V.answerableCount x ≤ 2 ^ (V.random.value x.length))

def InPrAM (problem : PromiseProblem) : Prop := ∃ V : AMVerifier, WitnessesAM problem V

/-- Search relation, source promise and the type (length) of a candidate solution.
Existence of solutions is a property, not an axiom of the data. -/
structure SearchProblem where
  promised : Set Bits
  solutionLength : Bits → ℕ
  relation : Bits → Bits → Prop

def SearchProblem.totalOnPromise (A : SearchProblem) : Prop :=
  ∀ x ∈ A.promised, ∃ y, y.length = A.solutionLength x ∧ A.relation x y

/-- Range avoidance itself permits arbitrary positive stretch, Definition 2.7. -/
def Avoid : SearchProblem where
  promised := {b | ∃ C, decodeCircuit b = some C ∧ C.inputs < C.outputs.length}
  solutionLength b := match decodeCircuit b with
    | some C => C.outputs.length
    | none => 0
  relation b y := ∃ C, decodeCircuit b = some C ∧ C.inputs < C.outputs.length ∧
    y.length = C.outputs.length ∧ y ∉ C.image

/-- The source's one-query, one-bit-stretch many-one search reduction.
The translator always has the candidate's type, including on YES inputs.
Only promised source inputs have a correctness guarantee. -/
def SearchReducesToAvoid (A : SearchProblem) : Prop :=
  ∃ f : Bits → Bits, ∃ g : Bits → Bits → Bits,
    PolyTime f ∧
    PolyTime (fun b => match readFrames 2 b with
      | some ([x, y], []) => g x y
      | _ => []) ∧
    (∀ x, ∃ C, decodeCircuit (f x) = some C ∧
      C.outputs.length = C.inputs + 1 ∧
      (∀ y, y.length = C.outputs.length → (g x y).length = A.solutionLength x) ∧
      (∀ y, x ∈ A.promised → y.length = C.outputs.length → y ∉ C.image →
        A.relation x (g x y)))

/-- A single full challenge rejecting every possible Merlin response (Definition 3.4). -/
def TargetedHitting (problem : PromiseProblem) (V : AMVerifier) : SearchProblem where
  promised := problem.no
  solutionLength x := V.random.value x.length
  relation x r := r.length = V.random.value x.length ∧
    ∀ w : Word (V.response.value x.length), V.run x r (wordBits w) = false

end AMRangeAvoid.Characterization


