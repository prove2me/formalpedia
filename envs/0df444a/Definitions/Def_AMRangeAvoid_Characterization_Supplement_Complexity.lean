-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Supplement_Complexity
-- name    : AMRangeAvoid_Characterization_Supplement_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:20:59.359368+00:00
-- url     : https://prove2.me/theorems/a3eba8f6-3158-4c4a-a69c-c9c2ae5e274e
-- title:
--   Operational promise classes and family-specific search
-- statement:
--   A promise problem has disjoint YES and NO subsets of finite binary strings. Promise symmetric polynomial time uses a single uniformly polynomial-time predicate and one fixed polynomial witness length: YES inputs have an existential first witness that works against every second witness, and NO inputs have an existential second witness that forces rejection against every first witness. Promise NP uses an existential polynomial-length certificate. Promise coNP exchanges the promised sides.
--
--   Promise MA has perfect completeness and soundness at most $1/3$, with Merlin's witness chosen before Arthur's random bits. For a total search relation, SearchNP requires at least one accepting branch on every input and a valid output on every accepting branch. Acceptance and output are evaluated by actual polynomial-time Turing machines.
--
--   $$\mathrm{YES}_{S_2}:\exists a\,\forall b\,V(x,a,b)=1,\qquad \mathrm{NO}_{S_2}:\exists b\,\forall a\,V(x,a,b)=0.$$
--
--   The definition also exposes a particular search-reduction pair and its family-specific Avoid relation, retaining the translator's output-length guarantee on all inputs. The finite-program execution predicate counts actual Mathlib stack-machine transitions, observing the output stack at halting while allowing unread input and scratch stacks. This supports the source's early rejection of oversized integer coordinates.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Definitions 2.1, 2.5, §2.2 and §5, printed pp.9–11,24 (PDF pp.11–13,26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Computation

namespace AMRangeAvoid.Characterization.Supplement

/-- Fixed framing, shared by all binary predicates and transducers. -/
def binaryProgram (f : Bits → Bits → Bits) (b : Bits) : Bits :=
  match readFrames 2 b with
  | some ([x, a], []) => f x a
  | _ => []

def ternaryProgram (f : Bits → Bits → Bits → Bool) (b : Bits) : Bits :=
  match readFrames 3 b with
  | some ([x, a, b], []) => [f x a b]
  | _ => [false]

/-- Definition 2.5: one predicate and one common polynomial, chosen before x. -/
def InPromiseS2P (A : PromiseProblem) : Prop :=
  ∃ p : LengthPolynomial, ∃ v : Bits → Bits → Bits → Bool,
    PolyTime (ternaryProgram v) ∧
    (∀ x ∈ A.yes, ∃ a : Word (p.value x.length),
      ∀ b : Word (p.value x.length), v x (wordBits a) (wordBits b) = true) ∧
    (∀ x ∈ A.no, ∃ b : Word (p.value x.length),
      ∀ a : Word (p.value x.length), v x (wordBits a) (wordBits b) = false)

/-- Promise NP; arbitrary strings outside the promise impose no condition. -/
def InPrNP (A : PromiseProblem) : Prop :=
  ∃ p : LengthPolynomial, ∃ v : Bits → Bits → Bool,
    PolyTime (binaryProgram (fun x a => [v x a])) ∧
    (∀ x ∈ A.yes, ∃ a : Word (p.value x.length), v x (wordBits a) = true) ∧
    (∀ x ∈ A.no, ∀ a : Word (p.value x.length), v x (wordBits a) = false)

def complement (A : PromiseProblem) : PromiseProblem :=
  ⟨A.no, A.yes, A.disjoint.symm⟩

def InPrNPCoNP (A : PromiseProblem) : Prop := InPrNP A ∧ InPrNP (complement A)

/-- Definition 2.1: reuse the operational verifier, but its second argument is
Merlin's witness and its third argument is Arthur's random string. -/
noncomputable def maAcceptCount (V : AMVerifier) (x w : Bits) : ℕ :=
  (Finset.univ.filter (fun r : Word (V.random.value x.length) =>
    V.run x w (wordBits r) = true)).card

def WitnessesMA (A : PromiseProblem) (V : AMVerifier) : Prop :=
  V.efficient ∧
    (∀ x ∈ A.yes, ∃ w : Word (V.response.value x.length),
      ∀ r : Word (V.random.value x.length), V.run x (wordBits w) (wordBits r) = true) ∧
    (∀ x ∈ A.no, ∀ w : Word (V.response.value x.length),
      3 * maAcceptCount V x (wordBits w) ≤ 2 ^ V.random.value x.length)

def InPrMA (A : PromiseProblem) : Prop := ∃ V, WitnessesMA A V

/-- A certificate describes a nondeterministic branch. Some branch accepts on
EVERY input, and every accepting branch outputs a solution. Both the acceptance
predicate and output transducer are ordinary uniformly polynomial-time machines. -/
def InSearchNP (R : Bits → Bits → Prop) : Prop :=
  ∃ p : LengthPolynomial, ∃ accept : Bits → Bits → Bool,
    ∃ output : Bits → Bits → Bits,
      PolyTime (binaryProgram (fun x c => [accept x c])) ∧
      PolyTime (binaryProgram output) ∧
      (∀ x, ∃ c : Word (p.value x.length), accept x (wordBits c) = true) ∧
      (∀ x, ∀ c : Word (p.value x.length), accept x (wordBits c) = true →
        R x (output x (wordBits c)))

/-- The actual pair underlying the base existential search-reduction predicate. -/
def IsAvoidReduction (A : SearchProblem) (f : Bits → Bits)
    (g : Bits → Bits → Bits) : Prop :=
  PolyTime f ∧ PolyTime (binaryProgram g) ∧
    ∀ x, ∃ C, decodeCircuit (f x) = some C ∧ C.outputs.length = C.inputs + 1 ∧
      (∀ y, y.length = C.outputs.length → (g x y).length = A.solutionLength x) ∧
      (∀ y, x ∈ A.promised → y.length = C.outputs.length → y ∉ C.image →
        A.relation x (g x y))

/-- Total family-specific relation, including inputs outside the decision promise. -/
def AvoidFamily (f : Bits → Bits) (x y : Bits) : Prop :=
  ∃ C, decodeCircuit (f x) = some C ∧ C.outputs.length = C.inputs + 1 ∧
    y.length = C.outputs.length ∧ y ∉ C.image

/-- Fixed finite Mathlib stack program. A halt can leave unread input and
scratch stacks, as standard early-rejecting algorithms do; only the output stack
is observed. Every transition is counted, with no unit-cost arithmetic. -/
def RunsWithin (M : Turing.TM2ComputableAux Bool Bool) (input output : Bits)
    (time : ℕ) : Prop :=
  ∃ t ≤ time, ∃ c : Turing.TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ,
    (fun z => z.bind M.tm.step)^[t]
        (some (Turing.initList M.tm (input.map M.inputAlphabet.symm))) = some c ∧
      c.l = none ∧ (c.stk M.tm.k₁).map M.outputAlphabet = output

end AMRangeAvoid.Characterization.Supplement


