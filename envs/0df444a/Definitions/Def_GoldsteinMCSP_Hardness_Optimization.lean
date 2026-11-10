-- Prove2me | Definitions.Def_GoldsteinMCSP_Hardness_Optimization
-- name    : GoldsteinMCSP_Hardness_Optimization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:12:15.896735+00:00
-- url     : https://prove2.me/theorems/65c979fe-06ce-4fd0-87b2-b793a6746a0b
-- title:
--   Encoded NPO problems, APX and uniform PTAS-preserving reductions
-- statement:
--   An encoded optimization problem consists of a Boolean input-validity test, a Boolean feasibility test on input and solution words, a natural-number objective, and a choice of minimization or maximization. These data contain no assumed complexity certificates. NPO is the predicate requiring actual finite-alphabet polynomial-time machines for validity, feasibility and the binary objective, a polynomial bound on every feasible witness length, and a feasible solution for every valid input.
--
--   A feasible solution is within factor r when its cost is at most r times every feasible cost for minimization, or r times its value is at least every feasible value for maximization. On NPO problems these comparisons are equivalent to the attained optimum inequalities, including optimum zero. APX requires NPO and a single polynomial-time algorithm with one instance-independent constant approximation factor.
--
--   A PTAS-preserving reduction has an instance map, a solution map and a computable positive rational accuracy transfer independent of the instance. Each of the two maps has one finite-alphabet Turing machine accepting accuracy together with data. For each fixed accuracy that same machine has a polynomial running-time bound in data length. Valid instances map to valid instances, every feasible target solution decodes to a feasible source solution, and every target solution within transferred factor 1+δ decodes within factor 1+ε. APX-hardness requires target NPO membership and a reduction from every APX problem, for either objective direction. The definitions use the published polynomial-time predicate and Mathlib TM2 execution semantics.
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Theorem 2.1, printed/PDF p. 6; uniform bit-machine convention for the standard complexity classes

import Definitions.Def_Grunbaum2003_ContainmentPolyTime
import Definitions.Def_GoldsteinMCSP_Hardness_Encoding

namespace GoldsteinMCSP.Hardness

/-- General encoded optimization data; contains no correctness or hardness certificates. -/
structure OptimizationProblem where
  valid : Bits → Bool
  feasible : Bits → Bits → Bool
  value : Bits → Bits → ℕ
  maximize : Bool

/-- Uniform finite-alphabet computability, with no time bound. -/
def machineComputable (f : Bits → Bits) : Prop :=
  ∃ M : Turing.TM2Computable id id f, ∀ k, Finite (M.tm.Γ k)

/-- One machine takes the accuracy and data together. Its running time on each fixed
accuracy slice is polynomial in the data length; the machine itself never changes. -/
def accuracyPolyTime (f : Accuracy → Bits → Bits) : Prop :=
  ∃ M : Turing.TM2Computable id id (onAccuracy f),
    (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ e : Accuracy, ∃ b : Polynomial ℕ, ∀ x : Bits,
      Nonempty (Turing.TM2OutputsInTime M.tm
        ((pairBits (encodeAccuracy e) x).map M.inputAlphabet.invFun)
        (some ((f e x).map M.outputAlphabet.invFun)) (b.eval x.length))

/-- NPO: polynomial validity, feasibility and value, polynomial witnesses, and feasibility. -/
def IsNPO (p : OptimizationProblem) : Prop :=
  Grunbaum2003.ContainmentPolyTime (fun x => [p.valid x]) ∧
  Grunbaum2003.ContainmentPolyTime (onPair fun x y => [p.feasible x y]) ∧
  Grunbaum2003.ContainmentPolyTime (onPair fun x y => encodeNat (p.value x y)) ∧
  (∃ b : Polynomial ℕ, ∀ x y, p.valid x = true → p.feasible x y = true →
    y.length ≤ b.eval x.length) ∧
  (∀ x, p.valid x = true → ∃ y, p.feasible x y = true)

/-- Comparison with every feasible value equals comparison with the attained optimum in NPO.
Multiplication, rather than division by OPT, handles optimum zero. -/
def withinFactor (p : OptimizationProblem) (r : ℚ) (x y : Bits) : Prop :=
  p.feasible x y = true ∧ ∀ z, p.feasible x z = true →
    if p.maximize then (p.value x z : ℚ) ≤ r * p.value x y
    else (p.value x y : ℚ) ≤ r * p.value x z

def InAPX (p : OptimizationProblem) : Prop :=
  IsNPO p ∧ ∃ (a : Bits → Bits) (c : ℕ), 1 ≤ c ∧
    Grunbaum2003.ContainmentPolyTime a ∧
    ∀ x, p.valid x = true → withinFactor p c x (a x)

/-- PTAS-preserving reductions: one computable accuracy transfer and uniform machines,
with polynomial running time for each fixed positive rational source accuracy. -/
def PTASReducible (p q : OptimizationProblem) : Prop :=
  ∃ (f : Accuracy → Bits → Bits) (g : Accuracy → Bits → Bits → Bits)
    (δ : Accuracy → Accuracy),
    accuracyPolyTime f ∧
    accuracyPolyTime (fun e => onPair (g e)) ∧
    machineComputable (fun w => match decodeAccuracy w with
      | some e => encodeAccuracy (δ e)
      | none => []) ∧
    (∀ e x, p.valid x = true → q.valid (f e x) = true) ∧
    (∀ e x y, p.valid x = true → q.feasible (f e x) y = true →
      p.feasible x (g e x y) = true) ∧
    (∀ e x y, p.valid x = true →
      withinFactor q (1 + accuracyValue (δ e)) (f e x) y →
      withinFactor p (1 + accuracyValue e) x (g e x y))

def APXHard (q : OptimizationProblem) : Prop :=
  IsNPO q ∧ ∀ p : OptimizationProblem, InAPX p → PTASReducible p q

end GoldsteinMCSP.Hardness


