-- Prove2me | Definitions.Def_UniformKServer
-- name    : UniformKServer
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:36.086992+00:00
-- url     : https://prove2.me/theorems/1750fc81-d79f-47d2-9722-8b63e2dca62d
-- statement:
--   A RationalMetric on n points Fin n is a rational-valued distance that is nonnegative, zero exactly between equal points, symmetric, and satisfies the triangle inequality. A configuration of k servers is a map Fin k → Fin n of server positions; serving request r with server j moves server j to r, and costAlong sums the real-valued distances d(s_j, r) of the moves along a history, a list of (request, server) pairs. offlineCost(d,s,w) is the infimum of costAlong over all histories whose requests spell the word w, i.e. the optimal cost with full knowledge of the request sequence. The rest of the block defines an explicit bit-level randomized machine model. A BitTape has a left list, a head cell and a right list of optional bits, with head moves left, stay or right (moving onto unvisited cells gives an empty cell). A BitMachine has finitely many control states, a start state, and work tapes; its transition function reads the control state, the input head, the work-tape heads and one coin bit, and returns the next control state, an input move, a write and a move for each work tape, an optional output bit, and a yield flag. A step does nothing once the machine has yielded; running a machine feeds it a list of coins. Between requests, install replaces only the input tape and clears the output and yield flag, keeping control and work tapes. Instances are encoded in a fixed self-delimiting binary code: natCode writes the bit length in unary, a zero, then the bits low-to-high; rationals are coded by a sign bit, numerator magnitude and denominator; instanceCode concatenates n, k, all n² distances, and the initial server positions (shifted by one), with length L. Machine outputs are read as little-endian numbers. Time budgets are polynomialBudget(c,e,x)=c(x+1)^e, and the budget for request t is that polynomial in L plus ⌈log₂(t+1)⌉. boot runs the machine on the encoded instance for a polynomial in L number of steps with all-zero coins, and each request is processed by installing the code of r+1 and running the machine on an arbitrary coin string of the request budget length. Reachable states are those obtainable from boot by any request and any coin string at every step, covering every binary choice rather than an almost-sure set. The server selected is the output value modulo k, and machineExpectedCost averages, uniformly over all coin strings, the move cost of the selected servers plus the recursive cost of the rest of the request word. UniformAlgorithmClaim is a defined proposition, not a proved theorem: it asserts that there exist one machine M, natural numbers c>0 and e, and a real C>0 such that for all n≥3, 2≤k<n, every rational metric d and every initial configuration s, the boot state has yielded, at every reachable state and every request and coin string the machine yields with output below k, and there is a constant B≥0 such that for every request word w the machine's expected cost is at most C(log(k+1))² times offlineCost(d,s,w) plus B.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniformKServer.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniformKServer.lean; bytes 16..7652
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

   

                                                                               

  
namespace UniformKServer

structure RationalMetric (n : ℕ) where
  distance : Fin n → Fin n → ℚ
  nonneg : ∀ x y, 0 ≤ distance x y
  eq_zero : ∀ x y, distance x y = 0 ↔ x = y
  symm : ∀ x y, distance x y = distance y x
  triangle : ∀ x y z, distance x z ≤ distance x y + distance y z

abbrev Configuration (n k : ℕ) := Fin k → Fin n
abbrev History (n k : ℕ) := List (Fin n × Fin k)

def serve {n k : ℕ} (s : Configuration n k) (r : Fin n) (j : Fin k) :
    Configuration n k := Function.update s j r

def costAlong {n k : ℕ} (d : RationalMetric n) :
    Configuration n k → History n k → ℝ
  | _, [] => 0
  | s, (r, j) :: h => (d.distance (s j) r : ℝ) + costAlong d (serve s r j) h

/-- All finite serving-label choices, knowing the entire request word. -/
noncomputable def offlineCost {n k : ℕ} (d : RationalMetric n) (s : Configuration n k)
    (w : List (Fin n)) : ℝ :=
  sInf {c | ∃ h : History n k, h.map Prod.fst = w ∧ c = costAlong d s h}

inductive HeadMove where
  | left | stay | right
  deriving DecidableEq

structure BitTape where
  left : List (Option Bool)
  head : Option Bool
  right : List (Option Bool)

namespace BitTape

def blank : BitTape := ⟨[], none, []⟩

def ofWord (w : List Bool) : BitTape :=
  match w with
  | [] => blank
  | b :: bs => ⟨[], some b, bs.map some⟩

def shift (T : BitTape) : HeadMove → BitTape
  | .stay => T
  | .left => match T.left with
    | [] => ⟨[], none, T.head :: T.right⟩
    | a :: as => ⟨as, a, T.head :: T.right⟩
  | .right => match T.right with
    | [] => ⟨T.head :: T.left, none, []⟩
    | a :: as => ⟨T.head :: T.left, a, as⟩

end BitTape

structure BitAction (q m : ℕ) where
  control : Fin q
  inputMove : HeadMove
  write : Fin m → Option Bool
  workMove : Fin m → HeadMove
  emit : Option Bool
  yield : Bool

structure BitMachine where
  controls : ℕ
  tapes : ℕ
  start : Fin controls
  transition : Fin controls → Option Bool → (Fin tapes → Option Bool) →
    Bool → BitAction controls tapes

structure MachineState (M : BitMachine) where
  control : Fin M.controls
  input : BitTape
  work : Fin M.tapes → BitTape
  outputRev : List Bool
  yielded : Bool

namespace BitMachine

def initial (M : BitMachine) (input : List Bool) : MachineState M :=
  ⟨M.start, BitTape.ofWord input, fun _ => BitTape.blank, [], false⟩

def step (M : BitMachine) (s : MachineState M) (coin : Bool) : MachineState M :=
  if s.yielded then s else
  let a := M.transition s.control s.input.head (fun i => (s.work i).head) coin
  { control := a.control
    input := s.input.shift a.inputMove
    work := fun i => ({s.work i with head := a.write i}).shift (a.workMove i)
    outputRev := match a.emit with
      | none => s.outputRev
      | some b => b :: s.outputRev
    yielded := a.yield }

def run (M : BitMachine) (s : MachineState M) (coins : List Bool) : MachineState M :=
  coins.foldl M.step s

/-- At a request boundary only the input/output interface is refreshed.
    Work tapes and control retain the complete internal state. -/
def install (M : BitMachine) (s : MachineState M) (input : List Bool) : MachineState M :=
  {s with input := BitTape.ofWord input, outputRev := [], yielded := false}

end BitMachine

/-- Self-delimiting binary code: ℓ ones, a zero, then ℓ low-to-high bits.
    This fixes one standard binary encoding rather than allowing a nonuniform
    advice string to be included in the input. -/
def natCode (a : ℕ) : List Bool :=
  List.replicate a.bits.length true ++ [false] ++ a.bits

def rationalCode (a : ℚ) : List Bool :=
  (a.num < 0) :: (natCode a.num.natAbs ++ natCode a.den)

def instanceCode {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) : List Bool :=
  natCode n ++ natCode k ++
    (List.ofFn fun x : Fin n =>
      (List.ofFn fun y : Fin n => rationalCode (d.distance x y)).flatten).flatten ++
    (List.ofFn fun j : Fin k => natCode ((s j).val + 1)).flatten

def bitValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitValue bs

def outputValue {M : BitMachine} (s : MachineState M) : ℕ :=
  bitValue s.outputRev.reverse

/-- A dominating polynomial; every fixed polynomial nonnegative on natural
    inputs is bounded by one of this form after increasing c and e. -/
def polynomialBudget (c e x : ℕ) : ℕ := c * (x + 1)^e

def requestBudget (c e L t : ℕ) : ℕ :=
  polynomialBudget c e (L + Nat.clog 2 (t + 1))

def boot {n k : ℕ} (M : BitMachine) (c e : ℕ)
    (d : RationalMetric n) (s : Configuration n k) : MachineState M :=
  M.run (M.initial (instanceCode d s))
    (List.replicate (polynomialBudget c e (instanceCode d s).length) false)

def requestStep {n : ℕ} (M : BitMachine) (c e L t : ℕ)
    (s : MachineState M) (r : Fin n)
    (coins : Fin (requestBudget c e L t) → Bool) : MachineState M :=
  M.run (M.install s (natCode (r.val + 1))) (List.ofFn coins)

/-- Reachability includes every binary choice, not merely an almost-sure set.
    The index counts requests already served. -/
inductive Reachable {n k : ℕ} (M : BitMachine) (c e : ℕ)
    (d : RationalMetric n) (s : Configuration n k) : ℕ → MachineState M → Prop
  | boot : Reachable M c e d s 0 (boot M c e d s)
  | next {t z} : Reachable M c e d s t z → (r : Fin n) →
      (bits : Fin (requestBudget c e (instanceCode d s).length (t+1)) → Bool) →
      Reachable M c e d s (t+1)
        (requestStep M c e (instanceCode d s).length (t+1) z r bits)

/-- Modulo makes the semantic recursion total even for unsuccessful machines.
    The main statement separately requires the output to be < k at *every*
    reachable outcome, so no invalid output is accepted or silently repaired. -/
def selectedLabel {M : BitMachine} {k : ℕ} (hk : 0 < k) (s : MachineState M) : Fin k :=
  ⟨outputValue s % k, Nat.mod_lt _ hk⟩

noncomputable def machineExpectedCost {n k : ℕ} (M : BitMachine) (c e L : ℕ)
    (d : RationalMetric n) (hk : 0 < k) :
    ℕ → MachineState M → Configuration n k → List (Fin n) → ℝ
  | _, _, _, [] => 0
  | t, z, s, r :: w =>
      let B := requestBudget c e L (t+1)
      (∑ bits : Fin B → Bool,
        let z' := requestStep M c e L (t+1) z r bits
        let j := selectedLabel hk z'
        (d.distance (s j) r : ℝ) +
          machineExpectedCost M c e L d hk (t+1) z' (serve s r j) w) / (2 : ℝ)^B

/-- Full uniform main objective in the explicit bit model, not a theorem or
    assumption. Machine transition steps are bit operations. Installing the
    standard input and reading/erasing the output adds only O(L + budget)
    charged bit operations, hence is absorbed by a single larger polynomial.
    A single deterministic boot is sufficient for the source construction. -/
def UniformAlgorithmClaim : Prop :=
  ∃ (M : BitMachine) (c e : ℕ) (C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ (n k : ℕ) (hn : 3 ≤ n) (hk : 2 ≤ k) (hkn : k < n)
      (d : RationalMetric n) (s : Configuration n k),
      let L := (instanceCode d s).length
      (boot M c e d s).yielded = true ∧
      (∀ (t : ℕ) (z : MachineState M), Reachable M c e d s t z →
        ∀ (r : Fin n) (bits : Fin (requestBudget c e L (t+1)) → Bool),
          let z' := requestStep M c e L (t+1) z r bits
          z'.yielded = true ∧ outputValue z' < k) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ w : List (Fin n),
        machineExpectedCost M c e L d (by omega) 0 (boot M c e d s) s w ≤
          C * (Real.log (k + 1))^2 * offlineCost d s w + B)



end UniformKServer
end OAI


