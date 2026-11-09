-- Prove2me | Definitions.Def_EnumeratingComplexity224_Dichotomy_Machines
-- name    : EnumeratingComplexity224_Dichotomy_Machines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:38.939495+00:00
-- url     : https://prove2.me/theorems/d11a7266-1434-4914-b7e0-58c2d5e7db50
-- title:
--   Effective enumerators, exact-output probability and optimality
-- statement:
--   A program is a finite binary word $p$, with its end distinguishable from either bit. A random tape is $w\in\{0,1\}^{\mathbb N}$. A machine has a finite partial-recursive code, a natural control register and a growing finite set of printed numbers. Each interpreter step either advances a bounded transition computation, updates control, prints a number, reads one random bit, or reads an indexed cell of the padded program or auxiliary input. Input reads return distinct codes for the end marker and the two bits. Divergence leaves the previous output intact.
--
--   The stage output $M^t(p,y,w)$ is the set printed in $t$ interpreter steps; the complete output is
--   $$M(p,y,w)=\bigcup_{t\in\mathbb N}M^t(p,y,w).$$
--   The deterministic interface fixes $y$ empty and all random bits to zero. Its plain enumerating complexity is
--   $$D_M(S)=\inf\{|p|:M(p)=S\}\in\mathbb N\cup\{\infty\},$$
--   with value infinity if no description exists. The probability interface fixes the program empty. Under the infinite product of uniform Boolean measures, it gives
--   $$R_P(S\mid y)=\mu\{w:P(w,y)=S\}.$$
--   Equality refers to the complete output, rather than a finite stage or halting output. Optimal deterministic machines dominate every concrete code up to an additive natural constant; optimal random machines dominate all exact-output probabilities up to a positive real factor. Conditional optimality requires one factor uniform in both $S$ and $y$.
--
--   The auxiliary pair input uses little-endian binary naturals, zero represented by one false bit, and the unary length of the binary representation of $k$, a false delimiter, that representation, then the binary representation of $l$. The padded tape end delimits $l$. This supplies the source's computable self-delimiting convention. These definitions provide the common machine and probability layer for every selected statement.
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 5–6, Definitions 7, 9, 10 and §2 conventions

import Mathlib
import Mathlib.Computability.PartrecCode
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

namespace EnumeratingComplexity224.Dichotomy

abbrev Word := List Bool
abbrev Tape := ℕ → Bool
abbrev Machine := Nat.Partrec.Code

/-- A finite effective interpreter state. The output component is append-only.
`fuel` is a bound for the partial-recursive transition evaluator, not a time bound. -/
structure Configuration where
  control : ℕ := 0
  fuel : ℕ := 0
  head : ℕ := 0
  printed : Finset ℕ := ∅
  deriving Inhabited

/-- The end marker has code 0; bits false and true have codes 1 and 2. -/
def paddedRead (p : Word) (i : ℕ) : ℕ :=
  match p[i]? with
  | none => 0
  | some false => 1
  | some true => 2

/-- A machine code computes an instruction from its natural-valued control register.
Instructions use Nat.unpair: tag 0 updates control, tag 1 emits a number,
tag 2 reads one fresh random bit, tags 3/4 read a padded program/auxiliary cell.
Other tags idle. Divergent transition computations idle forever. -/
def machineStep (m : Machine) (p y : Word) (w : Tape)
    (s : Configuration) : Configuration :=
  match m.evaln (s.fuel + 1) s.control with
  | none => { s with fuel := s.fuel + 1 }
  | some instruction =>
    let tag := instruction.unpair.1
    let data := instruction.unpair.2
    match tag with
    | 0 => { s with control := data, fuel := 0 }
    | 1 => { s with control := data.unpair.2, fuel := 0,
                    printed := insert data.unpair.1 s.printed }
    | 2 => { s with control := Nat.pair data (if w s.head then 1 else 0),
                    fuel := 0, head := s.head + 1 }
    | 3 => { s with control := Nat.pair data.unpair.2 (paddedRead p data.unpair.1),
                    fuel := 0 }
    | 4 => { s with control := Nat.pair data.unpair.2 (paddedRead y data.unpair.1),
                    fuel := 0 }
    | _ => { s with fuel := 0 }

def machineRun (m : Machine) (p y : Word) (w : Tape) : ℕ → Configuration
  | 0 => default
  | t + 1 => machineStep m p y w (machineRun m p y w t)

def stageOutput (m : Machine) (p y : Word) (w : Tape) (t : ℕ) : Finset ℕ :=
  (machineRun m p y w t).printed

def enumerated (m : Machine) (p y : Word) (w : Tape) : Set ℕ :=
  {n | ∃ t, n ∈ stageOutput m p y w t}

/-- Deterministic machines have the random interface tied to the all-zero tape. -/
def deterministicOutput (m : Machine) (p : Word) : Set ℕ :=
  enumerated m p [] (fun _ => false)

/-- Complete-lattice infimum in ℕ ∪ {∞}; an empty description set has value ∞. -/
noncomputable def complexity (m : Machine) (S : Set ℕ) : ℕ∞ :=
  sInf {n | ∃ p : Word, deterministicOutput m p = S ∧ n = (p.length : ℕ∞)}

def OptimalDeterministic (m : Machine) : Prop :=
  ∀ a : Machine, ∃ c : ℕ, ∀ S : Set ℕ,
    complexity m S ≤ complexity a S + c

noncomputable def fairBit : MeasureTheory.Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

noncomputable def tapeMeasure : MeasureTheory.Measure Tape :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => fairBit)

/-- Exact equality to the whole infinite-time output, with no halting test. -/
noncomputable def probability (m : Machine) (S : Set ℕ) (y : Word) : ENNReal :=
  tapeMeasure {w | enumerated m [] y w = S}

def OptimalRandom (m : Machine) : Prop :=
  ∀ a : Machine, ∃ c : ℝ, 0 < c ∧ ∀ S : Set ℕ,
    ENNReal.ofReal c * probability a S [] ≤ probability m S []

def OptimalConditional (m : Machine) : Prop :=
  ∀ a : Machine, ∃ c : ℝ, 0 < c ∧ ∀ (S : Set ℕ) (y : Word),
    ENNReal.ofReal c * probability a S y ≤ probability m S y

/-- Least-significant-bit first binary; zero is the one-bit word [false]. -/
def binary (n : ℕ) : Word :=
  if n = 0 then [false] else (List.range n.size).map n.testBit

/-- Unary length prefix, delimiter, binary k, followed by binary l.
The first component is prefix decodable and the padded end delimits the second. -/
def pairInput (k l : ℕ) : Word :=
  List.replicate (binary k).length true ++ [false] ++ binary k ++ binary l

noncomputable def dyadic (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ k

end EnumeratingComplexity224.Dichotomy


