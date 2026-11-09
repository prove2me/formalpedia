-- Prove2me | Definitions.Def_DirectedGlobalMincut_Sampling_IntegerReduction
-- name    : DirectedGlobalMincut_Sampling_IntegerReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:05.916854+00:00
-- url     : https://prove2.me/theorems/2788dc18-d969-4b38-b063-eb7cd94962c5
-- title:
--   Uniform integer reduction and actual max-flow solver substitution
-- statement:
--   The global computation uses the published finite integer RAM with fair coins, an explicit input edge list, and one bit per vertex in the returned cut mask. Query volume counts both vertices and arcs. Word bounds limit all registers to a constant times $1+\log_2(2+n)$ bits. Every query must encode maximum flow with integral capacities bounded by a fixed polynomial of its own instance size.
--
--   The full reduction target requires, uniformly over admissible graphs,
--
--   $$\Pr[\text{exact global cut}]\ge1-n^{-a},\qquad
--   \text{work},\ \text{aggregate query size}\le\left\lceil K m\log^k(2+n)\right\rceil.$$
--
--   All random outcomes halt with a valid cut. The standalone target existentially establishes a deterministic, oracle-free almost-linear max-flow program. A two-procedure execution suspends the reduction at each query, runs that program on the actual query, copies the answer back, and charges every executed operation and copy. A quadratic observation clock bounds all runs, while actual executed work satisfies $K_\varepsilon m^{1+\varepsilon}$ for every $\varepsilon>0$ above a uniform threshold; halted states do no work. All caller and callee words remain logarithmic in the original graph size.
--
--   The separately defined external rooted-approximation contract uses the ratio $5/4$, $O(\log^4 n)$ linear-size max-flow calls, near-linear additional work and arbitrary inverse-polynomial confidence. These are propositions to establish with actual programs, not facts supplied by an input structure. First-halting output specifies a deterministic solver's mathematical oracle; the standalone operational execution never evaluates a first-halting search as a primitive.
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Theorem 1.1 and following consequence, p.1; unnumbered external approximation contract, p.3, p. 1 (PDF p. 1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_MaxFlow

namespace DirectedGlobalMincut.Sampling

/-- These are the actual published integer RAM programs, not arbitrary functions with assigned costs. -/
abbrev IntegerProgram := CongruencyTU.Program

def NoQueries (P : IntegerProgram) : Prop := ∀ a, CongruencyTU.Instr.query a ∉ P

def NoCoins (P : IntegerProgram) : Prop := ∀ d, CongruencyTU.Instr.coin d ∉ P

def encGlobal {n m : ℕ} (G : Graph n m) (W : ℕ) (w : Fin m → ℕ) : List ℤ :=
  encGraphI G ++ [(W : ℤ)] ++ List.ofFn (fun e => (w e : ℤ))

noncomputable def integerCut (n : ℕ) (xs : List ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => xs.getD v.val 0 = 1)

def cutEncoding {n : ℕ} (S : Finset (Fin n)) : List ℤ :=
  List.ofFn (fun v => if v ∈ S then 1 else 0)

/-- Query volume counts vertices and arcs, including isolated vertices. -/
def queryVolumeI (xs : List ℤ) : ℕ := (xs.getD 0 0).toNat + (xs.getD 1 0).toNat

noncomputable def integerVolume (P : IntegerProgram) (O : CongruencyTU.Oracle)
    (c : ℕ → Bool) (I : List ℤ) (B : ℕ) : ℕ :=
  ∑ t ∈ Finset.range B, match CongruencyTU.queryAt P O c I t with
    | none => 0
    | some xs => queryVolumeI xs

/-- Word width is logarithmic in the original input graph size, with a uniform multiplier. -/
def WordBound (P : IntegerProgram) (O : CongruencyTU.Oracle) (c : ℕ → Bool)
    (I : List ℤ) (B scale width : ℕ) : Prop :=
  ∀ t ≤ B, ∀ j, Nat.size ((CongruencyTU.run P O c I t).reg j).natAbs ≤
    width * (1 + Nat.log2 (2 + scale))

/-- All queries really encode maximum flow, with polynomially bounded integral capacities.
The bound relative to their own instance size allows genuine solver substitution. -/
def IntegralQuestions (P : IntegerProgram) (O : CongruencyTU.Oracle) (c : ℕ → Bool)
    (I : List ℤ) (B exponent : ℕ) : Prop :=
  ∀ t < B, ∀ xs, CongruencyTU.queryAt P O c I t = some xs →
    ∃ Q : MFProblem ℕ, Q.ValidI ∧ xs = Q.encI ∧
      ∀ e, Q.capacity e ≤ (Q.n + Q.m + 2) ^ exponent

noncomputable def reductionClock (K : ℝ) (k n m : ℕ) : ℕ :=
  ⌈K * m * (Real.log (2 + n)) ^ k⌉₊

noncomputable def successFraction (B : ℕ) (Good : (ℕ → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun c : Fin B → Bool => Good (CongruencyTU.extendCoins c))).card : ℝ) / 2 ^ B

/-- Full reduction contract, quantified uniformly over input graphs by the theorem.
All random outcomes terminate with a valid cut; optimality alone is probabilistic. -/
def ReductionCorrect (P : IntegerProgram) (K : ℝ) (k width exponent a : ℕ)
    {n m : ℕ} (G : Graph n m) (W : ℕ) (w : Fin m → ℕ) : Prop :=
  let I := encGlobal G W w
  let B := reductionClock K k n m
  (∀ O, IsMFOracleI O → ∀ c,
    CongruencyTU.isHalted P (CongruencyTU.run P O c I B) = true ∧
    (CongruencyTU.run P O c I B).cost ≤ B ∧ integerVolume P O c I B ≤ B ∧
    WordBound P O c I B n width ∧ IntegralQuestions P O c I B exponent ∧
    ∃ S : Finset (Fin n), IsCut S ∧ CongruencyTU.outputAfter P O c I B = cutEncoding S) ∧
  ∀ O, IsMFOracleI O →
    1 - 1 / (n : ℝ) ^ a ≤ successFraction B (fun c =>
      IsMinimumCut G (fun e => (w e : ℝ))
        (integerCut n (CongruencyTU.outputAfter P O c I B)))

/-- First-halting operational output. Failure to halt is given the empty output, and is separately
excluded by the solver contract. -/
noncomputable def solverOutput (S : IntegerProgram) (I : List ℤ) : List ℤ := by
  classical
  exact if h : ∃ t, CongruencyTU.isHalted S
      (CongruencyTU.run S CongruencyTU.noOracle CongruencyTU.noCoins I t) = true then
    CongruencyTU.outputAfter S CongruencyTU.noOracle CongruencyTU.noCoins I (Nat.find h)
  else []

/-- The cited deterministic almost-linear solver is an existential conclusion, never an assumption
on the mincut input. A single finite program works for all accuracy exponents. -/
def FastMaximumFlow (S : IntegerProgram) : Prop :=
  NoQueries S ∧ NoCoins S ∧ IsMFOracleI (solverOutput S) ∧
  (∀ Q : MFProblem ℕ, Q.ValidI → ∃ t, CongruencyTU.isHalted S
    (CongruencyTU.run S CongruencyTU.noOracle CongruencyTU.noCoins Q.encI t) = true) ∧
  ∀ b : ℕ, 1 ≤ b → ∃ width : ℕ, ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
    ∀ Q : MFProblem ℕ, Q.ValidI → N ≤ Q.n + Q.m →
      (∀ e, Q.capacity e ≤ (Q.n + Q.m + 2) ^ b) →
      let B := ⌈K * (Q.n + Q.m + 2 : ℝ) ^ (1 + ε)⌉₊
      CongruencyTU.isHalted S
        (CongruencyTU.run S CongruencyTU.noOracle CongruencyTU.noCoins Q.encI B) = true ∧
      (CongruencyTU.run S CongruencyTU.noOracle CongruencyTU.noCoins Q.encI B).cost ≤ B ∧
      WordBound S CongruencyTU.noOracle CongruencyTU.noCoins Q.encI B (Q.n + Q.m) width

/-- Two-procedure RAM state. A max-flow query suspends the caller and enters the actual solver.
No optimization oracle is present in this operational execution. -/
structure SubstitutionState where
  caller : CongruencyTU.State
  callee : Option (ℕ × CongruencyTU.State)
  totalWork : ℕ

/-- Input copying is charged on call; answer copying is charged on return. -/
def substitutionStep (P S : IntegerProgram) (c : ℕ → Bool) (z : SubstitutionState) : SubstitutionState :=
  match z.callee with
  | some (a, u) =>
      if CongruencyTU.isHalted S u then
        let ys := CongruencyTU.outputOf u
        { caller := { z.caller with reg := CongruencyTU.writeBlock z.caller.reg a ys, pc := z.caller.pc + 1, queries := z.caller.queries + 1 }, callee := none, totalWork := z.totalWork + 1 + ys.length }
      else
        let v := CongruencyTU.step S CongruencyTU.noOracle CongruencyTU.noCoins u
        { z with callee := some (a, v), totalWork := z.totalWork + (v.cost - u.cost) }
  | none =>
      match P[z.caller.pc]? with
      | some (.query a) =>
          let xs := CongruencyTU.readBlock z.caller.reg a (z.caller.reg a).toNat
          { z with callee := some (a, CongruencyTU.initState xs), totalWork := z.totalWork + 1 + xs.length }
      | _ =>
          let v := CongruencyTU.step P CongruencyTU.noOracle c z.caller
          { z with caller := v, totalWork := z.totalWork + (v.cost - z.caller.cost) }

def substitutionRun (P S : IntegerProgram) (c : ℕ → Bool) (I : List ℤ) : ℕ → SubstitutionState
  | 0 => ⟨CongruencyTU.initState I, none, 0⟩
  | t + 1 => substitutionStep P S c (substitutionRun P S c I t)

def substitutionHalted (P : IntegerProgram) (z : SubstitutionState) : Bool :=
  z.callee.isNone && CongruencyTU.isHalted P z.caller

/-- The composed execution also stays in logarithmic-width words. -/
def SubstitutionWords (P S : IntegerProgram) (c : ℕ → Bool) (I : List ℤ)
    (B scale width : ℕ) : Prop :=
  ∀ t ≤ B, ∀ j,
    Nat.size ((substitutionRun P S c I t).caller.reg j).natAbs ≤
      width * (1 + Nat.log2 (2 + scale)) ∧
    ∀ a u, (substitutionRun P S c I t).callee = some (a, u) →
      Nat.size (u.reg j).natAbs ≤ width * (1 + Nat.log2 (2 + scale))

/-- A quadratic clock bounds all executions, including small inputs. The actual executed cost has
an m^(1+ε) bound for every ε>0; the clock is not counted as executed work after halting. -/
noncomputable def standaloneClock (K : ℝ) (m : ℕ) : ℕ := ⌈K * (m + 1 : ℝ) ^ 2⌉₊

def SubstitutionCorrect (P S : IntegerProgram) (K0 K : ℝ) (k a width : ℕ)
    {n m : ℕ} (G : Graph n m) (W : ℕ) (w : Fin m → ℕ) : Prop :=
  let I := encGlobal G W w
  let B := standaloneClock K0 m
  (∀ c, substitutionHalted P (substitutionRun P S c I B) = true ∧
    (substitutionRun P S c I B).totalWork ≤ B ∧
    SubstitutionWords P S c I B n width ∧
    CongruencyTU.outputOf (substitutionRun P S c I B).caller =
      CongruencyTU.outputAfter P (solverOutput S) c I (reductionClock K k n m)) ∧
  1 - 1 / (n : ℝ) ^ a ≤ successFraction B (fun c =>
    IsMinimumCut G (fun e => (w e : ℝ))
      (integerCut n (CongruencyTU.outputOf (substitutionRun P S c I B).caller)))

/-- The genuine external approximation contract cited on p.3. The witness x and the optimum
are not inputs. All random outcomes return a rooted cut, and its approximation ratio holds w.h.p. -/
def RootedApproximationTarget : Prop :=
  ∀ b a : ℕ, 1 ≤ b → 1 ≤ a →
    ∃ (P : IntegerProgram) (K : ℝ) (k width exponent : ℕ), 0 < K ∧
    ∀ n m (G : Graph n m) W w (r : Fin n), InputDomain b G W w →
      let I := encGlobal G W w ++ [(r.val : ℤ)]
      let B := reductionClock K k n m
      (∀ O, IsMFOracleI O → ∀ c,
        let z := CongruencyTU.run P O c I B
        CongruencyTU.isHalted P z = true ∧ z.cost ≤ B ∧
        z.queries ≤ ⌈K * (Real.log (2 + n)) ^ 4⌉₊ ∧
        WordBound P O c I B n width ∧ IntegralQuestions P O c I B exponent ∧
        (∀ t < B, ∀ xs, CongruencyTU.queryAt P O c I t = some xs →
          queryVolumeI xs ≤ ⌈K * m⌉₊) ∧
        ∃ U, IsRootedCut r U ∧ CongruencyTU.outputOf z = cutEncoding U) ∧
      ∀ O, IsMFOracleI O →
        1 - 1 / (n : ℝ) ^ a ≤ successFraction B (fun c =>
          let U := integerCut n (CongruencyTU.outputAfter P O c I B)
          ∀ X, IsRootedCut r X →
            cutWeight G (fun e => (w e : ℝ)) U ≤
              (5 / 4 : ℝ) * cutWeight G (fun e => (w e : ℝ)) X)

/-- Uniform near-linear reduction AND the standalone consequence, with an actual solver call stack. -/
def FullMincutTarget : Prop :=
  ∃ S : IntegerProgram, FastMaximumFlow S ∧
  ∀ b a : ℕ, 1 ≤ b → 1 ≤ a →
    ∃ (P : IntegerProgram) (K K0 : ℝ) (k width exponent : ℕ),
      0 < K ∧ 0 < K0 ∧
      (∀ n m (G : Graph n m) W w, InputDomain b G W w →
        ReductionCorrect P K k width exponent a G W w ∧
        SubstitutionCorrect P S K0 K k a width G W w) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ n m (G : Graph n m) W w, InputDomain b G W w → N ≤ m →
          ∀ c, (substitutionRun P S c (encGlobal G W w) (standaloneClock K0 m)).totalWork ≤
            C * (m : ℝ) ^ (1 + ε)

end DirectedGlobalMincut.Sampling


