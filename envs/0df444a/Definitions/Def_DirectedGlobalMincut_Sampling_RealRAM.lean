-- Prove2me | Definitions.Def_DirectedGlobalMincut_Sampling_RealRAM
-- name    : DirectedGlobalMincut_Sampling_RealRAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:52.942956+00:00
-- url     : https://prove2.me/theorems/33e6c159-d95f-4f11-a77c-556dde374b92
-- title:
--   Exact-real randomized programs and charged execution laws
-- statement:
--   A real program is a finite list of elementary RAM instructions, extended by floor and exact Bernoulli sampling. Its registers hold real numbers. It can perform arithmetic, comparisons, indirect memory access, fair coins, or an explicit maximum-flow request. No instruction contains an arbitrary mathematical function. Each elementary operation costs one unit; question and answer copying are also charged.
--
--   Fresh randomness is defined by binding one-step probability mass functions. If $\mu$ is the execution law and $F$ an output coordinate, its mean is
--
--   $$\mathbb E_\mu[F]=\sum_s\mu(s)F(s),$$
--
--   with summability required separately wherever a mean is asserted. Execution bounds require halting, work, number of calls, and the total vertices plus arcs of all queries on every supported outcome. Invalid sampling probabilities are clamped to $[0,1]$ by a total convention. This exact-real interface preserves arbitrary real $q$; it is distinct from the integer word model of the global algorithm.
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Lemma 2.2, Lemma 3.1, Algorithm 1 and Theorem 4.4, pp.2–4,10, p. 4 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_MaxFlow

open scoped ENNReal NNReal

namespace DirectedGlobalMincut.Sampling

/-- An exact-arithmetic extension of the published integer RAM syntax, for arbitrary real q.
Sampling Bernoulli(p) is the standard exact-real sampling primitive. -/
inductive RealInstr where
  | ram (instruction : CongruencyTU.Instr)
  | floor (destination source : ℕ)
  | bernoulli (destination probability : ℕ)
  deriving DecidableEq

abbrev RealProgram := List RealInstr
abbrev RealOracle := List ℝ → List ℝ

structure RealState where
  pc : ℕ
  reg : ℕ → ℝ
  work : ℕ
  questions : List (List ℝ)

noncomputable def realRead (R : ℕ → ℝ) (a len : ℕ) : List ℝ :=
  (List.range len).map (fun i => R (a + 1 + i))

noncomputable def realWrite (R : ℕ → ℝ) (a : ℕ) (xs : List ℝ) : ℕ → ℝ := fun j =>
  if j = a then xs.length else
  if a + 1 ≤ j ∧ j < a + 1 + xs.length then xs.getD (j - (a + 1)) 0 else R j

noncomputable def realInit (I : List ℝ) : RealState :=
  ⟨0, fun j => if j = 0 then I.length else I.getD (j - 1) 0, 0, []⟩

noncomputable def realOutput (s : RealState) : List ℝ := realRead s.reg 0 ⌊s.reg 0⌋₊

noncomputable def realHalted (P : RealProgram) (s : RealState) : Bool :=
  match P[s.pc]? with
  | none => true
  | some (.ram .halt) => true
  | _ => false

noncomputable def RealState.next (s : RealState) (d : ℕ) (x : ℝ) : RealState :=
  { s with reg := Function.update s.reg d x, pc := s.pc + 1, work := s.work + 1 }

/-- Total semantics on invalid probabilities; valid programs use p in [0,1]. -/
noncomputable def coinLaw (p : ℝ) : PMF Bool :=
  PMF.bernoulli ⟨max 0 (min 1 p), le_max_left _ _⟩ (by
    change max 0 (min 1 p) ≤ (1 : ℝ)
    exact max_le (by norm_num) (min_le_left _ _))

/-- Every transition is either one elementary operation or a genuine maximum-flow request.
All construction, input/output copies and oracle-query serialization are charged. -/
noncomputable def realStep (P : RealProgram) (O : RealOracle) (s : RealState) : PMF RealState :=
  match P[s.pc]? with
  | none => PMF.pure s
  | some (.floor d a) => PMF.pure (s.next d (Int.floor (s.reg a)))
  | some (.bernoulli d a) => (coinLaw (s.reg a)).map (fun b => s.next d (if b then 1 else 0))
  | some (.ram .halt) => PMF.pure s
  | some (.ram (.const d v)) => PMF.pure (s.next d v)
  | some (.ram (.copy d a)) => PMF.pure (s.next d (s.reg a))
  | some (.ram (.add d a b)) => PMF.pure (s.next d (s.reg a + s.reg b))
  | some (.ram (.sub d a b)) => PMF.pure (s.next d (s.reg a - s.reg b))
  | some (.ram (.mul d a b)) => PMF.pure (s.next d (s.reg a * s.reg b))
  | some (.ram (.div d a b)) => PMF.pure (s.next d (s.reg a / s.reg b))
  | some (.ram (.mod d a b)) => PMF.pure (s.next d
      (s.reg a - s.reg b * (Int.floor (s.reg a / s.reg b) : ℝ)))
  | some (.ram (.jle a b t)) => PMF.pure
      { s with pc := (if s.reg a ≤ s.reg b then t else s.pc + 1), work := s.work + 1 }
  | some (.ram (.load d a)) => PMF.pure (s.next d (s.reg ⌊s.reg a⌋₊))
  | some (.ram (.store a v)) => PMF.pure (s.next ⌊s.reg a⌋₊ (s.reg v))
  | some (.ram (.coin d)) => (coinLaw (1 / 2)).map (fun b => s.next d (if b then 1 else 0))
  | some (.ram (.query a)) =>
      let xs := realRead s.reg a ⌊s.reg a⌋₊
      let ys := O xs
      PMF.pure { s with reg := realWrite s.reg a ys, pc := s.pc + 1, work := s.work + 1 + xs.length + ys.length, questions := s.questions ++ [xs] }

/-- Monad binding supplies fresh independent randomness at every sampling instruction. -/
noncomputable def realLaw (P : RealProgram) (O : RealOracle) (I : List ℝ) : ℕ → PMF RealState
  | 0 => PMF.pure (realInit I)
  | t + 1 => (realLaw P O I t).bind (realStep P O)

noncomputable def Mean (μ : PMF RealState) (f : RealState → ℝ) : ℝ :=
  ∑' s, (μ s).toReal * f s

def HasMean (μ : PMF RealState) (f : RealState → ℝ) : Prop :=
  Summable (fun s => (μ s).toReal * f s)

noncomputable def queryVolumeR (xs : List ℝ) : ℕ :=
  ⌊xs.getD 0 0⌋₊ + ⌊xs.getD 1 0⌋₊

/-- Complete bounded executions, including all random outcomes in the support. -/
def RealRuns (P : RealProgram) (O : RealOracle) (I : List ℝ) (B calls volume : ℕ) : Prop :=
  ∀ s ∈ (realLaw P O I B).support,
    realHalted P s = true ∧ s.work ≤ B ∧ s.questions.length ≤ calls ∧
      (s.questions.map queryVolumeR).sum ≤ volume ∧
      ∀ xs ∈ s.questions, ∃ Q : MFProblem ℝ, Q.ValidR ∧ xs = Q.encR

noncomputable def softBudget (K : ℝ) (k n m : ℕ) : ℕ :=
  ⌈K * (m + 1) * (Real.log (2 + n)) ^ k⌉₊

noncomputable def linearLogBudget (K : ℝ) (n m : ℕ) : ℕ :=
  ⌈K * (1 + m * Real.log (2 + n))⌉₊

noncomputable def outputSet (m : ℕ) (s : RealState) : Finset (Fin m) :=
  Finset.univ.filter (fun e => s.reg (e.val + 1) = 1)

def MaskOutput (m : ℕ) (s : RealState) : Prop :=
  realOutput s = List.ofFn (fun e : Fin m => if e ∈ outputSet m s then (1 : ℝ) else 0)

end DirectedGlobalMincut.Sampling


