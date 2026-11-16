-- Prove2me | Definitions.Def_QTolTest1673_Unified_Supplement_Partitions
-- name    : QTolTest1673_Unified_Supplement_Partitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:18:24.560882+00:00
-- url     : https://prove2.me/theorems/815ce08c-9320-4eaf-8a28-f3e7cf74b3a7
-- title:
--   Hidden partitions and complete classical trace laws
-- statement:
--   A labelled partition maps each input to its block label; a block-constant function has equal values on inputs with the same label. The YES oracle is obtained by sampling the partition and giving its labels independent uniform signs; the NO oracle assigns independent uniform signs to the inputs. Unused labels have no effect.
--
--   The complete trace law preserves the list of queries and answers when an algorithm halts and also records its optional output. Its total variation is the supremum of the absolute differences on trace events. A collision requires two distinct queried inputs with the same block label; repeated queries do not count. The collision probability uses the NO trace and an independently drawn partition.
--
--   These constructions expose the two distributions and their coupling target in Lemma 4.1. At a budget of $q$, traces are evaluated after $q+1$ actions so the final halt is included; the theorem's uniform query bound ensures that the run has then halted. The measurable space on traces is discrete. Every distribution on partitions of the finite input set has a finite labelled representation. The definition also supports unequal block sizes; Lemma 4.3 imposes the exact sizes it needs.
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, §4.1–4.2 pp.21–23

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Model

noncomputable section
open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum

namespace QTolTest1673.Unified.Supplement

/-- A partition into b labelled blocks; labels need not be used in this general interface. -/
abbrev Partition (n b : ℕ) := V n → Fin b

def partitionClass {n b : ℕ} (P : Partition n b) : Set (BoolFn n) :=
  {f | ∀ x y, P x = P y → f x = f y}

/-- §4.1, p.21: give every block an independent uniform bit. -/
def blockOracle {n b : ℕ} (P : Partition n b) : PMF (BoolFn n) :=
  (PMF.uniformOfFintype (Fin b → Bool)).map fun v x => v (P x)

/-- Hidden-partition YES law, before the algorithm is run. All finite partition laws are allowed. -/
def yesOracle {n b : ℕ} (law : PMF (Partition n b)) : PMF (BoolFn n) :=
  law.bind blockOracle

/-- Full trace, retaining queries and answers even after halting. The optional output records halt. -/
def traceLaw {n : ℕ} (A : CAlg n) (f : BoolFn n) :
    ℕ → PMF (List (V n × Bool) × Option Bool)
  | 0 => PMF.pure ([],none)
  | t+1 => (traceLaw A f t).bind fun st =>
      match st.2 with
      | some _ => PMF.pure st
      | none => (A.step st.1).map fun action =>
          match action with
          | .inl x => (st.1 ++ [(x,f x)], none)
          | .inr y => (st.1, some y)

/-- Probability of a trace event for a randomly sampled fixed oracle. -/
def traceEvent {n : ℕ} (A : CAlg n) (D : PMF (BoolFn n)) (q : ℕ)
    (E : Set (List (V n × Bool) × Option Bool)) : ℝ :=
  letI : MeasurableSpace (List (V n × Bool) × Option Bool) := ⊤
  ∑ f, (D f).toReal * ((traceLaw A f (q+1)).toMeasure E).toReal

/-- Total variation via all trace events, as on p.21; values lie in [0,1]. -/
def traceTV {n : ℕ} (A : CAlg n) (D E : PMF (BoolFn n)) (q : ℕ) : ℝ :=
  sSup {r | ∃ B : Set (List (V n × Bool) × Option Bool),
    r = |traceEvent A D q B - traceEvent A E q B|}

def collides {n b : ℕ} (P : Partition n b) (tr : List (V n × Bool)) : Prop :=
  ∃ x y : V n, x ≠ y ∧ x ∈ tr.map Prod.fst ∧ y ∈ tr.map Prod.fst ∧ P x = P y

/-- NO trace sampled first; the hidden partition is sampled independently afterward. -/
def collisionProb {n b : ℕ} (A : CAlg n) (law : PMF (Partition n b)) (q : ℕ) : ℝ :=
  ∑ P, (law P).toReal * traceEvent A (PMF.uniformOfFintype (BoolFn n)) q
    {st | collides P st.1}

end QTolTest1673.Unified.Supplement


