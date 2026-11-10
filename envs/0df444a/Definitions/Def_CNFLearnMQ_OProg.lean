-- Prove2me | Definitions.Def_CNFLearnMQ_OProg
-- name    : CNFLearnMQ_OProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:29.045106+00:00
-- url     : https://prove2.me/theorems/8b3282c8-27a3-4fb2-b132-fc2f208bab54
-- title:
--   Oracle programs with sample and membership-query access, and their cost
-- statement:
--   A learner has **sample access** to $\mu_\Phi$ (each call returns an independent uniform solution of $\Phi$) and **membership-query access** to $\Phi$ (a query on $X$ returns whether $X$ satisfies $\Phi$). A learner is modelled as a program tree with five kinds of nodes: return a value; draw a sample and continue; ask a membership query on an assignment and continue with the answer; flip a coin of a given bias and continue; charge $c$ units of time and continue.
--
--   Running a program with a sample law $\mu$ and an oracle produces a joint distribution of (output, cost), where the cost records three counters: **time**, **samples** and **queries**. A sample adds $n$ to time and $1$ to samples; a query adds $n$ to time and $1$ to queries; a coin adds $1$ to time; a charge node adds $c$ to time. Samples and coins are independent. The module also provides the probability of an event under a law and the law of $N$ independent draws.
--
--   This is a unit-cost operation count: each step of an algorithm is charged at least the size of the data it reads or writes, and reals are unit cost, as in the paper's own accounting.
--
--   **Formalization Note** A program never receives the formula; it learns about $\Phi$ only through the answers of `run`. The number of samples and queries counted by `run` are the real number of oracle calls, so the sample and query complexity cannot be understated. Pure Lean code between oracle calls is free; its time is the explicit charge nodes, whose amounts are part of each algorithm's definition.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Definition 1.1, p.3 (access model); proof of Theorem 5.1, p.36 (accounting)

import Mathlib
import Definitions.Def_CNFLearning873_Valiant_CNF

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- A randomized learner with sample access and membership-query access to an unknown formula on
`n` variables (Feng, Yu, Zhang, STOC 2027 submission (manuscript sha256 519ee6d4…),
Definition 1.1, p.3), written as a program tree:
`sample k` draws one sample and continues with `k`; `query x k` asks whether `x` satisfies the
formula and continues with the answer; `coin p k` flips a coin with bias `p`; `tick c k` charges `c`
units of time for the pure computation it stands for.

**Formalization Note** The program never receives the formula: it can learn about it only through
`sample` and `query`, which `run` answers. Pure Lean code between oracle calls is free; its running
time is accounted for by explicit `tick` charges (see `run`). -/
inductive OProg (n : ℕ) (α : Type) : Type where
  | pure : α → OProg n α
  | sample : (Assignment n → OProg n α) → OProg n α
  | query : Assignment n → (Bool → OProg n α) → OProg n α
  | coin : ℚ → (Bool → OProg n α) → OProg n α
  | tick : ℕ → OProg n α → OProg n α

namespace OProg

variable {n : ℕ}

/-- Sequential composition of programs. -/
def bind {α β : Type} : OProg n α → (α → OProg n β) → OProg n β
  | .pure a, f => f a
  | .sample k, f => .sample fun x => bind (k x) f
  | .query x k, f => .query x fun b => bind (k b) f
  | .coin p k, f => .coin p fun b => bind (k b) f
  | .tick c k, f => .tick c (bind k f)

instance : Monad (OProg n) where
  pure := OProg.pure
  bind := OProg.bind

/-- Draw one sample. -/
def draw : OProg n (Assignment n) := .sample .pure

/-- Ask one membership query. -/
def ask (x : Assignment n) : OProg n Bool := .query x .pure

/-- Flip one coin with bias `p`. -/
def bern (p : ℚ) : OProg n Bool := .coin p .pure

/-- Charge `c` units of time. -/
def charge (c : ℕ) : OProg n Unit := .tick c (.pure ())

/-- Draw `N` samples, in order. -/
def drawList : ℕ → OProg n (List (Assignment n))
  | 0 => .pure []
  | N + 1 => .sample fun x => bind (drawList N) fun xs => .pure (x :: xs)

end OProg

/-- The resources used by one execution: running time, number of samples drawn and number of
membership queries asked. -/
structure Cost where
  time : ℕ
  samples : ℕ
  queries : ℕ

namespace Cost

instance : Zero Cost := ⟨⟨0, 0, 0⟩⟩

instance : Add Cost := ⟨fun a b => ⟨a.time + b.time, a.samples + b.samples, a.queries + b.queries⟩⟩

end Cost

/-- A coin of bias `p`, clamped to `[0, 1]`: `true` with probability `min 1 (max 0 p)`. -/
noncomputable def coinPMF (p : ℚ) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then min 1 (max 0 (p : ℝ))
      else 1 - min 1 (max 0 (p : ℝ))))
    (by
      have h0 : 0 ≤ min 1 (max 0 (p : ℝ)) := le_min zero_le_one (le_max_left _ _)
      have h1 : min 1 (max 0 (p : ℝ)) ≤ 1 := min_le_left _ _
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [← ENNReal.ofReal_add h0 (by linarith)]
      simp)

/-- Add `c` to the cost component of an outcome. -/
def addCost {α : Type} (c : Cost) (o : α × Cost) : α × Cost := (o.1, c + o.2)

/-- The joint law of (output, cost) of a program run with sample law `μ` and membership oracle
`oracle`.

Charges (the unit-cost convention of the sister mission's published
`CNFLearning873_Valiant_Execution`): a sample costs time `n` (writing down an assignment) and one
sample; a membership query costs time `n` (writing down the queried assignment) and one query; a
coin costs time `1`; `tick c` costs time `c`. Samples are independent draws from `μ` and coins are
independent of everything else. -/
noncomputable def run {n : ℕ} {α : Type} (μ : PMF (Assignment n)) (oracle : Assignment n → Bool) :
    OProg n α → PMF (α × Cost)
  | .pure a => PMF.pure (a, 0)
  | .sample k => μ.bind fun x => (run μ oracle (k x)).map (addCost ⟨n, 1, 0⟩)
  | .query x k => (run μ oracle (k (oracle x))).map (addCost ⟨n, 0, 1⟩)
  | .coin p k => (coinPMF p).bind fun b => (run μ oracle (k b)).map (addCost ⟨1, 0, 0⟩)
  | .tick c k => (run μ oracle k).map (addCost ⟨c, 0, 0⟩)

/-- The probability of an event under a law. -/
noncomputable def prob {α : Type} (D : PMF α) (E : α → Prop) : ENNReal :=
  D.toOuterMeasure {a | E a}

/-- The law of `N` independent draws from `μ`, as a list. -/
noncomputable def iidList {β : Type} (μ : PMF β) : ℕ → PMF (List β)
  | 0 => PMF.pure []
  | N + 1 => μ.bind fun x => (iidList μ N).map (x :: ·)

end CNFLearnMQ


