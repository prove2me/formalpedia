-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
-- name    : OAI_Combinatorics_GraphThreshold_AdaptiveTrials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:24:42.632165+00:00
-- url     : https://prove2.me/theorems/6c5acc85-b04c-475f-92fb-6306e277bade
-- title:
--   Adaptive runs, failure counts and rank failures for sequences of independent draws
-- statement:
--   This file sets up the bookkeeping for an adaptive random process driven by finitely many independent draws, in which the outcome of each attempt may depend on the entire current state.
--
--   Throughout, $\Omega$ is a finite set of possible draws and $\mathcal S$ is an arbitrary set of states. A *finite law* $\mu$ on $\Omega$ is a weight function $\mu:\Omega\to\mathbb{R}$ with $\mu(\omega)\ge0$ for all $\omega$ and $\sum_{\omega\in\Omega}\mu(\omega)=1$. Its $n$-fold independent power $\mu^{\otimes n}$ is the finite law on sequences $(\omega_0,\dots,\omega_{n-1})\in\Omega^n$ with weight $\prod_{i<n}\mu(\omega_i)$. A *step map* $\mathrm{step}:\mathcal S\times\Omega\to\mathcal S$ updates the current state with one draw.
--
--   1. **Head–tail splitting.** The bijection $\Omega\times\Omega^{n}\to\Omega^{n+1}$, $(\omega,(\omega_0,\dots,\omega_{n-1}))\mapsto(\omega,\omega_0,\dots,\omega_{n-1})$, whose inverse sends a sequence to its first draw and the sequence of the remaining draws. The accompanying identity says that the product weight factors along this split:
--   $$\mu^{\otimes(n+1)}(\omega,\omega_0,\dots,\omega_{n-1})=\mu(\omega)\,\mu^{\otimes n}(\omega_0,\dots,\omega_{n-1}).$$
--   2. **Adaptive run.** $\mathrm{run}_n(s,\cdot)$ is the state reached from the initial state $s$ by feeding the draws in order:
--   $$\mathrm{run}_0(s,\cdot)=s,\qquad \mathrm{run}_{n+1}\big(s,(\omega_0,\dots,\omega_n)\big)=\mathrm{run}_n\big(\mathrm{step}(s,\omega_0),(\omega_1,\dots,\omega_n)\big).$$
--   3. **Adaptive failure count.** Given in addition a Boolean predicate $\mathrm{bad}(s,\omega)$ (the attempt with draw $\omega$ from state $s$ fails), the number of failures along the actual trajectory is $N_0=0$ and
--   $$N_{n+1}\big(s,(\omega_0,\dots,\omega_n)\big)=\mathbf 1[\mathrm{bad}(s,\omega_0)]+N_n\big(\mathrm{step}(s,\omega_0),(\omega_1,\dots,\omega_n)\big).$$
--   Equivalently, with $s_0=s$ and $s_{i+1}=\mathrm{step}(s_i,\omega_i)$, one has $N_n=\#\{i<n:\ \mathrm{bad}(s_i,\omega_i)\}$.
--   4. **Rank failure.** Given a rank function $r:\mathcal S\to\mathbb N$, the attempt with draw $\omega$ from state $s$ is declared a failure exactly when the rank is not yet zero and does not strictly decrease:
--   $$\mathrm{rankFail}(s,\omega)\iff r(s)\neq0\ \text{ and }\ r\big(\mathrm{step}(s,\omega)\big)\ge r(s).$$
--   Once the rank is zero, every later draw counts as a success.
--
--   Only the draws are independent; no independence is assumed between the success indicators of different attempts, which may depend on the whole state produced by the earlier draws. These objects are the setting for completion estimates of adaptive processes: a uniform bound on the per-state failure probability controls the expectation of $N_n$ under $\mu^{\otimes n}$, and with the rank-failure predicate this yields bounds on the probability that a non-increasing rank reaches zero within a prescribed number of draws.
--
--   **Formalization Note** Draw sequences are functions `Fin n → Ω`, and `bad` is `Bool`-valued. The objects are `trialSplitEquiv`, `adaptiveRun`, `adaptiveFailureCount` and `rankFailure`; the weight identity is the simp lemma `FiniteLaw.iid_weight_cons`. The state type is arbitrary (not assumed finite).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling

namespace OAI

/-!
# Finite adaptive trials

The draws are independent, but whether an attempt succeeds may depend on the
entire current state. The head-tail identity below performs the conditioning
explicitly. No independence assumption is made about success indicators.
-/

noncomputable section
open scoped BigOperators

universe u v

namespace LeanBlast.SecondKahnKalai

variable {State : Type u} {Ω : Type v}

/-- Split a finite draw sequence into its first draw and remaining sequence. -/
def trialSplitEquiv (Ω : Type v) (n : ℕ) : Ω × (Fin n → Ω) ≃ (Fin (n + 1) → Ω) where
  toFun p := Fin.cases p.1 p.2
  invFun draws := (draws 0, fun i => draws i.succ)
  left_inv p := by cases p; rfl
  right_inv draws := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

namespace FiniteLaw

variable [Fintype Ω]

@[simp] theorem iid_weight_cons (μ : FiniteLaw Ω) (n : ℕ) (head : Ω) (tail : Fin n → Ω) :
    (μ.iid (n + 1)).weight (Fin.cases head tail) = μ.weight head * (μ.iid n).weight tail := by
  simp [iid_weight, Fin.prod_univ_succ]

end FiniteLaw

/-- A deterministic adaptive update iterated over a finite sequence of draws. -/
def adaptiveRun (step : State → Ω → State) :
    (n : ℕ) → State → (Fin n → Ω) → State
  | 0, state, _ => state
  | n + 1, state, draws => adaptiveRun step n (step state (draws 0)) (fun i => draws i.succ)

/-- Number of failed attempts along the actual adaptive state trajectory. -/
def adaptiveFailureCount (step : State → Ω → State) (bad : State → Ω → Bool) :
    (n : ℕ) → State → (Fin n → Ω) → ℕ
  | 0, _, _ => 0
  | n + 1, state, draws =>
      (if bad state (draws 0) then 1 else 0) +
        adaptiveFailureCount step bad n (step state (draws 0)) (fun i => draws i.succ)

/-- Once the rank is zero, later draws are declared successful for the purpose
of counting failures. Before then, success means a strict rank decrease. -/
def rankFailure (rank : State → ℕ) (step : State → Ω → State)
    (state : State) (draw : Ω) : Bool :=
  decide (rank state ≠ 0 ∧ ¬ rank (step state draw) < rank state)

end LeanBlast.SecondKahnKalai

end

end OAI


