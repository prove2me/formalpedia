-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_push
-- name    : NearlyOptimalPPR_Computation_push
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:37:55.675323+00:00
-- url     : https://prove2.me/theorems/453cb96f-4059-4235-b8bb-d11f2f241a8d
-- title:
--   Operational ACL Push and nonnegative per-call work envelopes
-- statement:
--   Algorithm 1 starts with $z=0$, $r=e_s$, and a FIFO queue containing the seed. A membership table prevents duplicate queue entries. A dequeued row with $r_v>\varepsilon d_v$ changes $z_v$ by $r_v/d_v$, resets $r_v$ to zero, and adds $(1-\alpha)r_v/d_v$ using the old residual to every neighbor. Excessive neighbor rows enter the queue. When the queue empties, only changed coordinates are traversed to emit $\alpha Dz$. Scalar operations, degree/neighbor queries, queue work and explicit output are charged; no global initialization or final vertex scan is included.
--
--   For $C>0$ and an integer exponent $c$, the recursive overhead is
--
--   $$P=C(2+\log(2/\varepsilon)+\ell)^c.$$
--
--   The work of an actual Normalize call includes its descendants, and is infinite if the call never closes. For fixed $\varepsilon,\ell$, schedule, level $j$ and scale $N$, $R_j(N)$ is the supremum in $[0,+\infty]$ of the work of calls actually created by executions on admissible graph/source inputs. An empty family of calls has supremum zero and an unbounded family has supremum infinity. Finiteness and the recurrence are conclusions, not clauses of the envelope definition. The analogous root work includes initialization, completion and explicit output. These analysis executions have deterministic idealized solve charges, so their charged work equals its expected value.
--
--   The $1+o(1)$ convention means that for every $\eta>0$ there is $0<\varepsilon_0\le1$ such that the quantitative envelope is at most $(1/\varepsilon)^{1+\eta}$ whenever $0<\varepsilon\le\varepsilon_0$. The threshold depends on $\eta,C,c$, never on a graph or teleportation parameter.
--
--   These objects support both the classic Push bound and the recursive runtime milestones.
--
--   Differences from the source:
--   - encoding: a local Push implementation and asymptotic charged work → FIFO sparse state transitions with fixed operation charges and explicit output; reason: these represent the specified operations up to uniform unit-cost conventions
--   - encoding: worst-case expected work R_j(N) → ENNReal suprema over actually created calls, with infinite nontermination work; reason: the chosen idealized solve charges are deterministic and suprema cannot hide divergence
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Algorithm 1 and Lemma 2.3 p.5; P and R_j(N) p.18; finite-prefix work conventions pp.28–29

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_recursive

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable

/-! Algorithm 1 p.5. FIFO queues use a membership table, so a scalar push and
its degree/neighbor queries cost O(degree), without a scan over the vertex type.
Functions below denote zero-default sparse tables; initialization touches s only.
The explicit output is assembled only from vertices at which z was changed. -/

structure PushState (n : ℕ) where
  z : Fin n → ℝ
  r : Fin n → ℝ
  queue : List (Fin n)
  queued : Finset (Fin n)
  support : Finset (Fin n)
  work : ℕ
  output : SparseOutput
  done : Bool

def pushInit {n : ℕ} (s : Fin n) : PushState n :=
  ⟨fun _ => 0, LocalPush.e s, [s], {s}, ∅, 4, [], false⟩

def pushStep {n : ℕ} (g : InputGraph n) (α ε : ℝ) (st : PushState n) : PushState n :=
  if st.done then st else
    match st.queue with
    | [] =>
        { st with
          done := true
          output := sparseOn st.support (potentialOutput g.graph α st.z)
          work := st.work + 4 * st.support.card + 1 }
    | v :: rest =>
        let Q := st.queued.erase v
        if ε * LocalPush.deg g.graph v < st.r v then
          let h := st.r v / LocalPush.deg g.graph v
          let r := fun u => (if u = v then 0 else st.r u) +
            if u ∈ g.neighbors v then (1 - α) * h else 0
          let add := (g.neighbors v).filter fun u =>
            u ∉ Q ∧ ε * LocalPush.deg g.graph u < r u
          { z := Function.update st.z v (st.z v + h), r := r
            queue := rest ++ add, queued := Q ∪ add.toFinset
            support := insert v st.support
            work := st.work + 32 * ((g.neighbors v).length + 1)
            output := [], done := false }
        else { st with queue := rest, queued := Q, work := st.work + 4 }

def pushRun {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ) (t : ℕ) : PushState n :=
  (pushStep g α ε)^[t] (pushInit s)

def pushWork {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ) : ℝ≥0∞ :=
  if ∃ t, (pushRun g s α ε t).done = true then
    ⨆ t, ((pushRun g s α ε t).work : ℝ≥0∞)
  else ⊤

/-- Polynomial overhead P from p.18; constants remain uniform across levels. -/
def overhead (C : ℝ) (c : ℕ) (ε : ℝ) (ℓ : ℕ) : ℝ :=
  C * (2 + Real.log (2 / ε) + (ℓ : ℝ)) ^ c

/-- Work of one actual call, including descendants and the crossing update.
An unclosed call has infinite work, rather than requiring termination as input. -/
def callWork {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (id : ℕ) : ℝ≥0∞ :=
  let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
  if ∃ t, id ∈ (run t).closed then ⨆ t, (run t).charged id else ⊤

/-- Uniform worst-case envelope over calls actually created by executions.
ENNReal suprema are valid on empty and unbounded families: respectively 0 and
infinity. No recurrence or finiteness assertion is assumed in this definition. -/
def workEnvelope (m : SolveModel) (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
    (j : ℕ) (N : ℝ) : ℝ≥0∞ :=
  sSup {w | ∃ (n : ℕ) (g : InputGraph n) (s : Fin n) (α : ℝ) (id t : ℕ),
    0 < α ∧ α ≤ 1 / 2 ∧ 0 < g.graph.degree s ∧
    (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).information id =
      some ⟨j, N, blockScale schedule ℓ j N⟩ ∧
    w = callWork m g s α ε ℓ schedule id}

def recursiveWork {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) : ℝ≥0∞ :=
  let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
  if ∃ t, (run t).done = true then ⨆ t, (run t).work else ⊤

/-- The quantitative envelope has exponent 1+o(1), with no fixed worse exponent. -/
def subpolynomialEnvelope (C c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → envelope C c ε ≤ (1 / ε) ^ (1 + η)

end NearlyOptimalPPR.Computation


