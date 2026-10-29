-- Prove2me | Definitions.Def_BramsonQueueing_Classical_MarkedQueue
-- name    : BramsonQueueing_Classical_MarkedQueue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:45.364214+00:00
-- url     : https://prove2.me/theorems/d450a769-9201-4532-b813-64c8e6d155d1
-- title:
--   Marked queues, isolated nodes, and process quasi-reversibility
-- statement:
--   A marked queue has rates $a_k(x,y)$ for an external arrival of class $k$, $d_k(x,y)$ for an exit, and $c(x,y)$ for an internal change. Its ordinary rates sum the mechanisms. Augmenting the state by the vectors of arrival and exit counts gives a countable Markov process whose transition kernel records the actual count processes. Products of its kernels define finite-dimensional cylinders over any finite list of successive nonnegative time intervals.
--
--   Quasi-reversibility requires stationarity and, for every such past-exit cylinder $D$, future-arrival cylinder $A$, and current state $z$,
--   $$\Pr(D,X(0)=z,A)=\pi(z)\Pr(D)\Pr(A).$$
--   Thus current state, past exits, and future arrivals are mutually independent in stationarity. Isolated-node data separately give a class set, job counts, stochastic insertion probabilities, removal rates, and count-preserving internal rates. Validity checks count changes and finite service rates. Multiplication by a prescribed arrival intensity produces the marked queue, with state-independent independent Poisson inputs. No stationary law is assumed in a node definition.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Section 2.5, printed pp. 41-45 / PDF pp. 49-53

import Definitions.Def_BramsonQueueing_Classical_CountableProcess

namespace BramsonQueueing.Classical
noncomputable section
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- A Markov queue with class-labelled external arrival and exit events. -/
structure MarkedQueue (S C : Type*) where
  arrival : C → S → S → ℝ≥0∞
  departure : C → S → S → ℝ≥0∞
  internal : S → S → ℝ≥0∞

def MarkedQueue.rate {S C : Type*} [Fintype C] (M : MarkedQueue S C)
    (x y : S) : ℝ≥0∞ :=
  offRate (fun u v => M.internal u v + ∑ k, (M.arrival k u v + M.departure k u v)) x y

/-- Counters start at zero; each external arrival/exit increments its own counter. -/
def increment {C : Type*} (a : C → ℕ) (k : C) : C → ℕ :=
  fun l => if l = k then a l + 1 else a l

def MarkedQueue.countRate {S C : Type*} [Fintype C] (M : MarkedQueue S C)
    (x y : S × (C → ℕ) × (C → ℕ)) : ℝ≥0∞ :=
  (if y.2 = x.2 then M.internal x.1 y.1 else 0) +
  ∑ k, ((if y.2.1 = increment x.2.1 k ∧ y.2.2 = x.2.2
    then M.arrival k x.1 y.1 else 0) +
    (if y.2.1 = x.2.1 ∧ y.2.2 = increment x.2.2 k
    then M.departure k x.1 y.1 else 0))

/-- The joint transition kernel with one vector of event counts retained. -/
def MarkedQueue.countKernel {S C : Type*} [Fintype C] (M : MarkedQueue S C)
    (arrivals : Bool) (t : ℝ) (c : C → ℕ) (x y : S) : ℝ≥0∞ :=
  ∑' other : C → ℕ, transition M.countRate t (x, 0, 0)
    (y, if arrivals then (c, other) else (other, c))

/-- Finite-dimensional count-process cylinders, on successive intervals. -/
def MarkedQueue.traceKernel {S C : Type*} [Fintype C] (M : MarkedQueue S C)
    (arrivals : Bool) : List (ℝ≥0 × (C → ℕ)) → S → S → ℝ≥0∞
  | [], x, y => if x = y then 1 else 0
  | (t,c) :: rest, x, y => ∑' z, M.countKernel arrivals t c x z *
      M.traceKernel arrivals rest z y

/-- Current state, past exits and future arrivals are mutually independent in
stationarity. Cylinder identities express the full count-process independence;
there is no replacement by balance equations or a product-form predicate. -/
def QuasiReversible {S C : Type*} [Fintype C]
    (M : MarkedQueue S C) (π : S → ℝ≥0∞) : Prop :=
  Stationary M.rate π ∧
  ∀ (past future : List (ℝ≥0 × (C → ℕ))) (z : S),
    (∑' x, π x * M.traceKernel false past x z) *
      (∑' y, M.traceKernel true future z y) =
    π z * (∑' x, ∑' y, π x * M.traceKernel false past x y) *
      (∑' x, ∑' y, π x * M.traceKernel true future x y)

/-- An isolated node: insertion probabilities, service-completion rates, and
internal changes, independent of its external arrival intensity. -/
structure Node (S C : Type*) where
  classes : Finset C
  count : S → C → ℕ
  insert : C → S → S → ℝ≥0∞
  remove : C → S → S → ℝ≥0∞
  internal : S → S → ℝ≥0∞

def Node.Valid {S C : Type*} [Fintype C] (N : Node S C) : Prop :=
  (∀ k x, ∑' y, N.insert k x y = if k ∈ N.classes then 1 else 0) ∧
  (∀ k x y, 0 < N.insert k x y → N.count y = increment (N.count x) k) ∧
  (∀ k x y, 0 < N.remove k x y → k ∈ N.classes ∧ N.count x = increment (N.count y) k) ∧
  (∀ x y, 0 < N.internal x y → N.count x = N.count y) ∧
  (∀ x, N.internal x x = 0) ∧
  (∀ x, (∑ k, ∑' y, N.remove k x y) + (∑' y, N.internal x y) ≠ ⊤) ∧
  (∀ x k, k ∉ N.classes → N.count x k = 0)

def Node.queue {S C : Type*} (N : Node S C) (α : C → ℝ≥0∞) : MarkedQueue S C where
  arrival k x y := α k * N.insert k x y
  departure := N.remove
  internal := N.internal

end
end BramsonQueueing.Classical


