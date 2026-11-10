-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_ShortestPaths
-- name    : FlowOptimalSeparators_MinorFree_ShortestPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:06:14.324807+00:00
-- url     : https://prove2.me/theorems/14ffa824-5f1e-41cb-ac7f-e35326abdbf0
-- title:
--   Shortest-path input arrays, parent trees, and actual SSSP time
-- statement:
--   A shortest-path query supplies a finite graph in CSR arrays, symmetric nonnegative edge lengths, and a source. A finite component-distance bound $L$ is an analysis parameter and is not part of the query input. An integral query has nonnegative integer edge lengths. Results flag unreachable vertices and give distances and a parent tree for the source component; the source uses $n$ as its parent sentinel.
--
--   A correct routine is one fixed deterministic scalar code block that terminates correctly from every valid input prefix, initializing its own work arrays. Its actual worst instruction count is
--   $$T_{\rm SSSP}(N,M,L)=\sup\{\operatorname{work}(I): |V(I)|\le N,\ |E(I)|\le M,\ \operatorname{diam}_{\rm finite}(I)\le L\}.$$
--   The supremum is extended nonnegative, including all valid scratch memories. Completed calls are checked against their actual entry and exit arrays. This interface supplies reusable shortest-path semantics; it assigns no freely chosen cost to a graph operation.
--
--   The routine preserves natural and real register 0 and both memories outside the scratch prefix of length $64(2+n+m+L)^2$. Caller data can be stored beyond that prefix; all instructions used inside the subroutine still execute and count toward its actual time. Algorithmic reductions work uniformly for every correct routine under this convention.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 8, 14, 25, Theorem 5; Theorem 7; its runtime proof

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Graph
import Definitions.Def_FlowOptimalSeparators_MinorFree_RandomRAM

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- An ordinary scalar SSSP input. Edge lengths occur in CSR order, not a dense matrix. -/
structure ShortestInput (n : ℕ) where
  G : Graph n
  adjacency : AdjacencyInput G
  source : Fin n
  length : Fin n → Fin n → ℝ

noncomputable def ShortestInput.metric {n : ℕ} (I : ShortestInput n) :
    Fin n → Fin n → ℝ≥0∞ := fun u v => ENNReal.ofReal (I.length u v)

/-- Distance limits are analysis parameters, not advice supplied to the routine. -/
noncomputable def ShortestInput.ns {n : ℕ} (I : ShortestInput n) : List ℕ :=
  I.adjacency.encode I.source.val

noncomputable def ShortestInput.rs {n : ℕ} (I : ShortestInput n) : List ℝ :=
  (List.finRange n).flatMap fun u => (I.adjacency.rows u).map (I.length u)

def ShortestInput.Valid {n : ℕ} (I : ShortestInput n) (L : ℕ) : Prop :=
  (∀ u v, I.G.Adj u v → 0 ≤ I.length u v ∧ I.length u v = I.length v u) ∧
  ∀ u v, distance I.G I.metric u v ≠ ⊤ → distance I.G I.metric u v ≤ (L : ℝ≥0∞)

def ShortestInput.Integral {n : ℕ} (I : ShortestInput n) : Prop :=
  ∀ u v, I.G.Adj u v → ∃ k : ℕ, I.length u v = k

/-- Only the input prefixes are specified; a routine must initialize its own work arrays. -/
def ShortestInput.InMemory {n : ℕ} (I : ShortestInput n)
    (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  (∀ i < I.ns.length, s.nm i = I.ns.getD i 0) ∧
  ∀ i < I.rs.length, s.rm i = I.rs.getD i 0

/-- n is the sentinel for a root or unreachable parent. -/
def parentPath {n : ℕ} (s : VehicleRoutingSurvey.Routing.ArithmeticState) :
    ℕ → Fin n → List (Fin n)
  | 0, _ => []
  | k + 1, v => v :: (if h : s.nm (n + 1 + v.val) < n then
      parentPath s k ⟨s.nm (n + 1 + v.val), h⟩ else [])

/-- Distances plus an actual shortest-path tree of the reachable component. -/
def ShortestInput.Answer {n : ℕ} (I : ShortestInput n)
    (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  s.nm (n + 1 + I.source.val) = n ∧
  ∀ v, if distance I.G I.metric I.source v = ⊤ then s.nm (v.val + 1) = 0
    else s.nm (v.val + 1) = 1 ∧
      ENNReal.ofReal (s.rm v.val) = distance I.G I.metric I.source v ∧
      IsSimplePath I.G I.source v (parentPath s n v).reverse ∧
      pathLength I.metric (parentPath s n v).reverse = distance I.G I.metric I.source v

/-- Execute a fixed code block from an actual call-entry memory. -/
noncomputable def fromState (code : List Instruction)
    (a : VehicleRoutingSurvey.Routing.ArithmeticState) (ω : Tape) (t : ℕ) : RAMState :=
  (ramStep ⟨code, []⟩ ω)^[t] {scalar := {a with pc := 0, halted := false}}

noncomputable def fromWork (code : List Instruction)
    (a : VehicleRoutingSurvey.Routing.ArithmeticState) (ω : Tape) : ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : (fromState code a ω t).scalar.halted = true), (t : ℝ≥0∞)

def DeterministicCode (code : List Instruction) : Prop :=
  ∀ i ∈ code, match i with | .uniform _ _ => False | .callSSSP => False | _ => True

/-- A fixed caller/callee convention: register 0 carries the caller's saved-data pointer.
The routine owns a bounded scratch prefix; it preserves both memories beyond that prefix.
The generous quadratic range accommodates standard SSSP arrays and Dial's buckets. -/
def SSSPFrame {n : ℕ} (I : ShortestInput n) (L : ℕ)
    (a b : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  b.nr 0 = a.nr 0 ∧ b.rr 0 = a.rr 0 ∧
    ∀ i, 64 * (2 + n + edgeCount I.G + L) ^ 2 ≤ i →
      b.nm i = a.nm i ∧ b.rm i = a.rm i

/-- A genuine routine implementation, on every input prefix and every scratch memory.
The integer flag restricts the routine's domain, rather than pretending real SSSP is Dial. -/
def SSSPCorrect (code : List Instruction) (integerOnly : Bool) : Prop :=
  DeterministicCode code ∧
  ∀ (n L : ℕ) (I : ShortestInput n), I.Valid L →
    (integerOnly = true → I.Integral) →
    ∀ a, I.InMemory a → ∀ ω, ∃ t,
      (fromState code a ω t).scalar.halted = true ∧
      (fromState code a ω t).fault = false ∧ I.Answer (fromState code a ω t).scalar ∧
      SSSPFrame I L a (fromState code a ω t).scalar

/-- Actual worst running time, a complete-lattice supremum; empty families have value zero.
No freely assignable cost parameter is attached to an SSSP routine. -/
noncomputable def TSSSP (code : List Instruction) (N M L : ℕ) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : n ≤ N) (I : ShortestInput n) (_ : edgeCount I.G ≤ M)
    (_ : I.Valid L) (_ : I.Integral)
    (a : VehicleRoutingSurvey.Routing.ArithmeticState) (_ : I.InMemory a)
    (ω : Tape), fromWork code a ω

/-- Audit a completed call: its real entry arrays encode the query and its real exit arrays
contain the correct distances and parent tree. Its size and distance limits are explicit. -/
def IsShortestCall (N M L : ℕ) (integerOnly : Bool)
    (a b : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  ∃ (n : ℕ) (I : ShortestInput n), n ≤ N ∧ edgeCount I.G ≤ M ∧ I.Valid L ∧
    (integerOnly = true → I.Integral) ∧ I.InMemory a ∧ I.Answer b ∧ SSSPFrame I L a b

/-- Full output correctness and almost-sure termination, without assigning any cost. -/
def Returns (P : Program) (ns : List ℕ) (rs : List ℝ)
    (Q : VehicleRoutingSurvey.Routing.ArithmeticState → Prop) : Prop :=
  (∀ ω t, (ramRun P ns rs ω t).scalar.halted = true →
    (ramRun P ns rs ω t).fault = false ∧ Q (ramRun P ns rs ω t).scalar) ∧
  ∀ᵐ ω ∂tapeLaw, ∃ t, (ramRun P ns rs ω t).scalar.halted = true

end FlowOptimalSeparators.MinorFree


