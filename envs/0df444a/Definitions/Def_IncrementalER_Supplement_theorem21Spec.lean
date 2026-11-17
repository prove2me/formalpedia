-- Prove2me | Definitions.Def_IncrementalER_Supplement_theorem21Spec
-- name    : IncrementalER_Supplement_theorem21Spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:47:32.066488+00:00
-- url     : https://prove2.me/theorems/b484a8c4-21a4-4d38-ae6f-c2c0867572c4
-- title:
--   Exact-real-RAM specification of terminal-request maintenance (Theorem 2.1)
-- statement:
--   This definition gives the complete machine-level meaning of the terminal-request maintenance theorem. A positive-capacity multigraph is supplied as an edge list, parallel capacities are collapsed only when Laplacian quantities are evaluated, and one randomized exact-real-RAM program is initialized before receiving an oblivious sequence of vertices online.
--
--   The specification includes the parameterized $k$-hitting-set condition, terminal-set size and containment, both directions of leverage-change mass, unweighted symmetric-difference recourse, total charged work, and a single whole-sequence high-probability event. Expectations are lower integrals of nonnegative quantities over the fair-coin tape.
--
--   This interface is reusable for randomized online graph algorithms whose outputs are finite vertex sets and whose guarantees mix expectation, recourse, work, and simultaneous high probability.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 2.1, pp.7 and 14; conventions p.10

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncrementalER_Edge
import Definitions.Def_IncrementalER_scCond
import Definitions.Def_IncrementalER_hitBefore

set_option autoImplicit false

open MeasureTheory

namespace IncrementalER.Supplement

/-!
# Exact-real-RAM interface for terminal-request maintenance

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 2.1, pp.7,14.

This file supplies the common graph, asymptotic and online-machine encodings used by the six
algorithmic supplement theorems.  In particular, all expectations are lower integrals of
nonnegative quantities, and every request is loaded only after the preceding run has halted.
-/

/-- Collapse a positive-capacity multigraph edge list to its symmetric conductance function.
Parallel capacities add and loops are ignored by all Laplacian quantities. -/
noncomputable def edgeCond {n : ℕ} (es : List (IncrementalER.Edge n)) : Fin n → Fin n → ℝ :=
  fun u v => if u = v then 0 else
    (es.map fun e => if (e.u = u ∧ e.v = v) ∨ (e.u = v ∧ e.v = u) then e.c else 0).sum

/-- The source's finite undirected capacitated multigraph assumptions. -/
def ValidGraph {n : ℕ} (es : List (IncrementalER.Edge n)) : Prop :=
  (∀ e ∈ es, 0 < e.c) ∧ IncrementalER.Connected (edgeCond es)

/-- A quasipolynomial capacity-ratio bound: at most
`n ^ (C * (1 + log n)^r)` between any two edge capacities. -/
def QuasiPolyCapacity {n : ℕ} (C : ℝ) (r N : ℕ) (es : List (IncrementalER.Edge n)) : Prop :=
  ∀ e ∈ es, ∀ e' ∈ es,
    e.c ≤ (N : ℝ) ^ (C * (1 + Real.log N) ^ r) * e'.c

/-- `C x (1 + log N)^r`, the fixed-artifact reading of `Õ(x)` from p.10. -/
noncomputable def softBound (C : ℝ) (r : ℕ) (N : ℕ) (x : ℝ) : ℝ :=
  C * x * (1 + Real.log N) ^ r

/-- `Õ(x poly(k))`, with absolute exponent `p`. -/
noncomputable def softPolyBound (C : ℝ) (r p : ℕ) (N : ℕ) (x k : ℝ) : ℝ :=
  softBound C r N (x * (1 + k) ^ p)

/-- A `k`-hitting set, including the paper's hidden `Õ(k²)` congestion bound. -/
def IsKHittingSet {n : ℕ} (c : Fin n → Fin n → ℝ) (T : Finset (Fin n))
    (k C : ℝ) (r N : ℕ) : Prop :=
  ∃ β : ℝ, 0 ≤ β ∧ β ≤ softBound C r N (k ^ 2) ∧
    IncrementalER.IsHittingSet c T k β

/-- Reset the program-facing registers and load one online request into negative cells, while
preserving both memories outside those cells, the random-tape cursor and accumulated work. -/
noncomputable def loadWords (s : PNormReg.State) (ints : List ℤ) (reals : List ℝ) :
    PNormReg.State :=
  { core :=
      { pc := 0
        regs := fun _ => 0
        ptrs := fun _ => 0
        mem := fun z =>
          if -(reals.length : ℤ) ≤ z ∧ z ≤ -1 then reals.getD (-1 - z).toNat 0
          else s.core.mem z }
    integerMemory := fun z =>
      if -(ints.length : ℤ) ≤ z ∧ z ≤ -1 then ints.getD (-1 - z).toNat 0
      else s.integerMemory z
    cursor := s.cursor
    halted := false
    work := s.work }

/-- The graph input layout: integer cells contain the original size `N`, the local size `n`, `m`,
and all endpoints; real cells contain `k` and all capacities. -/
noncomputable def graphState (N : ℕ) {n : ℕ} (es : List (IncrementalER.Edge n)) (k : ℝ) :
    PNormReg.State :=
  PNormReg.initState
    ([N, n, es.length].map Int.ofNat ++
      (es.flatMap fun e => [((e.u : ℕ) : ℤ), ((e.v : ℕ) : ℤ)]))
    (k :: es.map IncrementalER.Edge.c)

/-- Output set number `i`: membership of vertex `v` is the nonzero bit in integer cell
`-(16 + i*n + v)`.  The gap keeps all output cells disjoint from request headers. -/
noncomputable def outputSet (s : PNormReg.State) (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => s.integerMemory (-((16 + i * n + (v : ℕ) : ℕ) : ℤ)) ≠ 0

/-- Initialization followed by the first `t` terminal requests.  Initialization sees only the
graph and `k`; request `j` is loaded only after request `j-1` has completed. -/
noncomputable def terminalRun (P : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (requests : List (Fin n)) (fuel : ℕ)
    (omega : ℕ → Bool) (t : ℕ) : PNormReg.State :=
  (requests.take t).foldl
    (fun s v => PNormReg.run P
      (loadWords s [1, (n : ℤ), ((v : ℕ) : ℤ)] [k]) omega fuel)
    (PNormReg.run P (graphState N es k) omega fuel)

/-- The maintained terminal set after `t` arrived requests. -/
noncomputable def terminalsAt (P : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (requests : List (Fin n)) (fuel : ℕ)
    (omega : ℕ → Bool) (t : ℕ) : Finset (Fin n) :=
  outputSet (terminalRun P N es k requests fuel omega t) n 0

/-- The leverage-change mass in both directions, with each vertex evaluated in the corresponding
new or old terminal set exactly as in Theorem 2.1(2). -/
noncomputable def leverageChangeMass (P : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (requests : List (Fin n)) (fuel : ℕ)
    (omega : ℕ → Bool) : ℝ :=
  ∑ j ∈ Finset.range requests.length,
      let oldT := terminalsAt P N es k requests fuel omega j
      let newT := terminalsAt P N es k requests fuel omega (j + 1)
    (∑ v ∈ newT \ oldT, IncrementalER.levDegT (edgeCond es) newT v) +
      ∑ v ∈ oldT \ newT, IncrementalER.levDegT (edgeCond es) oldT v

/-- Total unweighted terminal-set recourse. -/
noncomputable def terminalRecourse (P : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (requests : List (Fin n)) (fuel : ℕ)
    (omega : ℕ → Bool) : ℕ :=
  ∑ j ∈ Finset.range requests.length,
      ((terminalsAt P N es k requests fuel omega (j + 1) \
        terminalsAt P N es k requests fuel omega j) ∪
       (terminalsAt P N es k requests fuel omega j \
        terminalsAt P N es k requests fuel omega (j + 1))).card

/-- Full machine-level specification of Theorem 2.1.  `C,r,p` are absolute constants; `c` is the
fixed high-probability exponent.  Failure covers initialization and the whole online request
sequence, while the expected leverage-change bound is unconditional. -/
def theorem21Spec (P : PNormReg.Program) (C : ℝ) (r p : ℕ) (c : ℝ) : Prop :=
  PNormReg.Admissible P ∧ 0 < C ∧
  ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, 1 ≤ n → n ≤ N →
    ∀ es : List (IncrementalER.Edge n), ValidGraph es →
    QuasiPolyCapacity C r N es → ∀ k : ℝ, 1 < k → ∀ requests : List (Fin n),
      (requests.length : ℝ) ≤ softBound C r N (es.length / k) →
      let work := softPolyBound C r p N es.length k
      let fuel := ⌊work⌋₊
      (∫⁻ omega, ENNReal.ofReal (leverageChangeMass P N es k requests fuel omega)
          ∂PNormReg.coinTape) ≤ ENNReal.ofReal (softBound C r N (es.length / k)) ∧
      PNormReg.coinTape {omega |
        ¬ ((∀ t ≤ requests.length,
              (terminalRun P N es k requests fuel omega t).halted = true) ∧
            IsKHittingSet (edgeCond es) (terminalsAt P N es k requests fuel omega 0) k C r N ∧
            (∀ t ≤ requests.length,
              ((terminalsAt P N es k requests fuel omega t).card : ℝ) ≤
                softBound C r N (es.length / k) ∧
              terminalsAt P N es k requests fuel omega 0 ∪ (requests.take t).toFinset ⊆
                terminalsAt P N es k requests fuel omega t) ∧
            (terminalRecourse P N es k requests fuel omega : ℝ) ≤
              softBound C r N (es.length / k) ∧
            ((terminalRun P N es k requests fuel omega requests.length).work : ℝ) ≤ work)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-c))

end IncrementalER.Supplement


