-- Prove2me | Definitions.Def_STCSublinear1377_Main_Machine
-- name    : STCSublinear1377_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:28.32314+00:00
-- url     : https://prove2.me/theorems/abddba60-fd48-45e0-a45e-1c2b52c02692
-- title:
--   Uniform binary evaluators and finite fair tapes
-- statement:
--   A randomized graph algorithm has one binary evaluator and a fixed polynomial $p$ determining the number $p(n)$ of independent fair bits on an input graph of order $n$. Its input contains the order, the binary adjacency table and the random tape, and its output is a binary tree adjacency table. For an event $A$ on tapes,
--
--   $$\Pr(A)=\frac{\#\{s\in\{0,1\}^{p(n)}:A(s)\}}{2^{p(n)}}.$$
--
--   The evaluator is accompanied by a finite-state machine that computes it with a polynomial step bound. Every work alphabet is finite. This excludes a graph-dependent distribution with an unrelated field called runtime and permits the goal to express effective uniform computation. An empty tape has exactly one outcome.
--
--   **Formalization Note** Mathlib's `TM2ComputableInPolyTime` supplies the step relation and time polynomial. A self-delimited unary order header has polynomial length, followed by the binary adjacency table. Output length and spanning-tree correctness are conclusions of the algorithmic theorems.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Theorem 1.1 p.2; §3.4, Theorem 3.10 and final paragraph, PDF/printed p.15; standard finite-machine interpretation of polynomial time

import Definitions.Def_STCSublinear1377_Main_Graph
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- Fixed-size row-major binary table. -/
def tableBits {n : ℕ} (g : Table n) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => g u v

/-- Self-delimited unary order followed by the binary adjacency table and a finite fair tape.
The order header has polynomial length and contains no optimum or certificate. -/
def graphTapeBits {n : ℕ} (g : Table n) (tape : List Bool) : List Bool :=
  List.replicate n true ++ [false] ++ tableBits g ++ tape

/-- Out-of-range entries of a malformed output are false; length is checked by the theorems. -/
def outputTable (n : ℕ) (bits : List Bool) : Table n :=
  fun u v => bits[u.val * n + v.val]?.getD false

/-- A uniform finite-alphabet evaluator. Every work-stack alphabet is finite, in addition to
Mathlib's finite state/control/stack-index requirements. The actual TM2 step relation supplies
the polynomial bound; no runtime label on an arbitrary graph-valued function is used. -/
structure BinaryEvaluator where
  eval : List Bool → List Bool
  implementation : Turing.TM2ComputableInPolyTime id id eval
  finiteWork : ∀ j : implementation.tm.K, Finite (implementation.tm.Γ j)

/-- A bounded fair-tape randomized machine. The tape length is a polynomial in the graph order;
the evaluator reads its complete encoded input within its proved polynomial step bound. -/
structure RandomGraphMachine where
  evaluator : BinaryEvaluator
  tapePolynomial : Polynomial ℕ

def RandomGraphMachine.tapeLength (a : RandomGraphMachine) (n : ℕ) : ℕ :=
  a.tapePolynomial.eval n

def RandomGraphMachine.output {n : ℕ} (a : RandomGraphMachine) (g : Table n)
    (tape : Fin (a.tapeLength n) → Bool) : List Bool :=
  a.evaluator.eval (graphTapeBits g ((List.finRange (a.tapeLength n)).map tape))

/-- Uniform counting probability on all complete fair-coin tapes, including the unique empty tape. -/
noncomputable def tapeProbability (a : RandomGraphMachine) (n : ℕ)
    (event : (Fin (a.tapeLength n) → Bool) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / (2 : ℝ) ^ a.tapeLength n

end STCSublinear1377.Main


