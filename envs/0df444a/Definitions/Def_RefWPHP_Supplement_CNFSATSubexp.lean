-- Prove2me | Definitions.Def_RefWPHP_Supplement_CNFSATSubexp
-- name    : RefWPHP_Supplement_CNFSATSubexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:25:45.085579+00:00
-- url     : https://prove2.me/theorems/b78f0166-93b1-45c6-a25c-93c5c8cd6dd9
-- title:
--   CNF-SAT is decidable in time $2^{o(n)} \cdot (n+m)^{O(1)}$
-- statement:
--   **CNF-SAT admits a deterministic algorithm running in time $2^{o(n)} \cdot (n+m)^{O(1)}$**: there are an algorithm $B$, a constant $c$ and a function $f$ with $f(n)/n \to 0$ such that on every CNF formula $\varphi$ with $n$ variables and $m$ clauses, $B$ decides whether $\varphi$ is satisfiable within
--
--   $$
--   2^{f(n)} \cdot (n + m + 2)^{c}
--   $$
--
--   steps. This is the conclusion of Theorem 5.1; such an algorithm would refute the Exponential Time Hypothesis.
--
--   **Formalization Note** The machine model and the input encoding are those of `PKAutomatable` (Mathlib's `Turing.FinTM2`, input `encodeCNF φ`); the output is one bit. $f$ is natural-valued (a real-valued $f = o(n)$ can be rounded up), and the $+2$ changes the bound by a constant factor when $n + m \ge 1$.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), Theorem 5.1, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_RefWPHP_Supplement_Unsat
import Definitions.Def_RefWPHP_Supplement_encodeCNF

namespace RefWPHP

namespace Supplement

open Filter Topology

/-- "CNF-SAT admits a deterministic algorithm running in time `2^{o(n)} · (n + m)^{O(1)}` where `n`
is the number of variables and `m` is the number of clauses of the input CNF formula", Theorem 5.1
of N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole Principle*, STOC 2027 submission
(held manuscript, sha256 ee75d7f1…), p.39 (PDF 41).

There are a machine `tm`, an exponent `c` and a function `f` with `f(n)/n → 0` such that on the
code of every CNF `φ` with `n` variables and `m` clauses, `tm` halts within
`2^{f(n)} · (n + m + 2)^c` steps with the single bit "`φ` is satisfiable" on its output stack.

**Formalization Note.**
1. The machine model and the input encoding are those of `PKAutomatable` (Mathlib's
   `Turing.FinTM2`, input `encodeCNF φ`); the class `2^{o(n)}·(n+m)^{O(1)}` is invariant under the
   polynomial simulations between standard deterministic models.
2. `f` is natural-valued; a real-valued `f = o(n)` can be replaced by `⌈f⌉`. The `+ 2` in the base
   only changes the bound by a constant factor `2^{O(1)}` when `n + m ≥ 1`. -/
def CNFSATSubexp : Prop :=
  ∃ (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (c : ℕ) (f : ℕ → ℕ),
    Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 0) ∧
    ∀ (n m : ℕ) (φ : Fin m → Finset (Lit n)), ∃ b : Bool, (b = true ↔ ¬ Unsat φ) ∧
      Nonempty (Turing.TM2OutputsInTime tm ((encodeCNF φ).map e₀.symm) (some [e₁.symm b])
        (2 ^ f n * (n + m + 2) ^ c))

end Supplement

end RefWPHP


