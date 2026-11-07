-- Prove2me | Definitions.Def_CutwidthCircuitLB_B2Circuit
-- name    : CutwidthCircuitLB_B2Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:25.807958+00:00
-- url     : https://prove2.me/theorems/91b5c8d9-8232-40d4-a249-5cebc59ce7be
-- title:
--   $B_2$-circuit on $n$ variables
-- statement:
--   A **$B_2$-circuit** on the variables $x_1, \dots, x_n$ is a directed acyclic graph whose sources are the $n$ variables and whose other vertices, the **gates**, each have two ordered predecessors (variables or other gates) and compute an arbitrary Boolean function $\{0,1\}^2 \to \{0,1\}$ of them. All $16$ binary functions are allowed, and the two predecessors of a gate may coincide. The **size** $s$ is the number of gates. The DAG has exactly one sink among its gates, the **output gate**.
--
--   This is the circuit model of all lower bounds of the mission: Theorem 1.4 bounds the size of every such circuit deciding a fixed language in $\mathbf P$.
--
--   **Formalization Note** The gates are listed in a topological order, indexed by $\{0, \dots, s-1\}$; a predecessor of gate $g$ is a variable or a gate with a smaller index. The single-sink condition is stated as: every gate except the last one is a predecessor of some later gate. Then the last gate is the only gate without a successor, and it is the output gate. A circuit has at least one gate (its output gate); there are no constant inputs. Booleans are `Bool`, with $1$ = `true`.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.1, p.6, and Section 1, p.1

import Mathlib

namespace CutwidthCircuitLB

/-- A **B₂-circuit** on the variables `x₁, …, xₙ` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.1, p.6, and §1, p.1):
a DAG whose sources are the `n` variables and whose other vertices, the gates, have two ordered
predecessors and compute an arbitrary Boolean function of them. The size is the number of gates,
and the DAG has exactly one sink among its gates, the output gate.

**Formalization Note** The gates are listed in a topological order as `Fin size`; the
predecessors of gate `g` are variables (`Sum.inl j`) or earlier gates (`Sum.inr k` with
`k < g`), and the two predecessors may coincide. `op g` is any of the 16 binary Boolean functions.
The single-sink condition is `single_sink`: every gate other than the last one is a predecessor of
a later gate, so the last gate is the only gate without a successor and is the output gate.
Booleans are `Bool`, with `1 = true`. A circuit has at least one gate (`size_pos`): the output
gate is a gate. There are no constant inputs. -/
structure B2Circuit (n : ℕ) where
  /-- the number of gates `s` -/
  size : ℕ
  /-- the output gate exists -/
  size_pos : 0 < size
  /-- the Boolean function computed by each gate -/
  op : Fin size → Bool → Bool → Bool
  /-- the first predecessor of gate `g`: a variable or an earlier gate -/
  pred₁ : (g : Fin size) → Fin n ⊕ Fin g.val
  /-- the second predecessor of gate `g`: a variable or an earlier gate -/
  pred₂ : (g : Fin size) → Fin n ⊕ Fin g.val
  /-- one sink among the gates: every gate except the last is used by a later gate -/
  single_sink : ∀ g : Fin size, g.val + 1 < size →
    ∃ (h : Fin size) (hgh : g.val < h.val),
      pred₁ h = Sum.inr ⟨g.val, hgh⟩ ∨ pred₂ h = Sum.inr ⟨g.val, hgh⟩

end CutwidthCircuitLB


