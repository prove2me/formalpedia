-- Prove2me | Definitions.Def_WildeQIT_traceDist
-- name    : WildeQIT_traceDist
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:51:38.302191+00:00
-- url     : https://prove2.me/theorems/25d4c22e-4f55-44e2-8d02-41c78c9cd6be
-- title:
--   Trace distance $\|M - N\|_1$
-- statement:
--   **Definition 9.1.2 (Trace Distance).** Given any two operators $M, N \in \mathcal{L}(\mathcal{H}, \mathcal{H}')$, the trace distance between them is
--
--   $$
--   \|M - N\|_1 .
--   $$
--
--   For density operators $\rho, \sigma$ the trace distance $\|\rho - \sigma\|_1$ is the operational measure of distinguishability of the two states (Chapter 9); every later result of §9.1 (probability-difference characterization, triangle inequality, monotonicity under partial trace and channels, strong convexity, the diamond norm) is phrased with it.
--
--   **Formalization Note.** `WildeQIT.traceDist M N := WildeQIT.traceNorm (M - N)` for (possibly rectangular) matrices `M N : Matrix m n ℂ`, where `WildeQIT.traceNorm` is Definition 9.1.1 (`Definitions.Def_WildeQIT_traceNorm`). It is not normalized: the book's normalized trace distance is $\tfrac12 \|\rho-\sigma\|_1$.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.1.2 "Trace Distance from the Trace Norm", Definition 9.1.2 (Trace Distance).

import Definitions.Def_WildeQIT_traceNorm

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.1.2, Definition 9.1.2 (Trace Distance).

Given any two operators `M, N ∈ L(H, H')`, the trace distance between them is `‖M − N‖₁`.
-/

namespace WildeQIT

/-- **Definition 9.1.2 (Trace Distance).** The trace distance between two
(possibly rectangular) matrices `M N : Matrix m n ℂ` is the trace norm of their difference,
`‖M − N‖₁`. -/
noncomputable def traceDist {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M N : Matrix m n ℂ) : ℝ :=
  traceNorm (M - N)

end WildeQIT


