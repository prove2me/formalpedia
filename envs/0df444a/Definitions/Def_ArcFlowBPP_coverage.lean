-- Prove2me | Definitions.Def_ArcFlowBPP_coverage
-- name    : ArcFlowBPP_coverage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:10.692084+00:00
-- url     : https://prove2.me/theorems/600d3510-be5d-4e7f-a2ef-1a8f72ab9bcd
-- title:
--   Number of copies of item $i$ produced by a Gilmore–Gomory solution
-- statement:
--   For a Gilmore–Gomory solution $x$, which uses pattern $p$ exactly $x_p$ times, the **coverage** of item $i$ is $\sum_p p_i\, x_p$, the left-hand side $\sum_{j} a^j_i x_j$ of the demand constraint (7).
--
--   **Formalization Note** A solution is a finitely supported function on patterns, $x : \mathbb N^m \to R$ with $R = \mathbb N$ or $\mathbb R$.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, eq. (7), p.4

import Mathlib

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, eq. (7), p.4: the left-hand side `∑_{j∈J} aʲᵢ xⱼ` of the Gilmore–Gomory demand
constraint, the number of copies of item `i` produced when pattern `p` is used `x p` times.

**Formalization Note.** A solution is a finitely supported function `x : (Fin m → ℕ) →₀ R` on
patterns (`R = ℕ` or `ℝ`); the paper's index set `J` of patterns becomes the pattern set `P`
that contains its support (`ArcFlowBPP.GGFeasible`). -/
def coverage {m : ℕ} {R : Type*} [Semiring R] (x : (Fin m → ℕ) →₀ R) (i : Fin m) : R :=
  x.sum fun p c => (p i : R) * c

end ArcFlowBPP


