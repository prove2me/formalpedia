-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_IsSCSmoothQuadratic
-- name    : FourierRankQLB_Supplement_IsSCSmoothQuadratic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:14:26.141197+00:00
-- url     : https://prove2.me/theorems/06a15488-ab59-43ba-8bc2-c375efd10335
-- title:
--   1-strongly convex, $\kappa$-smooth quadratic: $I \preceq H \preceq \kappa I$
-- statement:
--   A function $f:\mathbb R^n\to\mathbb R$ is a **1-strongly convex, κ-smooth quadratic** if
--
--   $$
--   f(x) = \tfrac12\, x^\top H x + b^\top x + c
--   $$
--
--   for some real symmetric $H$, $b\in\mathbb R^n$ and $c\in\mathbb R$ with
--
--   $$
--   I \preceq H \preceq \kappa I
--   $$
--
--   in the Loewner order. This is the paper's definition on p.33: for a quadratic with Hessian $H$, these inequalities mean that the function is 1-strongly convex and κ-smooth, with condition number at most κ. Theorems 6.1 and 7.13 require every member of their hard families to be of this kind.
--
--   **Formalization Note** $A \preceq B$ is written as positive semidefiniteness of $B - A$ (`Matrix.PosSemidef`).
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §6, p.33

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_quadFun

open Matrix

namespace FourierRankQLB

namespace Supplement

/-- `f` is a quadratic function on `ℝⁿ` that is `1`-strongly convex and `κ`-smooth: `f(x) =
½ xᵀ H x + bᵀ x + c` with `H` real symmetric and `I ⪯ H ⪯ κ I`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §6, p. 33 ("For a quadratic function with Hessian `H`, the inequalities `I ⪯ H ⪯ κI` mean
that the function is 1-strongly convex and κ-smooth").

**Formalization Note.** `⪯` is the Loewner order: `H - I` and `κ I - H` are positive
semidefinite. -/
def IsSCSmoothQuadratic {n : ℕ} (κ : ℝ) (f : Ambient n → ℝ) : Prop :=
  ∃ (H : Matrix (Fin n) (Fin n) ℝ) (b : Ambient n) (c : ℝ), H.IsSymm ∧
    (H - 1).PosSemidef ∧ (κ • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef ∧ f = quadFun H b c

end Supplement

end FourierRankQLB


