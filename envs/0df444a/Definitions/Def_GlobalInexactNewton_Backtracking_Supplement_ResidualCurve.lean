-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_ResidualCurve
-- name    : GlobalInexactNewton_Backtracking_Supplement_ResidualCurve
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:46:54.838746+00:00
-- url     : https://prove2.me/theorems/98dada65-b9ec-4b25-b9ef-3af5f89f5c5e
-- title:
--   Residual-minimizing equality curves, with skipped stages and endpoint truncation
-- statement:
--   At a nonzero-residual point $x$, run a residual-minimizing method for $F'(x)s=-F(x)$ from zero. Retain stages $q_0=0<q_1<\cdots<q_N$ whose normalized residuals $r_j$ strictly decrease. Keep $r_N\le\bar\eta<r_{N-1}$ and, on the part of segment $j$ where $\max\{\bar\eta,r_{j+1}\}\le\eta\le r_j$, set
--
--   $$\sigma(\eta)=z\!\left(\eta\|F(x)\|\right),$$
--
--   where $z(\rho)$ is Lemma 8.1's square-root parametrization between the original minimizers at $q_j$ and $q_{j+1}$. At a zero-residual point take the zero curve. The first vertex level after a possible truncation is $\max\{\bar\eta,r_1\}$.
--
--   The curve is linear in space, and generally nonlinear in the residual parameter. Both resetting $\bar\eta$ to the last residual and truncating the final segment are included. **Formalization Note** Original minimizers and all underlying method spaces are retained as witnesses. Thus the first method space $K_1$ remains available even when retained stages skip it, or when the sole segment is truncated. No bound on that space, rank condition, or particular Krylov method is imposed.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 416, Residual minimizing equality curve construction; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_ResidualMinimizer

namespace GlobalInexactNewton.Backtracking.Supplement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Level of an original retained residual-minimizing iterate, before endpoint truncation. -/
noncomputable def retainedLevel (F : E → E) (x : E) (z : ℕ → E) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  ‖F x + fderiv ℝ F x (z (q j))‖ / ‖F x‖

/-- The actual first vertex level: truncation can affect it only on a single-segment curve. -/
noncomputable def firstVertexLevel (F : E → E) (x : E) (ηbar : ℝ)
    (z : ℕ → E) (q : ℕ → ℕ) : ℝ :=
  max ηbar (retainedLevel F x z q 1)

/-- p. 416: retain any strictly improving subsequence, then restrict the last segment at ηbar.
The original untruncated minimizers remain as witnesses. Redefining ηbar to the last residual
and truncating the last segment are both included. K 1 is the original first method stage. -/
def IsResidualCurve (F : E → E) (x : E) (ηbar : ℝ) (σ : ℝ → E)
    (K : ℕ → Submodule ℝ E) (z : ℕ → E) (q : ℕ → ℕ) (N : ℕ) : Prop :=
  (F x = 0 ∧ ∀ η ∈ Set.Icc ηbar 1, σ η = 0) ∨
  (F x ≠ 0 ∧ IsResidualMethod (fderiv ℝ F x) (-F x) 0 K z ∧
    0 < N ∧ q 0 = 0 ∧ (∀ j < N, q j < q (j + 1)) ∧
    (∀ j < N, retainedLevel F x z q (j + 1) < retainedLevel F x z q j) ∧
    retainedLevel F x z q N ≤ ηbar ∧ ηbar < retainedLevel F x z q (N - 1) ∧
    ∀ j < N, ∀ η ∈ Set.Icc (max ηbar (retainedLevel F x z q (j + 1)))
        (retainedLevel F x z q j),
      σ η = residualSegment (fderiv ℝ F x) (-F x) 0 (z (q j)) (z (q (j + 1)))
        (η * ‖F x‖))

end GlobalInexactNewton.Backtracking.Supplement


