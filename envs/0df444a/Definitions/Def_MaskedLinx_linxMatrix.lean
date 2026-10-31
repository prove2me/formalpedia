-- Prove2me | Definitions.Def_MaskedLinx_linxMatrix
-- name    : MaskedLinx_linxMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:18.704527+00:00
-- url     : https://prove2.me/theorems/fecaf36d-e621-44b1-afcb-802f429dc572
-- title:
--   The linx matrix $\gamma\,C\,\mathrm{Diag}(x)\,C+\mathrm{Diag}(e-x)$
-- statement:
--   For a real square matrix $C$ indexed by a finite set $N$, a scaling parameter $\gamma\in\mathbb R$ and a vector $x\in\mathbb R^N$, the linx matrix is
--
--   $$\gamma\,C\,\mathrm{Diag}(x)\,C+\mathrm{Diag}(e-x),$$
--
--   where $\mathrm{Diag}(v)$ is the diagonal matrix with diagonal $v$ and $e$ is the all-ones vector. With $\gamma=1$ it is the matrix $C\,\mathrm{Diag}(x)\,C+\mathrm{Diag}(e-x)$ whose log-determinant is Anstreicher's linx objective.
--
--   When $C$ is symmetric positive semidefinite, $\gamma>0$ and $0\le x\le e$, this matrix is positive semidefinite.
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, §1, definition of f(C,s;γ;x) after display (2), p.2

import Mathlib

namespace MaskedLinx

/-- **The matrix `γ C Diag(x) C + Diag(e − x)` inside the scaled linx objective.**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, §1, definition of `f(C,s;γ;x)` after display (2), p.2.

`linxMatrix C γ x = γ • (C * diagonal x * C) + diagonal (fun i => 1 - x i)`. With `γ = 1` it is
the matrix `C Diag(x) C + Diag(e − x)` of the unscaled objective `f(C,s;x)` of (1).

**Formalization Note.** Indices range over an arbitrary finite type `ι`; `e` is the all-ones
vector and `Diag` is `Matrix.diagonal`. -/
noncomputable def linxMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (γ : ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  γ • (C * Matrix.diagonal x * C) + Matrix.diagonal (fun i => 1 - x i)

end MaskedLinx


