-- Prove2me | Definitions.Def_MatrixLewis_dualMin
-- name    : MatrixLewis_dualMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:50.289563+00:00
-- url     : https://prove2.me/theorems/089a22c7-b4ec-4779-9422-524eca9faed5
-- title:
--   Dual minimizer $M_*(S)$
-- statement:
--   The **dual minimizer** $M_*(S)$ is the unique minimizer of $F^S_{\mathrm{du}}$ over the positive definite $m\times m$ matrices; it exists by Theorem 3.9(i).
--
--   **Formalization Note** Defined by choice when $F^S_{\mathrm{du}}$ has exactly one minimizer over $\mathbb S^m_{++}$, and as the junk value $I_m$ otherwise. Theorem 3.9(i) (a milestone) states that the unique minimizer exists for every $S\succ0$, so the junk branch is never used where the paper uses $M_*(S)$.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 3.9(i), p.20

import Mathlib
import Definitions.Def_MatrixLewis_Fdu

namespace MatrixLewis

/-- The dual minimizer `M*(S)`: the unique minimizer of `F^S_du` over `Sᵐ₊₊` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Theorem 3.9(i), pp.20–21).

**Formalization Note** Defined by choice when `F^S_du` has exactly one minimizer over the
positive definite `m × m` matrices, and `1` (a junk value) otherwise. Theorem 3.9(i) proves the
unique minimizer exists at every `S ≻ 0` under Assumption 3.1, so the junk branch never occurs
where the paper uses `M*(S)`. -/
noncomputable def dualMin {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  open Classical in
  if h : ∃! M : Matrix (Fin m) (Fin m) ℝ,
      M.PosDef ∧ ∀ M' : Matrix (Fin m) (Fin m) ℝ, M'.PosDef → Fdu q A S M ≤ Fdu q A S M'
  then Classical.choose h.exists else 1

end MatrixLewis


