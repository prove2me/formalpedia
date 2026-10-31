-- Prove2me | Definitions.Def_ParriloTheta_IsK0Cert
-- name    : ParriloTheta_IsK0Cert
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:17.972672+00:00
-- url     : https://prove2.me/theorems/349eb45c-4efd-41f9-8d48-05b8f975f921
-- title:
--   $\mathcal K^{(0)}$-certificate
-- statement:
--   Let $M$ be a real matrix indexed by a finite set. A matrix $P$ is a **$\mathcal K^{(0)}$-certificate** for $M$ if
--   1. $P\succeq0$ (positive semidefinite),
--   2. $P\le M$ entrywise, and
--   3. $P_{ii}=M_{ii}$ for every $i$.
--
--   For symmetric $M$, such a $P$ exists exactly when $M\in\mathcal K^{(0)}_n$, by Parrilo's description $\mathcal K^{(0)}_n=\{P+N:P\succeq0,\ N\ge0\}$.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, p.5

import Mathlib

namespace ParriloTheta

/-- **`K^(0)`-certificate.**
Laurent & Vargas, arXiv:2109.12876v1, p.5: "We say that P is a K(0)-certificate for M if P ⪰ 0,
P ≤ M and P_ii = M_ii for all i ∈ [n]."

`IsK0Cert M P`: `P` is positive semidefinite, `P ≤ M` entrywise, and `P` and `M` have the same
diagonal.

**Formalization Note.** `P ⪰ 0` is Mathlib's `Matrix.PosSemidef` (over `ℝ` it includes symmetry
of `P`); `P ≤ M` is entrywise, as in the paper's notation `M ≥ 0` for entrywise nonnegativity
(p.4). The index set `[n]` is a general finite type `ι`. -/
def IsK0Cert {ι : Type*} [Fintype ι] (M P : Matrix ι ι ℝ) : Prop :=
  P.PosSemidef ∧ (∀ i j, P i j ≤ M i j) ∧ ∀ i, P i i = M i i

end ParriloTheta


