-- Prove2me | Definitions.Def_QuadSDE_Observable
-- name    : QuadSDE_Observable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:18.443602+00:00
-- url     : https://prove2.me/theorems/0b02882c-053a-4130-867a-ef743060c48d
-- title:
--   Observables $u_0(x)=x_i$ and $u_0(x)=x_ix_j$
-- statement:
--   The class $\mathcal O$ of observables of APX-SDE consists of the monomials
--   $$u_0(x)=x_i\qquad\text{and}\qquad u_0(x)=x_ix_j,\qquad i,j\in[N],$$
--   where $i=j$ is allowed. They measure the mean values and second moments of the coordinates of the final state vector.
--
--   **Formalization Note** `lin i` is $x_i$ and `quad i j` is $x_ix_j$, with indices in `Fin N`; `Observable.eval` evaluates $u_0$ at a point of $\mathbb R^N$.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §1, p. 3

import Mathlib

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §1, p. 3: the class
`𝒪` of observables, the monomials `u₀(x) = x_i` and `u₀(x) = x_i x_j` with `i, j ∈ [N]`;
`i = j` is allowed.

**Formalization Note.** `lin i` is `x_i`, `quad i j` is `x_i x_j`; indices are `Fin N` (0-based). -/
inductive Observable (N : ℕ) where
  | lin (i : Fin N)
  | quad (i j : Fin N)

/-- The value `u₀(x)` of an observable at `x ∈ ℝ^N`. -/
def Observable.eval {N : ℕ} : Observable N → (Fin N → ℝ) → ℝ
  | .lin i, x => x i
  | .quad i j, x => x i * x j

end QuadSDE


