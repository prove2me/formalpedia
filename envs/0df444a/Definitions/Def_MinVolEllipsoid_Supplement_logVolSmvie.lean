-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_logVolSmvie
-- name    : MinVolEllipsoid_Supplement_logVolSmvie
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:31:36.61203+00:00
-- url     : https://prove2.me/theorems/e14a696f-cbc5-4490-ac5b-210204e368bd
-- title:
--   Optimal value of problem (28), $\log\mathrm{Vol}(\mathcal E_{\mathrm{smvie}})$
-- statement:
--   For the polytope $\mathcal P=\{x:Sx\le t\}$ with $S\in\mathbb R^{J\times K}$, problem (28) is
--
--   $$
--   \sup_{B\in\mathbb S^K,\ d\in\mathbb R^K}\ \log\det(B)\quad\text{s.t.}\quad \|BS_{j:}\|+K\,S_{j:}^\top d\le K t_j\quad\forall j\in[J],
--   $$
--
--   where $S_{j:}\in\mathbb R^K$ is the transpose of the $j$-th row of $S$, $\|\cdot\|$ is the Euclidean norm and $K$ is the dimension. This definition is its optimal value, an extended real number, with $B$ ranging over positive definite matrices (the domain of $\log\det$).
--
--   Problem (28) is the maximum volume inscribed ellipsoid problem (27) rescaled by the factor $K$; for $(B,d)$ optimal the paper sets $\mathcal E_{\mathrm{smvie}}=\{Bu+d:\|u\|\le1\}$, and the optimal value is $\log\mathrm{Vol}(\mathcal E_{\mathrm{smvie}})$.
--
--   **Formalization Note** $K$ is the dimension $n$ as a real number, $S_{j:}$ is the row `S j`, and $\|v\|$ is $\sqrt{v^\top v}$. The value lives in `EReal` ($-\infty$ if infeasible).
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Appendix B.1, displays (27)–(28), p.31

import Mathlib

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **Problem (28): the optimal value `log Vol(ℰ_smvie)`** (Mittal & Hanasusanto,
arXiv:1807.07507v4, Appendix B.1, displays (27)–(28), p.31).

`logVolSmvie S t` is the optimal value of

`sup { log det(B) : B ∈ 𝕊ᴷ, d ∈ ℝᴷ, ‖B S_{j:}‖ + K S_{j:}⊤ d ≤ K t_j ∀ j ∈ [J] }`,   (28)

the supremum taken over `B` positive definite (the domain of `log det`). Here `S_{j:} ∈ ℝᴷ` is the
transpose of the `j`-th row of `S`, `‖·‖` is the Euclidean norm and `K` is the dimension. The paper
calls `ℰ_smvie = {Bu + d : ‖u‖ ≤ 1}`, for `(B, d)` optimal in (28), the maximum volume inscribed
ellipsoid scaled by `K`, and its objective "provides the logarithm of `Vol(ℰ_smvie)`".

**Formalization Note** The dimension `K` is `n`, used as the real number `(n : ℝ)`. `S_{j:}` is the
row `S j : Fin n → ℝ`, and `‖v‖` is `√(v ⬝ᵥ v)` (the pi type carries the sup norm). `B ∈ 𝕊ᴷ` with the
domain of `log det` is `B.PosDef`. The value is in `EReal`: `⊥` if (28) is infeasible, `⊤` if
unbounded. -/
noncomputable def logVolSmvie {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ) : EReal :=
  ⨆ (B : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (_ : B.PosDef ∧ ∀ j, Real.sqrt ((B *ᵥ S j) ⬝ᵥ (B *ᵥ S j)) + (n : ℝ) * (S j ⬝ᵥ d) ≤
      (n : ℝ) * t j),
    ((Real.log B.det : ℝ) : EReal)

end MinVolEllipsoid.Supplement


