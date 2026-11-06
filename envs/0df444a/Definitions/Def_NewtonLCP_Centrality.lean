-- Prove2me | Definitions.Def_NewtonLCP_Centrality
-- name    : NewtonLCP_Centrality
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:41.355546+00:00
-- url     : https://prove2.me/theorems/390830e8-256f-4bfa-a9a0-6dcc4d80ed31
-- title:
--   Centrality error $\mathrm{err}(x,s,\mu)$ and the neighbourhood $\mathcal N^2(\beta)$
-- statement:
--   For $(x,s)\in\mathcal F_{>0}(M,q)$ and $\mu>0$ the **centrality error** is the vector
--
--   $$\mathrm{err}(x,s,\mu)=1_n-\frac{xs}{\mu}\qquad(3)$$
--
--   (entrywise product and division). For $\beta\ge0$ the **$\ell_2$-neighbourhood of the central path** is
--
--   $$\mathcal N^2(\beta)=\{(x,s,\mu):(x,s)\in\mathcal F_{>0}(M,q),\ \mu>0,\ \|\mathrm{err}(x,s,\mu)\|_2\le\beta\}.$$
--
--   Path-following methods keep their iterates in such a neighbourhood while decreasing $\mu$; Algorithm 3 tests membership in $\mathcal N^2(\beta)$ after every pair of Newton steps.
--
--   **Formalization Note** $\|v\|_2=\sqrt{\sum_i v_i^2}$ is written directly. The error vector is defined by formula (3) for all $x,s,\mu$.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), display (3) and N²(β), p.6

import Mathlib
import Definitions.Def_NewtonLCP_LCP

open Matrix

namespace NewtonLCP

/-!
# Centrality error and the ℓ₂-neighbourhood N²(β) of the central path

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), §2.1, display (3) and the definition of `N²(β)`,
p.6.

**Formalization Note.** `l2norm v = √(Σᵢ vᵢ²)` is the Euclidean norm of `v : ι → ℝ` (written
directly rather than through `EuclideanSpace`). `err x s µ = 1ₙ − xs/µ` is the formula of (3)
for any `x, s, µ`; the neighbourhood carries the paper's side conditions `(x, s) ∈ F_{>0}` and
`µ > 0`. The Lean identifier `mu` stands for `µ`.
-/

variable {ι : Type*} [Fintype ι]

/-- The Euclidean norm `‖v‖₂ = √(Σᵢ vᵢ²)`. -/
noncomputable def l2norm (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The centrality error vector `err(x, s, µ) = 1ₙ − xs/µ` (3), p.6. -/
noncomputable def err (x s : ι → ℝ) (mu : ℝ) : ι → ℝ :=
  fun i => 1 - x i * s i / mu

/-- `(x, s, µ) ∈ N²(β)` for LCP(M, q): `(x, s) ∈ F_{>0}(M, q)`, `µ > 0` and
`‖err(x, s, µ)‖₂ ≤ β` (p.6). -/
def InN2 (M : Matrix ι ι ℝ) (q : ι → ℝ) (β : ℝ) (x s : ι → ℝ) (mu : ℝ) : Prop :=
  (x, s) ∈ FeasPos M q ∧ 0 < mu ∧ l2norm (err x s mu) ≤ β

end NewtonLCP


