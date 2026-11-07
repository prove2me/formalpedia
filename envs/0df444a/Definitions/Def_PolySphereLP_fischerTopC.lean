-- Prove2me | Definitions.Def_PolySphereLP_fischerTopC
-- name    : PolySphereLP_fischerTopC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:17.490189+00:00
-- url     : https://prove2.me/theorems/ca36627d-e027-46a5-8042-254d0063cde3
-- title:
--   The Fischer top component $\Pi_k G$ of a complex homogeneous polynomial
-- statement:
--   Let $G\in\mathbb C[x_1,\dots,x_n]$ be homogeneous of degree $k$. Its **top harmonic component** $G_k=\Pi_kG$ is the unique $G_k\in\mathcal H^{\mathbb C}_{n,k}$ such that
--   $$G(x)=G_k(x)+(x_1^2+\cdots+x_n^2)\,R(x),\qquad \deg R=k-2,$$
--   with $R=0$ when $k<2$ (Fischer decomposition).
--
--   **Formalization Note** The decomposition exists and $G_k$ is unique for homogeneous $G$, so the fallback value $0$ of the definition is never used. The remainder $R$ is homogeneous of degree $k-2$, and is required to vanish when $k<2$.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (16), p.10; Lemma A.4, p.28

import Mathlib
import Definitions.Def_PolySphereLP_harmonicSpaceC
import Definitions.Def_PolySphereLP_normSqC

namespace PolySphereLP

open Classical in
/-- **The top harmonic component `G_k = Π_k G` of a complex homogeneous polynomial (Fischer).**
Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (16), p.10 and Lemma A.4, p.28: "For a homogeneous degree-k polynomial G, there is a unique
homogeneous harmonic polynomial `Π_k G` such that `G(x) = Π_k G(x) + (x₁² + ⋯ + xₙ²)R(x)`,
`deg R = k − 2`"; Lemma A.4 uses it with complex coefficients.

`fischerTopC n k G` is the `G_k ∈ ℋ^ℂ_{n,k}` for which some `R`, homogeneous of degree `k − 2`
(and `R = 0` when `k < 2`), gives `G = G_k + (x₁² + ⋯ + xₙ²) R`.

**Formalization Note.** For homogeneous `G` of degree `k` the decomposition exists and `G_k` is
unique (complexified Fischer decomposition), so the `else 0` branch is never taken. The clause
`k < 2 → R = 0` encodes `deg R = k − 2 < 0`. -/
noncomputable def fischerTopC (n k : ℕ) (G : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  if h : ∃ Gk ∈ harmonicSpaceC n k, ∃ R : MvPolynomial (Fin n) ℂ,
      R.IsHomogeneous (k - 2) ∧ (k < 2 → R = 0) ∧ G = Gk + normSqC n * R
  then h.choose else 0

end PolySphereLP


