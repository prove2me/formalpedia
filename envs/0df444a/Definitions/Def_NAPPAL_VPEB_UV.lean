-- Prove2me | Definitions.Def_NAPPAL_VPEB_UV
-- name    : NAPPAL_VPEB_UV
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:01:48.736729+00:00
-- url     : https://prove2.me/theorems/fd19e5ce-c93a-4fab-9f9b-998ae9e42a64
-- title:
--   The Euclidean space $\mathbb{R}^n \times \mathbb{R}^d$ of primal pairs $(u,v)$
-- statement:
--   For natural numbers $n, d$, the space of **primal pairs** is $\mathbb{R}^n \times \mathbb{R}^d$, whose points are written $(u, v)$ with $u \in \mathbb{R}^n$ and $v \in \mathbb{R}^d$. It carries the Euclidean inner product and norm
--   $$\langle (u,v), (u',v') \rangle = \langle u, u' \rangle + \langle v, v' \rangle, \qquad \|(u,v)\|^2 = \|u\|^2 + \|v\|^2 .$$
--
--   This is the domain of the coupling function $G(u,v)$ of problem (P), and the space in which (H7) measures coercivity.
--
--   **Formalization Note** The product is `WithLp 2 (ℝⁿ × ℝᵈ)`; Lean's plain product would carry the maximum norm instead of the Euclidean one.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, §1.1, p. 2 (problem (P)) and §2, p. 5 (Euclidean scalar product and norm)

import Mathlib

namespace NAPPAL.VPEB

/-- **The Euclidean space `ℝⁿ × ℝᵈ` of primal pairs `(u, v)`.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, §1.1, p. 2 (problem (P): `u ∈ U ⊆ Rn`, `v ∈ Rd`, `G : Rn × Rd → R`) and §2, p. 5:
"We denote Euclidean scalar product of Rn and Euclidean norm as ⟨·⟩ and ‖·‖, respectively."

A point of `UV n d` is a pair `(u, v)` with `u ∈ ℝⁿ`, `v ∈ ℝᵈ`; the first component is `x.fst`,
the second `x.snd`.

**Formalization Note.** `WithLp 2` gives the product the Euclidean norm
`‖(u, v)‖² = ‖u‖² + ‖v‖²` and the inner product `⟨u, u'⟩ + ⟨v, v'⟩`, as in the paper; Lean's
bare product `×` would carry the max norm. -/
abbrev UV (n d : ℕ) : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))

end NAPPAL.VPEB


