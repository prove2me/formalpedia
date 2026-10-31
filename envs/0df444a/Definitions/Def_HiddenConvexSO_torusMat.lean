-- Prove2me | Definitions.Def_HiddenConvexSO_torusMat
-- name    : HiddenConvexSO_torusMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:20.618179+00:00
-- url     : https://prove2.me/theorems/31453394-7859-4353-8ff4-3a52912a3b44
-- title:
--   Block rotation matrix $R(\theta_1,\dots,\theta_k)$ of the maximal torus (7)–(8)
-- statement:
--   Let $n\ge 0$ and $k=\lfloor n/2\rfloor$. For angles $\theta_1,\dots,\theta_k\in\mathbb R$, the matrix $R(\theta_1,\dots,\theta_k)\in\mathbb R^{n\times n}$ is block diagonal with the $k$ rotation blocks
--
--   $$
--   \begin{pmatrix}\cos\theta_i & \sin\theta_i\\ -\sin\theta_i & \cos\theta_i\end{pmatrix},\qquad i=1,\dots,k,
--   $$
--
--   in rows and columns $2i-1,2i$, followed, when $n$ is odd, by a final diagonal entry $1$ in position $(n,n)$. All other entries are $0$. The **maximal torus** $\mathbb T$ is the set of these matrices as the $\theta_i$ range over $[0,2\pi)$.
--
--   Every element of $\mathrm{SO}(n)$ is conjugate, by an element of $\mathrm{SO}(n)$, to some $R(\theta)$ (Theorem 8); the paper's construction of loops in $\mathrm{SO}(n)$ (Lemma 4) runs inside the torus.
--
--   **Formalization Note** Indices are 0-based: block $b=i-1$ occupies rows and columns $2b,2b+1$, and for odd $n$ the trailing $1$ sits at index $n-1$. The angle vector is indexed by `Fin (n / 2)` (natural division). The angles are arbitrary reals; the range $[0,2\pi)$ is imposed in Theorem 8.
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, §2, displays (7)–(8) and the definition of the maximal torus, p.9

import Mathlib

namespace HiddenConvexSO

/-- **The block-rotation matrix `R(θ₁, …, θ_k)` of the maximal torus.**
Ramachandran, Shu & Wang, *Hidden convexity, optimization, and algorithms on rotation matrices*,
arXiv:2304.08596v2, §2, displays (7)–(8), p.9 (PDF p.9): `R(θ₁, …, θ_k)` is block diagonal with the
`k` blocks `( cos θᵢ  sin θᵢ ; −sin θᵢ  cos θᵢ )` on the diagonal, followed (for odd `n`) by a final
diagonal entry `1`; every other entry is `0`. "We define the maximal torus T to be the set of matrices
of the form R(θ1, . . . , θk) as the θi range over [0, 2π)."

`torusMat n θ` is this `n × n` matrix, with `k = n / 2` (natural-number division, so `k = ⌊n/2⌋`).

**Formalization Note.** Indices are 0-based (`Fin n`): the paper's block `i ∈ {1, …, k}` sits in rows
and columns `2i − 1, 2i`, here the 0-based block `b = i − 1` sits in rows/columns `2b, 2b + 1`, with
`cos θ_b` at `(2b, 2b)` and `(2b+1, 2b+1)`, `sin θ_b` at `(2b, 2b+1)` and `−sin θ_b` at `(2b+1, 2b)`.
An entry `(i, j)` lies in a common block exactly when `i / 2 = j / 2 < n / 2`. For odd `n` the only
index outside every block is `n − 1`, which carries the trailing `1`. The angles are arbitrary reals;
the paper's range `[0, 2π)` is imposed where it is used (Theorem 8). -/
noncomputable def torusMat (n : ℕ) (θ : Fin (n / 2) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if h : i.val / 2 < n / 2 ∧ i.val / 2 = j.val / 2 then
      if i = j then Real.cos (θ ⟨i.val / 2, h.1⟩)
      else if i.val % 2 = 0 then Real.sin (θ ⟨i.val / 2, h.1⟩)
      else - Real.sin (θ ⟨i.val / 2, h.1⟩)
    else if i = j then 1 else 0

end HiddenConvexSO


