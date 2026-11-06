-- Prove2me | Definitions.Def_RandomLPIPM_refProj
-- name    : RandomLPIPM_refProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:29.424823+00:00
-- url     : https://prove2.me/theorems/9d1c082d-c1ed-4574-b3db-9f0e35478eaa
-- title:
--   $P(UX)$ under the uniform subspace law (Theorem 6.8, Lemma 6.9)
-- statement:
--   Let $x,s\in\mathbb R^n_{>0}$ with $\langle x-\mathbf 1,s-\mathbf 1\rangle=0$, and let $U\in\mathbb R^{d\times n}$ have orthonormal rows such that $\operatorname{im}[U^\top]$ is **uniformly distributed among all $d$-dimensional subspaces of $\mathbb R^n$ that contain $s-\mathbf 1$ and are orthogonal to $x-\mathbf 1$**. The object of Theorem 6.8 and Lemma 6.9 is the projection $P(UX)$, $X=\operatorname{Diag}(x)$, onto the row space $X\operatorname{im}[U^\top]$.
--
--   This definition realizes that law through a Gaussian matrix $G\in\mathbb R^{d\times n}$ with rows $g_1,\dots,g_d$. Let $Q$ be the orthogonal projector onto $\operatorname{span}\{x-\mathbf 1,s-\mathbf 1\}^\perp$ and
--   $$W=\begin{cases}\operatorname{span}\big(\{s-\mathbf 1\}\cup\{Qg_i: i\le d-1\}\big), & s\neq\mathbf 1,\\ \operatorname{span}\{Qg_i: i\le d\}, & s=\mathbf 1.\end{cases}$$
--   Then $\texttt{refProj}(x,s,G)$ is the orthogonal projector onto $X W=\{x\cdot w: w\in W\}$.
--
--   When $G$ has independent $\mathcal N(0,1)$ entries and $d<n$, rotation invariance makes $W$ almost surely $d$-dimensional and uniformly distributed among the $d$-dimensional subspaces containing $s-\mathbf 1$ and orthogonal to $x-\mathbf 1$, so $\texttt{refProj}(x,s,G)$ has the law of $P(UX)$.
--
--   **Formalization Note** Mathlib has no Haar measure on Grassmannians, so the uniform law is represented by this Gaussian construction, which is the representation used in the proof of Lemma 6.10 (p.49). $P(UX)$ depends on $U$ only through $\operatorname{im}[U^\top]$. When $s=\mathbf 1$ the containment condition is vacuous and all $d$ rows are used.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 6.8 and Lemma 6.9, p.48; Lemma 6.10 and its proof, p.49

import Mathlib
import Definitions.Def_RandomLPIPM_orthProj

open Matrix

namespace RandomLPIPM

/-- **`P(UX)` under the uniform subspace law of Theorem 6.8 / Lemma 6.9**, as a function of
`x, s ∈ ℝⁿ_{>0}` and a Gaussian matrix `G ∈ ℝ^{d×n}`. Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 6.8 and Lemma 6.9, p.48:
"let `U ∈ ℝ^{d×n}` have orthonormal rows such that `im[Uᵀ]` is uniformly distributed among all
`d`-dimensional subspaces of `ℝⁿ` that contain `s − 1` and are orthogonal to `x − 1`"; the
quantity bounded is `P(UX)·1`, `X = Diag(x)`.

Construction (the representation of the proof of Lemma 6.10, p.49). Let `Q` be the orthogonal
projector onto `span{x − 1, s − 1}^⊥` and `g₁, …, g_d` the rows of `G`. Put
`W = span({s − 1} ∪ {Q gᵢ : i ≤ d − 1})` if `s ≠ 1`, and `W = span{Q gᵢ : i ≤ d}` if `s = 1`.
Then `refProj x s G v` is the orthogonal projection of `v` onto `X·W = {x·w : w ∈ W}`, which is the
row space of `UX` when `im[Uᵀ] = W`.

**Formalization Note.** Mathlib has no Haar measure on Grassmannians. When `G` has independent
`N(0,1)` entries and `⟨x − 1, s − 1⟩ = 0`, rotation invariance makes `W` (almost surely of dimension
`d` when `d < n`) uniformly distributed among the `d`-dimensional subspaces containing `s − 1` and
orthogonal to `x − 1`; this is the law of `im[Uᵀ]`. `P(UX)` depends on `U` only through `im[Uᵀ]`.
When `s = 1` the containment condition is vacuous and all `d` rows are used. Only the first `d − 1`
rows of `G` enter when `s ≠ 1`. -/
noncomputable def refProj {d n : ℕ} (x s : Fin n → ℝ) (G : Fin d → Fin n → ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ := by
  classical
  exact
    let q : (Fin n → ℝ) → (Fin n → ℝ) :=
      orthProj (Submodule.span ℝ {WithLp.toLp 2 (x - 1), WithLp.toLp 2 (s - 1)})ᗮ
    let gens : Set (Fin n → ℝ) :=
      if s = 1 then Set.range (fun i : Fin d => q (G i))
      else insert (s - 1) (Set.range fun i : {i : Fin d // i.val + 1 < d} => q (G i.val))
    orthProj (Submodule.span ℝ ((fun w => WithLp.toLp 2 (x * w)) '' gens)) v

end RandomLPIPM


