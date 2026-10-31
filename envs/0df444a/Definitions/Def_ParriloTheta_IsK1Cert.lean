-- Prove2me | Definitions.Def_ParriloTheta_IsK1Cert
-- name    : ParriloTheta_IsK1Cert
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:18.099861+00:00
-- url     : https://prove2.me/theorems/b44b560d-9153-464f-ae21-24808f0c941e
-- title:
--   $\mathcal K^{(1)}$-certificate
-- statement:
--   Let $M$ be a real matrix indexed by a finite set $[n]$. Matrices $P(1),\dots,P(n)$ form a **$\mathcal K^{(1)}$-certificate** for $M$ if
--   1. $P(i)\succeq0$ for all $i$;
--   2. $P(i)_{ii}=M_{ii}$ for all $i$;
--   3. $2P(i)_{ij}+P(j)_{ii}=2M_{ij}+M_{ii}$ for all $i\ne j$;
--   4. $P(i)_{jk}+P(j)_{ik}+P(k)_{ij}\le M_{ij}+M_{ik}+M_{jk}$ for all distinct $i,j,k$.
--
--   These are conditions (i)–(iv) of Lemma 2.2; for symmetric $M$ such a family exists exactly when $M\in\mathcal K^{(1)}_n$.
--
--   **Formalization Note** The family is `P : ι → Matrix ι ι ℝ` and $P(i)_{jk}$ is `P i j k`: the first index picks the matrix. Symmetry of each $P(i)$ is part of positive semidefiniteness over $\mathbb R$.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Lemma 2.2, p.5 and p.6

import Mathlib

namespace ParriloTheta

/-- **`K^(1)`-certificate.**
Laurent & Vargas, arXiv:2109.12876v1, p.6: "We say that the matrices P(1), P(2), . . . P(n) are a
K(1)-certificate for M if they satisfy the conditions (i)-(iv) of Lemma 2.2", namely (p.5)
matrices `P(i) ∈ Sⁿ` with
(i) `P(i) ⪰ 0` for all `i`;
(ii) `P(i)_ii = M_ii` for all `i`;
(iii) `2P(i)_ij + P(j)_ii = 2M_ij + M_ii` for all `i ≠ j`;
(iv) `P(i)_jk + P(j)_ik + P(k)_ij ≤ M_ij + M_ik + M_jk` for all distinct `i, j, k`.

**Formalization Note.** The family is `P : ι → Matrix ι ι ℝ` and `P(i)_jk` is `P i j k`: the
first index chooses the matrix. Symmetry `P(i) ∈ Sⁿ` is part of `Matrix.PosSemidef` over `ℝ`.
The index set `[n]` is a general finite type `ι`. -/
def IsK1Cert {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (P : ι → Matrix ι ι ℝ) : Prop :=
  (∀ i, (P i).PosSemidef) ∧
  (∀ i, P i i i = M i i) ∧
  (∀ i j, i ≠ j → 2 * P i i j + P j i i = 2 * M i j + M i i) ∧
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → P i j k + P j i k + P k i j ≤ M i j + M i k + M j k)

end ParriloTheta


