-- Prove2me | Definitions.Def_GUT_realification
-- name    : GUT_realification
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T00:33:47.978152+00:00
-- url     : https://prove2.me/theorems/5df63f52-6bf1-4074-a227-dabe12fb02be
-- title:
--   Realification $\rho : \mathbb{C}^{5\times5} \to \mathbb{R}^{10\times10}$
-- statement:
--   Forgetting that $\mathbb{C}^5$ is a complex vector space leaves a $10$-dimensional real inner product space $\mathbb{R}^{10}$, and every complex-linear operator becomes a real-linear one. This file makes that passage explicit at the level of matrices.
--
--   Real coordinates are indexed by pairs: a complex coordinate $i$ together with a label $s\in\{0,1\}$ selecting the real or the imaginary part. Multiplication by a complex number $z$ is the real $2\times2$ matrix
--
--   $$\begin{pmatrix}\operatorname{Re} z & -\operatorname{Im} z\\ \operatorname{Im} z & \operatorname{Re} z\end{pmatrix}$$
--
--   in the real basis $(1, i)$, and the **realification** $\rho(A)$ of a complex $5\times5$ matrix $A$ is obtained by replacing each entry $A_{ij}$ by this $2\times2$ real block.
--
--   The index set of $\mathbb{R}^{10}$ is arranged as $(\{0,1\}\times\{0,1\})\sqcup(\{0,1,2\}\times\{0,1\})$, so that the splitting $\mathbb{C}^5\cong\mathbb{C}^2\oplus\mathbb{C}^3$ becomes the splitting $\mathbb{R}^{10}\cong\mathbb{R}^{4}\oplus\mathbb{R}^{6}$ on the nose: this is the compatibility between the $2+3$ splitting of the $\mathrm{SU}(5)$ theory and the $4+6$ splitting of the Pati-Salam side that Theorem 8 of the source turns on.
--
--   As with the two gauge-group homomorphisms, $\rho$ is introduced here as a bare function; its multiplicativity, injectivity, and the fact that it carries $\mathrm{SU}(5)$ into $\mathrm{SO}(10)$ are separate theorems of the mission.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 4 pp. 67-68 (proof of Theorem 8: forgetting the complex structure on ℂ⁵ gives ℝ¹⁰ and U(5) ⊆ SO(10))

import Mathlib
import Definitions.Def_GUT_standard_model_group

namespace GrandUnifiedTheories

open Matrix

/-- Index type for `ℝ¹⁰ ≅ ℝ⁴ ⊕ ℝ⁶`, the real form of the 2+3 splitting of `ℂ⁵`. -/
abbrev Idx10 : Type := (Fin 2 × Fin 2) ⊕ (Fin 3 × Fin 2)

/-- The real coordinate `(i, s)` of `ℝ¹⁰` lies over the complex coordinate `i` of `ℂ⁵`. -/
def idx10ToC : Idx10 → Idx5 × Fin 2
  | Sum.inl (i, s) => (Sum.inl i, s)
  | Sum.inr (j, s) => (Sum.inr j, s)

/-- The `2 × 2` real matrix of multiplication by `z : ℂ` in the real basis `(1, i)`. -/
noncomputable def realEntry (z : ℂ) (s t : Fin 2) : ℝ :=
  if s = t then z.re else if s = 0 then -z.im else z.im

/-- Forgetting the complex structure: a complex `5 × 5` matrix viewed as a real
`10 × 10` matrix acting on `ℝ¹⁰ ≅ ℂ⁵`. -/
noncomputable def realify (A : Matrix Idx5 Idx5 ℂ) : Matrix Idx10 Idx10 ℝ :=
  Matrix.of fun x y =>
    realEntry (A (idx10ToC x).1 (idx10ToC y).1) (idx10ToC x).2 (idx10ToC y).2

end GrandUnifiedTheories


