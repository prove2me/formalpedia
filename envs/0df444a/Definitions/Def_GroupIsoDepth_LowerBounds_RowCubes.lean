-- Prove2me | Definitions.Def_GroupIsoDepth_LowerBounds_RowCubes
-- name    : GroupIsoDepth_LowerBounds_RowCubes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:40:30.15222+00:00
-- url     : https://prove2.me/theorems/d4604f89-f85e-46c6-81e0-7f5764fc4745
-- title:
--   Row-cubes $A_1\times\dots\times A_k$ of $k\times k$ matrices over a field
-- statement:
--   Identify $F^{k\times k}\cong(F^k)^k$ by writing a matrix as the tuple of its rows, $M=(m_1,\dots,m_k)$. A **row-cube** is a set
--   $$\mathcal F=A_1\times\dots\times A_k=\{M:\ m_j\in A_j\ \text{for all } j\},$$
--   where each $A_j\subseteq F^k$ is an affine subspace.
--
--   **Formalization Note** $A_j$ is a Mathlib `AffineSubspace F (Fin k → F)`, which may be the empty subspace `⊥`; the row-cube is then empty. The paper defines row-cubes over $\mathbb F_2$ (§5.2.1) and uses the same notion over an arbitrary field in Lemma 5.9; the definition is over an arbitrary field.
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), §5.2.1 (p. 38, PDF 39); Lemma 5.9 (pp. 38–39, PDF 39–40)

import Mathlib

namespace GroupIsoDepth.LowerBounds

/-! Grochow, Kardeş, Levet, *Group Isomorphism: Depth-2½ Circuits and Lower Bounds*, STOC 2027
submission (manuscript sha256 cd6cacd4…), §5.2.1 (printed p. 38, PDF 39) and Lemma 5.9 (pp. 38–39,
PDF 39–40).

A `k × k` matrix over a field `F` is the tuple of its rows, `M = (m₁, …, m_k)` with `m_j = M j ∈ F^k`
(`Matrix (Fin k) (Fin k) F` is `Fin k → Fin k → F`). A row-cube is `A₁ × ⋯ × A_k` with every `A_j`
an affine subspace of `F^k`. -/

/-- The row-cube `A₁ × ⋯ × A_k = {M : ∀ j, row j of M ∈ A_j}`. An `A_j` may be Mathlib's empty
affine subspace `⊥`, in which case the row-cube is empty. -/
def rowCube {F : Type*} [Field F] {k : ℕ} (A : Fin k → AffineSubspace F (Fin k → F)) :
    Set (Matrix (Fin k) (Fin k) F) :=
  {M | ∀ j, M j ∈ A j}

end GroupIsoDepth.LowerBounds


