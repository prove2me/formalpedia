-- Prove2me | Definitions.Def_CharonChurn_Main_SpectralGap
-- name    : CharonChurn_Main_SpectralGap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:55:08.897412+00:00
-- url     : https://prove2.me/theorems/7a891570-1105-47ea-9df2-39687486f997
-- title:
--   $D$-regularity and normalized absolute spectral gap at least $\hat\lambda_0$
-- statement:
--   $G[S]$ is $D$-regular when every vertex of $S$ has exactly $D$ neighbours in $S$. With the real adjacency matrix of $G[S]$ (symmetric, indexed by $S$) and its eigenvalues $\mu_1\ge\mu_2\ge\dots\ge\mu_m$ in nonincreasing order, $G[S]$ has normalized absolute spectral gap at least $\lambda$ when $|\mu_j|\le(1-\lambda)D$ for every $j\ge 2$, i.e. $\hat\lambda(G[S])=1-\max_{j\ge2}|\mu_j|/D\ge\lambda$. The absolute value is kept, so a bipartite graph (eigenvalue $-D$) has gap $0$. The boundary estimate $|\partial S|\ge\hat\lambda_0D|S|/2$ is not part of the definition; it is a consequence used in the proofs.
--
--   The spectral inequality is total as an auxiliary predicate; its interpretation as a normalized gap is used on connected regular graphs with positive degree, supplied by RoundOK. Empty and zero-degree inputs are excluded by those network assumptions.
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), Definition 2, p. 8 (PDF 8)

import Mathlib
import Definitions.Def_CharonChurn_Main_Connectivity

namespace CharonChurn.Main

/-! # Regularity and the normalized absolute spectral gap (Definition 2, p. 8) -/

/-- `G[S]` is `D`-regular: every vertex of `S` has exactly `D` neighbours in `S`. -/
def IsRegularOn (G : SimpleGraph ℕ) (S : Finset ℕ) (D : ℕ) : Prop :=
  ∀ v ∈ S, (nbrsIn G S v).card = D

/-- The real adjacency matrix of `G[S]`, indexed by the vertices of `S`. -/
noncomputable def adjMatOn (G : SimpleGraph ℕ) (S : Finset ℕ) : Matrix S S ℝ := by
  classical
  exact fun u v => if G.Adj u.1 v.1 then 1 else 0

theorem adjMatOn_isHermitian (G : SimpleGraph ℕ) (S : Finset ℕ) :
    (adjMatOn G S).IsHermitian := by
  classical
  ext u v
  simp [adjMatOn, Matrix.conjTranspose_apply, G.adj_comm]

/-- Normalized absolute spectral gap at least `lam`: writing the adjacency eigenvalues of `G[S]`
in nonincreasing order `μ₁ ≥ μ₂ ≥ ⋯ ≥ μ_m`, every `μ_j` with `j ≥ 2` satisfies
`|μ_j| ≤ (1 − lam)·D`, i.e. `λ̂(G[S]) = 1 − max_{j ≥ 2} |μ_j| / D ≥ lam`. The absolute value is
kept, so a bipartite graph (eigenvalue `−D`) has gap `0`. -/
def HasAbsGapAtLeast (G : SimpleGraph ℕ) (S : Finset ℕ) (D : ℕ) (lam : ℝ) : Prop :=
  ∀ j : Fin (Fintype.card S), 1 ≤ j.val →
    |(adjMatOn_isHermitian G S).eigenvalues₀ j| ≤ (1 - lam) * D

end CharonChurn.Main


