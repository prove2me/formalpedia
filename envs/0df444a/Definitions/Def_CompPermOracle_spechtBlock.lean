-- Prove2me | Definitions.Def_CompPermOracle_spechtBlock
-- name    : CompPermOracle_spechtBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:17.042082+00:00
-- url     : https://prove2.me/theorems/4826dbe9-745e-4336-a254-ff131cf52d5b
-- title:
--   Blocks $S^\lambda\otimes S^\lambda$ of the group algebra and the Gram eigenvalue $g_{m,\mu}$
-- statement:
--   Under the left-right action of $S_N\times S_N$ on the group algebra, $\mathcal P\cong\bigoplus_{\lambda\vdash N}S^\lambda\otimes S^\lambda$. The **block** of $\lambda$ is the summand of type $S^\lambda\otimes S^\lambda$. For $\lambda=(m,\mu)$ with first row $m$ and conjugate partition $\mu'$ of the rest,
--   $$
--   g_{m,\mu}=\prod_{c=1}^{m}\Big(1+\frac{\mu'_c}{m-c+1}\Big).
--   $$
--   This is the scalar by which the Gram operator acts on the block.
--
--   **Formalization Note** Partitions are the published `DiagramCounting.Shape N`. The block is the $\lambda$-isotypic component of the left regular representation, `componentSpace (regularRep _) (SpechtActual.index λ)`, which as a subspace of $\mathbb C[S_N]$ is the two-sided ideal above. The published Specht modules are built from row tabloids, so the one-row shape is the trivial representation. With $c'=c-1$ (0-based), $\mu'_c$ is `colLen c' - 1`, an exact subtraction for $c'<m$.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), eq. (32) and Lemma 4.9, eq. (33), p.17

import Mathlib
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation

namespace CompPermOracle

open OAI.PartialPermutation OAI.PartialPermutation.DiagramCounting

/-- The block `S^λ ⊗ S^λ` of `𝒫 = ⨁_{λ ⊢ N} S^λ ⊗ S^λ` (Carolan, Majenz, arXiv:2609.28469 (version
of 2026-11-03, sha256 52ebc507…), eq. (32), p.17).

**Formalization Note.** As a subspace of `ℂ[S_N]`, the block is the `λ`-isotypic component of the left
regular representation (`regularRep`, `|φ⟩ ↦ |gφ⟩`, the source's left action), which is the two-sided
ideal of type `S^λ ⊗ S^λ`. Specht modules are the published OAI ones, built from row tabloids. -/
noncomputable def block {N : ℕ} (lam : Shape N) : Submodule ℂ (EuclideanSpace ℂ (Equiv.Perm (Fin N))) :=
  componentSpace (regularRep (Equiv.Perm (Fin N))) (SpechtActual.index lam)

/-- The first row `λ_1` of a Young diagram. -/
def firstRow {N : ℕ} (lam : Shape N) : ℕ := lam.1.rowLen 0

/-- The Gram eigenvalue `g_{m,μ} = ∏_{c=1}^{m} (1 + μ'_c / (m − c + 1))` of eq. (33), for
`λ = (m, μ)` (arXiv:2609.28469, Lemma 4.9, eq. (33), p.17).

**Formalization Note.** With `c' = c − 1` (0-based), `m − c + 1 = m − c'`. The column `c'` of
`μ = λ` minus its first row has length `λ'_{c'} − 1`, and `c' < m = λ_1` makes `λ'_{c'} ≥ 1`, so
the natural-number subtraction is exact. -/
noncomputable def gramEig {N : ℕ} (lam : Shape N) : ℝ :=
  ∏ c ∈ Finset.range (firstRow lam),
    (1 + ((lam.1.colLen c - 1 : ℕ) : ℝ) / (((firstRow lam : ℕ) : ℝ) - (c : ℝ)))

end CompPermOracle


