-- Prove2me | Definitions.Def_HighDimStat_Pca_PsiPCA
-- name    : HighDimStat_Pca_PsiPCA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:23.56826+00:00
-- url     : https://prove2.me/theorems/4e17f52e-ea9c-4ec2-8486-7328b69f5c46
-- title:
--   The function Psi(Delta; P) of Eq. (8.13)
-- statement:
--   This is the function $\Psi(\Delta; P)$ of Wainwright's Eq. (8.13), central to the PCA basic
--   inequality (Lemma 8.6).
--
--   For $P \in \mathbb R^{d\times d}$, and $\theta^*, \Delta \in \mathbb R^d$,
--
--   $$
--   \Psi(\Delta; P) \;:=\; \langle \Delta, P\Delta\rangle + 2\langle \Delta, P\theta^*\rangle.
--   $$
--
--   **Formalization Note** Both inner products unfolded directly as
--   $\sum_i \Delta_i (P\Delta)_i$ and $\sum_i \Delta_i (P\theta^*)_i$, matching Eq. (8.13)
--   exactly.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 243 (PDF p. 263), Eq. (8.13)

import Mathlib

namespace HighDimStat.Pca

/-- The function `Ψ(Δ; P) := ⟨Δ, PΔ⟩ + 2⟨Δ, Pθ*⟩` of Wainwright, *High-Dimensional Statistics*
(2019), Eq. (8.13), central to the PCA basic inequality (Lemma 8.6). -/
def psiPCA {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (θstar Δ : Fin d → ℝ) : ℝ :=
  (∑ i, Δ i * (P.mulVec Δ) i) + 2 * (∑ i, Δ i * (P.mulVec θstar) i)

end HighDimStat.Pca


