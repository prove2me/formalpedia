-- Prove2me | Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
-- name    : HighDimProb_Deviations_SubgaussianVectorNorm_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:32:51.981842+00:00
-- url     : https://prove2.me/theorems/672fb529-d172-44c4-a02e-404f015e2397
-- title:
--   The sub-gaussian norm $\|X\|_{\psi_2}=\sup_{x\in S^{n-1}}\|\langle X,x\rangle\|_{\psi_2}$ of a random vector, valued in $[0,\infty]$
-- statement:
--   This is the **sub-gaussian norm of a random vector** $X$ in $\mathbb R^n$ (Definition 3.4.1):
--   $$
--   \|X\|_{\psi_2} := \sup_{x\in S^{n-1}} \|\langle X,x\rangle\|_{\psi_2}\in[0,\infty],
--   $$
--   the supremum over the unit sphere of the (corrected, $[0,\infty]$-valued) scalar sub-gaussian norms of the one-dimensional marginals. $X$ is a **sub-gaussian random vector** in the book's sense (all marginals $\langle X,x\rangle$, $x\in\mathbb R^n$, sub-gaussian) exactly when $\|X\|_{\psi_2}<\infty$: finiteness gives sub-gaussianity of every marginal by scaling, and conversely in finite dimension $\|\langle X,x\rangle\|_{\psi_2}\le\sum_i|x_i|\,\|X_i\|_{\psi_2}$ by the triangle inequality for $\|\cdot\|_{\psi_2}$, so the marginal norms on the sphere are bounded.
--
--   **Formalization Note.** Re-issued (`_v2`) because it imports the corrected scalar norm `HighDimProb_Concentration_SubgaussianNorm_v2`; the retired version `HighDimProb_Deviations_SubgaussianVectorNorm` was an $\mathbb R$-valued `⨆` of the $\mathbb R$-valued scalar norm and returned the junk value $0$ for a heavy-tailed row, so "$\|A_i\|_{\psi_2}\le K$" was satisfiable with $K=0$ (the accepted disproofs of Theorems 9.1.1 and 9.4.2). The supremum is now taken in `ℝ≥0∞`, so it is $+\infty$ as soon as one marginal is not sub-gaussian or the marginal norms are unbounded. For $n=0$ the sphere is empty and the norm is $0$ (the norm of the zero marginal). Namespace and declaration name (`HighDimProb.Deviations.subgaussianVectorNorm`) are unchanged.
-- source:
--   Vershynin, High-Dimensional Probability (CUP 2018), Definition 3.4.1, p. 56 (PDF p. 64)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2

open MeasureTheory
open scoped ENNReal

namespace HighDimProb.Deviations

/-- The **sub-gaussian norm** `‖X‖_{ψ₂}` of a random vector `X : Ω → EuclideanSpace ℝ (Fin n)`.
Vershynin, *High-Dimensional Probability* (2018), Definition 3.4.1, p. 56 (PDF p. 64): "A random
vector `X` in `ℝⁿ` is called sub-gaussian if the one-dimensional marginals `⟨X,x⟩` are
sub-gaussian random variables for all `x ∈ ℝⁿ`. The sub-gaussian norm of `X` is defined as
`‖X‖_{ψ2} = sup_{x∈S^{n-1}} ‖⟨X,x⟩‖_{ψ2}`." The supremum ranges over the subtype of unit vectors
`{v // ‖v‖ = 1}`, the book's sphere `Sⁿ⁻¹`.

**Corrected version (`_v2`) of `HighDimProb_Deviations_SubgaussianVectorNorm`**, re-issued
because it imports the corrected scalar norm `HighDimProb.Concentration.subgaussianNorm` (now
`ℝ≥0∞`-valued, `⊤` for a non-sub-gaussian marginal). The supremum is taken in `ℝ≥0∞`: it is
`⊤` as soon as one marginal `⟨X,x⟩` is not sub-gaussian (or the marginal norms are unbounded),
and it is finite exactly when `X` is a sub-gaussian random vector in the sense of Definition
3.4.1 (in finite dimension, all marginals sub-gaussian ⇔ the unit-sphere marginal norms are
bounded, by the triangle inequality for `‖·‖_{ψ₂}`). The retired `ℝ`-valued `⨆` returned the
junk value `0` for a heavy-tailed vector, so `‖X‖_{ψ₂} ≤ K` held vacuously. For `n = 0` the
sphere is empty and the norm is `0`, the norm of the zero marginal. -/
noncomputable def subgaussianVectorNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ x : {v : EuclideanSpace ℝ (Fin n) // ‖v‖ = 1},
    HighDimProb.Concentration.subgaussianNorm P (fun ω => inner (𝕜 := ℝ) (X ω) x.1)

end HighDimProb.Deviations


