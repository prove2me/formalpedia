-- Prove2me | Definitions.Def_CompositeSAA_StandingAssumptions
-- name    : CompositeSAA_StandingAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:07.593614+00:00
-- url     : https://prove2.me/theorems/30efae38-fcae-4f65-85d4-c16aa019f492
-- title:
--   Standing assumptions on problem (3) and the compact sets $\mathcal U$, $I_j$
-- statement:
--   The paper's standing assumptions on the composite problem $\vartheta=\min_{u\in U}\varrho[u,X]$ (3), with $X\sim P$:
--
--   1. there are $k\ge1$ outer levels;
--   2. $P$ is a probability measure concentrated on the set $\mathcal X$ of realizations of $X$;
--   3. the feasible set $U\subseteq\mathbb R^n$ is closed;
--   4. $f_j$ is continuous in $(u,\eta)$ jointly for each $x$ ($j=1,\dots,k$), and $f_{k+1}$ is continuous in $u$ for each $x$;
--   5. every $f_j(u,\eta,\cdot)$ and $f_{k+1}(u,\cdot)$ is $P$-integrable;
--   6. the solution set $S$ of (3) is nonempty;
--   7. $\mathcal U$ is compact with $S\subseteq\mathcal U\subseteq U$, and $I_1,\dots,I_k$ are compact;
--   8. $\bar f^P_{j+1}(\mathcal U,I_{j+1})\subseteq\operatorname{int}(I_j)$ for $j=1,\dots,k-1$, and $\bar f^P_{k+1}(\mathcal U)\subseteq\operatorname{int}(I_k)$.
--
--   The compact sets $\mathcal U$ and $I_j$ localize the problem: every convergence statement of the paper is uniform over $\mathcal U\times I_j$.
--
--   **Formalization Note** The paper's "S is bounded" follows from $S\subseteq\mathcal U$ with $\mathcal U$ compact, and "U nonempty" from $S\ne\emptyset$, so neither is a separate field. The "without loss of generality" convexity of $\mathcal U$ and $I_j$ (p.5) is not assumed. The finite moment of $X$ is a hypothesis of the sample-based theorems, as $\mathbb E\|X\|<\infty$.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, p.1 (U closed), p.2 (integrability), p.3 (continuity, S nonempty and bounded), pp.4–5 (𝒰, I_j and the interior conditions)

import Mathlib
import Definitions.Def_CompositeSAA_CompositeModel
import Definitions.Def_CompositeSAA_riskFunctional
import Definitions.Def_CompositeSAA_solutionSet

open MeasureTheory

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, pp.1–5: the standing assumptions of the paper on
the composite problem (3), `ϑ = min_{u ∈ U} ϱ[u, X]`, and the compact sets `𝒰`, `I_j` fixed on
pp.4–5.

1. (p.2) `k ≥ 1` levels besides the innermost one.
2. (p.1, p.4) `P` is a probability measure on the data space concentrated on `𝒳`.
3. (p.1) `U` is closed.
4. (p.3) `f_j` is continuous in its first two arguments `(u, η)` jointly, for every `x`
   (`j = 1, …, k`), and `f_{k+1}` is continuous in `u` for every `x`.
5. (p.2) every `f_j(u, η, ·)` and `f_{k+1}(u, ·)` is `P`-integrable.
6. (p.3) the solution set `S` of (3) is nonempty.
7. (p.4) `𝒰` is compact with `S ⊆ 𝒰 ⊆ U`, and `I_1, …, I_k` are compact.
8. (p.4) `f̄^P_{j+1}(𝒰, I_{j+1}) ⊆ int(I_j)` for `j = 1, …, k − 1`, and
   `f̄^P_{k+1}(𝒰) ⊆ int(I_k)`.

**Formalization Note** The paper's "S is bounded" (p.3) is not a separate field: it follows from
`S ⊆ 𝒰` with `𝒰` compact. `U` nonempty (p.1) follows from `S` nonempty. The "without loss of
generality" convexity of `𝒰` and `I_j` (p.5) is not assumed. The paper's finite `p`-th moment
of `X` (p.1) is a hypothesis of the sample-based theorems where it is used, as `E‖X‖ < ∞`. -/
structure StandingAssumptions {n mX k : ℕ} (D : CompositeModel n mX k)
    (P : Measure (EuclideanSpace ℝ (Fin mX))) (𝒳 : Set (EuclideanSpace ℝ (Fin mX)))
    (U 𝒰 : Set (EuclideanSpace ℝ (Fin n)))
    (I : (j : ℕ) → Set (EuclideanSpace ℝ (Fin (D.m j)))) : Prop where
  one_le_k : 1 ≤ k
  isProb : IsProbabilityMeasure P
  ae_mem : ∀ᵐ x ∂P, x ∈ 𝒳
  isClosed_U : IsClosed U
  continuous_f : ∀ j, 1 ≤ j → j ≤ k → ∀ x,
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin (D.m j)) =>
      D.f j p.1 p.2 x)
  continuous_fLast : ∀ x, Continuous (fun u => D.fLast u x)
  integrable_f : ∀ j, 1 ≤ j → j ≤ k → ∀ u η, Integrable (fun x => D.f j u η x) P
  integrable_fLast : ∀ u, Integrable (fun x => D.fLast u x) P
  solution_nonempty : (solutionSet (riskFunctional D P) U).Nonempty
  isCompact_𝒰 : IsCompact 𝒰
  solution_subset : solutionSet (riskFunctional D P) U ⊆ 𝒰
  𝒰_subset : 𝒰 ⊆ U
  isCompact_I : ∀ j, 1 ≤ j → j ≤ k → IsCompact (I j)
  mapsTo_interior : ∀ j, 1 ≤ j → j < k → ∀ u ∈ 𝒰, ∀ η ∈ I (j + 1),
    (∫ x, D.f (j + 1) u η x ∂P) ∈ interior (I j)
  mapsTo_interior_last : ∀ u ∈ 𝒰, (∫ x, D.fLast u x ∂P) ∈ interior (I k)

end CompositeSAA


