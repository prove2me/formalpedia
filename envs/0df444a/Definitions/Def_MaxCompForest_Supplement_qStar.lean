-- Prove2me | Definitions.Def_MaxCompForest_Supplement_qStar
-- name    : MaxCompForest_Supplement_qStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:13:04.497381+00:00
-- url     : https://prove2.me/theorems/6710430b-3f50-4dc2-acc6-d13933d220e5
-- title:
--   Spectral budget $q^*$
-- statement:
--   Let $0=\lambda_1<\lambda_2\le\dots\le\lambda_n$ be the eigenvalues of $N=D^{-1/2}LD^{-1/2}$ for a connected graph, and $\sigma,R>0$. The **spectral budget** $q^*$ is the largest index $j\in\{1,\dots,n\}$ with
--
--   $$j\sigma^2\le R^2/\lambda_j,$$
--
--   where $j=1$ is admitted by convention ($\lambda_1=0$). It balances the approximation bias $R^2/\lambda_{q+1}$ of retaining $q$ low modes against the noise variance $q\sigma^2$.
--
--   **Formalization Note** $\lambda_j$ is the published `lam G (deg G) (j-1)`; the convention is a disjunct, so the value $R^2/0$ is never consulted.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 5.2, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_deg
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The spectral budget** `q*`: the largest `j ∈ {1, …, n}` with `j σ² ≤ R²/λ_j`, where `j = 1` is admitted by
convention (`λ_1 = 0`).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 5.2, p.30.

**Formalization Note.** `λ_j` is the published `lam G (deg G) (j − 1)` (ascending, with multiplicity). The
convention is the disjunct `j = 1`, so the junk value `R²/0 = 0` is never consulted. For `j ≥ 2` and a connected
graph, `λ_j > 0`. The maximum is `Finset.sup`, which is `1` or more as soon as `n ≥ 1`. -/
noncomputable def qStar (G : WGraph V E) (σ R : ℝ) : ℕ :=
  ((Finset.Icc 1 (Fintype.card V)).filter fun j : ℕ =>
    j = 1 ∨ (j : ℝ) * σ ^ 2 ≤ R ^ 2 / MaxCompForest.lam G (MaxCompForest.deg G) (j - 1)).sup id

end MaxCompForest.Supplement


