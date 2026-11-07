-- Prove2me | Definitions.Def_ParallelHAC_HACRun_phasePotential
-- name    : ParallelHAC_HACRun_phasePotential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:13.234607+00:00
-- url     : https://prove2.me/theorems/2f23b5b7-7615-452d-ace2-91da977d17c3
-- title:
--   Phase value $\mathrm{val}_j$ and phase potential $\phi_j$ (Definitions 10–11)
-- statement:
--   For a HAC run, a point $x_0$ and a phase $j$ with starting merge $s_j$, let $\tilde X_j=X_{s_j}$ and $\tilde\delta_j=\max_{i\le s_j}\delta_i$. Then
--   $$\mathrm{val}_j(A)=\exp_2\Bigl(-\frac{d(\tilde X_j,A)}{4\tilde\delta_j}\Bigr),\qquad \phi_j(\mathcal C)=\sum_{A\in\mathcal C:\ |A|<|\tilde X_j|/2}\mathrm{val}_j(A).$$
--
--   These are the value (Definition 10) and potential (Definition 11) of the $j$-th phase, evaluated on any family of clusters, in particular on the clusterings $\mathcal C_i$ of the run.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.2, Definitions 10–11, pp.19–20 (PDF pp.22–23)

import Mathlib
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_mergeValue
import Definitions.Def_ParallelHAC_HACRun_clusterOf
import Definitions.Def_ParallelHAC_HACRun_phaseEnd
import Definitions.Def_ParallelHAC_clusterValue

namespace ParallelHAC

/-- `val_j(A) = exp₂(−d(X̃_j, A)/(4 δ̃_j))`, the value of cluster `A` in the `j`-th phase, with
`X̃_j = X_{s_j}` and `δ̃_j = max_{i ≤ s_j} δ_i` (Definition 10, p.19).
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, p.19. -/
noncomputable def HACRun.phaseValue {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (j : ℕ)
    (A : Finset V) : ℝ :=
  clusterValue d (R.clusterOf x₀ (R.phaseStart x₀ cΔ j))
    (R.maxMergeValue (R.phaseStart x₀ cΔ j)) A

/-- `ϕ_j(𝒞) = ∑_{A ∈ 𝒞 : |A| < |X̃_j|/2} val_j(A)`, the potential of the family `𝒞` in the
`j`-th phase (Definition 11, p.20).
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, p.20. -/
noncomputable def HACRun.phasePotential {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (cΔ : ℝ) (j : ℕ)
    (𝒞 : Finset (Finset V)) : ℝ :=
  potential d (R.clusterOf x₀ (R.phaseStart x₀ cΔ j))
    (R.maxMergeValue (R.phaseStart x₀ cΔ j)) 𝒞

end ParallelHAC


