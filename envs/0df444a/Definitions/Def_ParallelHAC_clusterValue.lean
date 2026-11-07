-- Prove2me | Definitions.Def_ParallelHAC_clusterValue
-- name    : ParallelHAC_clusterValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:36.913808+00:00
-- url     : https://prove2.me/theorems/27cb0c33-16ec-4cb6-9cfc-48ba51e5a57f
-- title:
--   Cluster value $\mathrm{val}(A)=2^{-d(\tilde X,A)/(4\tilde\delta)}$ and potential $\phi$
-- statement:
--   Fix a centre cluster $\tilde X$ and a scale $\tilde\delta>0$. The **value** of a cluster $A$ is
--   $$\mathrm{val}(A)=\exp_2\Bigl(-\frac{d(\tilde X,A)}{4\tilde\delta}\Bigr),\qquad \exp_2(x)=2^x,$$
--   and the **potential** of a family of clusters $\mathcal C$ is the sum of the values of its clusters of size strictly less than $|\tilde X|/2$:
--   $$\phi(\mathcal C)=\sum_{A\in\mathcal C:\ |A|<|\tilde X|/2}\mathrm{val}(A).$$
--
--   With $\tilde X=\tilde X_j$ and $\tilde\delta=\tilde\delta_j$ these are the paper's $\mathrm{val}_j$ (Definition 10) and $\phi_j$ (Definition 11). The value decays exponentially in the distance from the phase's starting cluster; the potential is the quantity that decreases each time $x_0$'s cluster merges.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.2, Definition 10, p.19 (PDF p.22), Definition 11, p.20 (PDF p.23)

import Mathlib

namespace ParallelHAC

/-- The **value** of a cluster `A` relative to a centre `X̃` and a scale `δ̃ > 0`:
`exp₂(−d(X̃, A) / (4 δ̃))` with `exp₂(x) := 2^x` (Definition 10, p.19; `val_j` is the case
`X̃ = X̃_j`, `δ̃ = δ̃_j`).
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, Definition 10, p.19.

**Formalization Note.** `exp₂` is the real power `(2 : ℝ) ^ x`. -/
noncomputable def clusterValue {V : Type*} (d : Finset V → Finset V → ℝ) (Xt : Finset V)
    (δt : ℝ) (A : Finset V) : ℝ :=
  (2 : ℝ) ^ (-(d Xt A / (4 * δt)))

/-- The **potential** of a family of clusters `𝒞` relative to `X̃, δ̃`: the sum of the values of
the clusters `A ∈ 𝒞` with `|A| < |X̃|/2` (Definition 11, p.20; `ϕ_j` is the case `X̃ = X̃_j`,
`δ̃ = δ̃_j`).
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, Definition 11, p.20.

**Formalization Note.** The size comparison is made in `ℝ` (strict). -/
noncomputable def potential {V : Type*} (d : Finset V → Finset V → ℝ) (Xt : Finset V)
    (δt : ℝ) (𝒞 : Finset (Finset V)) : ℝ :=
  ∑ A ∈ 𝒞.filter (fun A => (A.card : ℝ) < (Xt.card : ℝ) / 2), clusterValue d Xt δt A

end ParallelHAC


