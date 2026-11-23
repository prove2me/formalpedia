-- Prove2me | Definitions.Def_DiffNeighbors_Bias_Supplement_ClusterModel
-- name    : DiffNeighbors_Bias_Supplement_ClusterModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:13:30.796752+00:00
-- url     : https://prove2.me/theorems/0d1ba42f-3b7f-4973-91ac-6af0d6bfc3e4
-- title:
--   §4, (9), Appendix A.2 — cluster assignments, external cluster neighbours and the cluster DN estimator
-- statement:
--   Let $c:I\to K$ assign each unit to a cluster label. Its nonempty fibres are the partition. A cluster assignment $z^C$ induces $z_i=z^C_{c(i)}$. Set
--   $$\mathcal N_i^C=\{c(j):j\in\mathcal N_i\}\setminus\{c(i)\},\quad d_i^C=|\{j\in\mathcal N_i:c(j)=c(i)\}|,\quad r_i=|\{j\in\mathcal N_i:c(j)\ne c(i)\}|=d_i-d_i^C.$$
--   With the published weights $\eta_i=z_i/p-(1-z_i)/(1-p)$ and $\xi_i=z_i(1-p)/p+(1-z_i)p/(1-p)$, Equation (9) is
--   $$\widehat{\mathrm{ATE}}_{\mathrm{DN-Cluster}}(z^C)=\frac1N\sum_i\left(\eta_i+\xi_i\sum_{C\in\mathcal N_i^C}\left(\frac{z^C_C}{p}-\frac{1-z^C_C}{1-p}\right)\right)f_i(z).$$
--   The expectation uses the published finite Bernoulli expectation on $K$: clusters are independent, while units in one cluster share treatment. Unused labels have no effect. In an empty population the estimator and ATE are zero.
--
--   The own cluster is excluded following p. 28, which resolves the ambiguity on p. 13. Including it would introduce bias even for constant outcomes. Each external cluster contributes once, while individual outcomes remain separate.
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, pp. 12–13, §4, (9); p. 28, Appendix A.2

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

noncomputable section

namespace DiffNeighbors.Bias.Supplement

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A cluster map c : ι → κ encodes the partition by its nonempty fibres.
Each cluster receives one treatment; units inherit it (§4, p. 12).
Unused cluster labels are harmless independent Bernoulli coordinates. -/
def unitTreatment (c : ι → κ) (zc : κ → Bool) : ι → Bool := fun i => zc (c i)

/-- Clusters containing neighbours of i, EXCLUDING its own cluster.
This follows the explicit convention in Appendix A.2, p. 28. -/
def clusterNeighbors (G : SimpleGraph ι) [DecidableRel G.Adj] (c : ι → κ)
    (i : ι) : Finset κ := ((G.neighborFinset i).image c).erase (c i)

/-- d_i^C, the number of neighbours in i's own cluster (p. 13). -/
def withinDegree (G : SimpleGraph ι) [DecidableRel G.Adj] (c : ι → κ) (i : ι) : ℕ :=
  ((G.neighborFinset i).filter (fun j => c j = c i)).card

/-- d_i - d_i^C, expressed as a cardinality to avoid truncated subtraction.
These are precisely the neighbours outside the unit's own cluster. -/
def outsideDegree (G : SimpleGraph ι) [DecidableRel G.Adj] (c : ι → κ) (i : ι) : ℕ :=
  ((G.neighborFinset i).filter (fun j => c j ≠ c i)).card

/-- The cluster DN estimator (9), p. 13, with the cluster-neighbour convention
of p. 28. eta, xi, and the normalization are the published base definitions.
The expectation is bernExp p on κ, i.e. independent cluster assignments,
NOT independent unit assignments. For an empty population the finite sum is 0. -/
def dnCluster (G : SimpleGraph ι) [DecidableRel G.Adj] (c : ι → κ) (p : ℝ)
    (f : ι → (ι → Bool) → ℝ) (zc : κ → Bool) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i,
    (eta p (unitTreatment c zc) i + xi p (unitTreatment c zc) i *
      ∑ C ∈ clusterNeighbors G c i, eta p zc C) * f i (unitTreatment c zc)

end DiffNeighbors.Bias.Supplement

end


