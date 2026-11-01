-- Prove2me | Definitions.Def_BenyOreshkov_AQEC_worstFid
-- name    : BenyOreshkov_AQEC_worstFid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:21.101309+00:00
-- url     : https://prove2.me/theorems/b274b2f3-e2ed-402a-9726-a1ad5161b498
-- title:
--   Worst-case entanglement fidelity $F(\mathcal N,\mathcal M)=\min_\rho F_\rho(\mathcal N,\mathcal M)$, Eq. (2)
-- statement:
--   For channels $\mathcal N,\mathcal M$ from $A$ to $X$, the **worst-case entanglement fidelity** is
--   $$
--   F(\mathcal N,\mathcal M) = \min_\rho F_\rho(\mathcal N,\mathcal M),
--   $$
--   the minimum over all states (density matrices) $\rho$ on $A$. Bény and Oreshkov compare channels with this quantity; it relates to the fidelity as the diamond-norm distance relates to the trace distance.
--
--   **Formalization Note** The minimum is the infimum over the set of density matrices (positive semidefinite, trace one; `PeresTerno.IsDensityMatrix`), not over all matrices. For nonempty $A$ that set is nonempty and compact, $F_\rho\ge 0$ and $\rho\mapsto F_\rho$ is continuous, so the infimum is attained and equals the paper's minimum.
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, Eq. (2), p. 2

import Definitions.Def_BenyOreshkov_AQEC_entFid
import Definitions.Def_PeresTerno_kraus_basics

open Matrix QAlgorithms

namespace BenyOreshkov.AQEC

/-- **Worst-case entanglement fidelity**, Eq. (2), Bény, Oreshkov, arXiv:0907.5391v4, p. 2:
`F(N, M) = min_ρ F_ρ(N, M)`, the minimum over all states `ρ` of the input system.

**Formalization Note** The minimum is the infimum `⨅` over the subtype of density matrices
(`PeresTerno.IsDensityMatrix`: positive semidefinite, trace one), never over all matrices. For a
nonempty `A` that set is nonempty and `F_ρ ≥ 0`, so the real infimum is the true infimum, and it
is attained (compact set, continuous map), so it is the paper's minimum. -/
noncomputable def worstFid {A X : Type} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]
    (N M : Superop A X) : ℝ :=
  ⨅ ρ : {ρ : Matrix A A ℂ // PeresTerno.IsDensityMatrix ρ}, entFid ρ.1 N M

end BenyOreshkov.AQEC


