-- Prove2me | Definitions.Def_BlockBochner_Supplement_haarSphere
-- name    : BlockBochner_Supplement_haarSphere
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:27:40.204492+00:00
-- url     : https://prove2.me/theorems/1932da7b-6d25-4d0f-9312-d5a3922cab44
-- title:
--   Uniform probability measure $\omega$ on $S^{N-1}$
-- statement:
--   $\omega$ is the uniform (rotation-invariant) probability measure on the unit sphere $S^{N-1}\subset\mathbb R^N$: the surface measure of the sphere normalized to total mass $1$. It is the reference measure of each spin in the $O(N)$ Gibbs measure (1) and of the tilted Haar measures $\nu_h$.
--
--   **Formalization Note** Mathlib's surface measure `volume.toSphere` ($\sigma(A)=N\cdot\mathrm{Leb}(\{tu:0<t<1,\ u\in A\})$, which is rotation invariant), normalized by conditioning on the whole sphere. For $N\ge1$ it is a probability measure (proved in the verification file); a structural instance records that it is finite.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 1.3, Eq. (1), p.4 (PDF p.5)

import Mathlib
import Definitions.Def_GraphNNSphere_Sph

open MeasureTheory ProbabilityTheory

namespace BlockBochner.Supplement

/-- **Uniform probability measure `ω` on `S^{N−1}`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.3, p.4,
Eq. (1): "where ω is the uniform probability measure on S^{N−1}".

**Formalization Note** Mathlib's surface measure `volume.toSphere` on the unit sphere of
`EuclideanSpace ℝ (Fin N)` (`μ.toSphere s = N · μ((0,1) • s)`, rotation invariant), normalized to
total mass `1` by conditioning on the whole sphere. For `N ≥ 1` it is a probability measure. -/
noncomputable def haarSphere (N : ℕ) : Measure (GraphNNSphere.Sph N) :=
  (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere[|Set.univ]

/-- `ω` is a finite measure (it has total mass `0` or `1`). -/
instance haarSphere.instIsFiniteMeasure (N : ℕ) : IsFiniteMeasure (haarSphere N) := by
  unfold haarSphere; infer_instance

end BlockBochner.Supplement


