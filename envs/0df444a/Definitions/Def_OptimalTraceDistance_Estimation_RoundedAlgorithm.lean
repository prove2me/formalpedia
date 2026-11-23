-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_RoundedAlgorithm
-- name    : OptimalTraceDistance_Estimation_RoundedAlgorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-23T09:55:42.234806+00:00
-- url     : https://prove2.me/theorems/ca6a8e4a-ca17-4dbb-88d7-03007b25a0a1
-- title:
--   Rounded variant of Algorithm 2 (finite report set)
-- statement:
--   A discretized variant of the two-stage estimator (Algorithm 2) of the source, used to realize the algorithm as a single measurement with finitely many intermediate outcomes.
--
--   For a mesh $\eta>0$, the *grid cell* of a complex $d\times d$ matrix $A$ is the array of integer pairs $(\lfloor \operatorname{Re}A_{ij}/\eta\rfloor,\lfloor \operatorname{Im}A_{ij}/\eta\rfloor)$. Every cell that meets the unitary group is assigned a fixed unitary representative, and $\operatorname{round}_\eta(U)$ is the representative of the cell of $U$; thus $\operatorname{round}_\eta(U)$ is unitary and differs from $U$ entrywise by less than $\sqrt2\,\eta$. The mesh used with $m$ tomography copies is
--
--   $$
--   \eta_{d,m}=\frac{1}{2^{10}(d+1)^2(m+1)} .
--   $$
--
--   The *rounded tomography law* is the law of the Keyl report $U'\operatorname{diag}(\lambda/m)U'^{\dagger}$ with $U'=\operatorname{round}_{\eta_{d,m}}(U)$, where $(\lambda,U)$ is distributed according to Keyl's joint law for $m$ copies of $\rho$. It takes finitely many values, all of them density matrices.
--
--   The *rounded algorithm weight* is defined exactly as the event weight of Algorithm 2, with every Keyl report replaced by its rounded version: for $d<d_0$ it is the law of the distance between rounded reports for $\rho$ and $\sigma$ (with $\lceil C_0d^2/\varepsilon^2\rceil$ copies each); for $d\ge d_0$ it is the mixture, over the rounded report for $(\rho+\sigma)/2$, of the clipped spectral outcome law of the polynomial observable built from the report projector, on $\lceil C\,\mathrm{rate}(d,\varepsilon)\rceil$ fresh labelled copies.
--
--   **Formalization Note** Cell representatives are chosen with `Classical.choice`; only the facts that the representative is unitary and lies in the same cell are used.
-- source:
--   Variant of Algorithm 2 (p.11) and §5 (p.21) of Chen–Gao–Wang, Optimal Trace Distance Estimation, STOC 2027 submission #875, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/875.pdf; tomography stage from O'Donnell–Wright, arXiv:1508.01907, Theorem 1.2. The rounding of the Keyl unitary to a finite grid is a formalization device, not part of the source.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal
noncomputable section

namespace OptimalTraceDistance.Estimation

/-- Grid cell of a complex matrix at mesh `η`: floors of the real and imaginary parts of the
entries divided by `η`. -/
def gridCell {d : ℕ} (η : ℝ) (A : Mat d) : Fin d → Fin d → ℤ × ℤ :=
  fun i j => (⌊(A i j).re / η⌋, ⌊(A i j).im / η⌋)

/-- A fixed unitary in each grid cell that meets the unitary group (the identity otherwise). -/
def cellUnitary {d : ℕ} (η : ℝ) (k : Fin d → Fin d → ℤ × ℤ) : Matrix.unitaryGroup (Fin d) ℂ :=
  if h : ∃ U : Matrix.unitaryGroup (Fin d) ℂ, gridCell η (U : Mat d) = k then h.choose else 1

/-- Rounding of a unitary to the representative of its grid cell. -/
def roundUnitary {d : ℕ} (η : ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  cellUnitary η (gridCell η (U : Mat d))

/-- Rounding mesh used with `m` tomography copies in dimension `d`. -/
def roundingMesh (d m : ℕ) : ℝ := 1 / (2^10 * ((d:ℝ) + 1)^2 * ((m:ℝ) + 1))

/-- Law of the Keyl report after rounding the unitary outcome to its grid cell:
the report is `U' diag(λ/m) U'^†` with `U'` the cell representative of the Keyl unitary `U`.
It takes finitely many values, all density matrices. -/
def roundedTomographyLaw {d : ℕ} (m : ℕ) (ρ : Mat d) (hρ : Density ρ) : Measure (Mat d) :=
  if h : 0 < d ∧ 0 < m then
    Measure.map (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate h.1 h.2 o.1 (roundUnitary (roundingMesh d m) o.2))
      (QAlgorithms.Tomography.keylJointLaw h.1 h.2 ρ hρ)
  else 0

/-- Event weights of the two-stage algorithm of Algorithm 2 in which every Keyl report is
replaced by its rounded version (`roundedTomographyLaw`). -/
def roundedAlgorithmWeight {d : ℕ} (C : ℝ) (d₀ : ℕ) (ε : ℝ)
    (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) (B : Set ℝ) : ℝ≥0∞ :=
  if d < d₀ then
    ∫⁻ a : Mat d, ∫⁻ b : Mat d, if distance a b ∈ B then 1 else 0
      ∂roundedTomographyLaw (boundedCount d ε) σ hσ
      ∂roundedTomographyLaw (boundedCount d ε) ρ hρ
  else
    let n := freshCount C d ε
    let mixture := plus ρ σ
    if hm : Density mixture then
      ∫⁻ report, spectralLaw (observable (f d ε (reportProjector d report)) n)
          (powerState (labelledState ρ σ) n) (clip ⁻¹' B)
        ∂roundedTomographyLaw (tomographyCount d) mixture hm
    else 0

end OptimalTraceDistance.Estimation


