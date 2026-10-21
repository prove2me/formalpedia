-- Prove2me | Definitions.Def_CODATA_lsa
-- name    : CODATA_lsa
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T01:29:28.440182+00:00
-- url     : https://prove2.me/theorems/c5316139-3133-4eaf-8d64-d0d257577fc4
-- title:
--   The least-squares adjustment model of the CODATA 2022 report
-- statement:
--   The formal skeleton of the least-squares adjustment by which the 2022
--   CODATA recommended values of the fundamental constants were
--   determined. A least-squares problem with N input data and M adjusted
--   constants packages: the observed values of the input data, their
--   standard uncertainties, their correlation coefficients, the design
--   matrix and offset vector of the observational equations, and the
--   weight matrix, which is required to invert the covariance matrix of
--   the data (entry r i j times the two uncertainties u i and u j) on both
--   sides. The associated quantities are the residual vector of the
--   observational equations, the chi-square statistic of the weighted
--   residuals, the normal equations, the minimization property, the
--   normal matrix with its two-sided inverses (the covariance matrix of
--   the adjusted constants), strict positive definiteness of the weight
--   matrix, the covariance matrix of the data, the number of degrees of
--   freedom nu = N - M, and the Birge ratio R_B = sqrt(chi^2/nu). The 2022
--   report's main adjustment has N = 133 input data and M = 79 adjusted
--   constants, hence nu = 54; its separate adjustment of the Newtonian
--   constant of gravitation has N = 16 and M = 1, hence nu = 15.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII, "Least-squares adjustment": the 133 input data and 79 adjusted constants, nu = N - M = 54, chi^2 = 44.2, and the Birge ratio R_B = sqrt(chi^2/nu) printed as 0.90; the separate adjustment of the sixteen values of G with nu = 15 and R_B = 0.93.

import Mathlib

/-!
# The CODATA 2022 adjustment: the least-squares model

The formal skeleton of the least-squares adjustment by which the 2022
CODATA recommended values of the fundamental physical constants were
determined: P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga,
CODATA recommended values of the fundamental physical constants: 2022,
J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860,
and the identical Rev. Mod. Phys. 97, 025002 (2025), doi
10.1103/RevModPhys.97.025002, section XII, "Least-squares adjustment".

The 2022 adjustment is a least-squares adjustment of 133 input data and
79 adjusted constants, so its number of degrees of freedom is
nu = N - M = 54. The model of this file keeps the two counts as
parameters: `LSQ N M` packages the data vector, the standard
uncertainties, the correlation coefficients, the design matrix and the
offset vector of the observational equations, and the weight matrix G,
together with the assertion that G is a two-sided inverse of the
covariance matrix of the data. The associated quantities are the
residual vector, the chi-square statistic, the normal equations, the
minimization property, the normal matrix with its two-sided inverses,
strict positive definiteness of the weight matrix, the covariance
matrix, the number of degrees of freedom (N - M, as in the paper), and
the Birge ratio, defined as in section XII by R_B = sqrt(chi^2/nu).
-/

namespace CODATA

/-- The data of a linear least-squares problem with `N` input data and
`M` adjusted constants: the observed values `y`, their standard
uncertainties `u`, their correlation coefficients `r`, the design matrix
`A` and the offset vector `b` of the observational equations
`y i = sum_k A i k x k + b i`, and the weight matrix `G`, required to be
a two-sided inverse of the covariance matrix with entries
`r i j * u i * u j` (section XII of the 2022 CODATA report: the input
data enter the adjustment together with their uncertainties and their
correlations, and the weights are the inverse covariance matrix). -/
structure LSQ (N M : ℕ) where
  /-- the observed input data -/
  y : Fin N → ℝ
  /-- the standard uncertainties of the input data -/
  u : Fin N → ℝ
  /-- the correlation coefficients of the input data -/
  r : Fin N → Fin N → ℝ
  /-- the design matrix of the observational equations -/
  A : Matrix (Fin N) (Fin M) ℝ
  /-- the offset vector of the observational equations -/
  b : Fin N → ℝ
  /-- the weight matrix of the adjustment -/
  G : Matrix (Fin N) (Fin N) ℝ
  /-- the weight matrix is a two-sided inverse of the covariance
  matrix of the data: both products reproduce the identity matrix,
  written entry by entry -/
  G_is_inv :
    (∀ i j, ∑ k, r i k * u i * u k * G k j = if i = j then 1 else 0) ∧
      (∀ i j, ∑ k, G i k * (r k j * u k * u j) = if i = j then 1 else 0)

/-- The residual of the i-th observational equation at the parameter
vector x: the observed value minus the fitted value plus the offset. -/
def resid {N M : ℕ} (L : LSQ N M) (x : Fin M → ℝ) : Fin N → ℝ :=
  fun i => L.y i - (L.A.mulVec x i + L.b i)

/-- The chi-square statistic of the weighted residuals at the
parameter vector x, relative to the weight matrix G of the adjustment
(section XII: the final 2022 adjustment has chi^2 = 44.2). -/
def chiSq {N M : ℕ} (L : LSQ N M) (x : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, resid L x i * L.G i j * resid L x j

/-- The statement that x solves the normal equations of the weighted
least-squares problem: every column of the design matrix is orthogonal,
relative to the weight matrix, to the residual vector at x. -/
def SolvesNormal {N M : ℕ} (L : LSQ N M) (x : Fin M → ℝ) : Prop :=
  ∀ k, ∑ i, ∑ j, L.A i k * L.G i j * resid L x j = 0

/-- The statement that x minimizes the chi-square statistic over all
parameter vectors. -/
def Minimizes {N M : ℕ} (L : LSQ N M) (x : Fin M → ℝ) : Prop :=
  ∀ z, chiSq L x ≤ chiSq L z

/-- The normal matrix of the weighted least-squares problem, with
entries sum_i sum_j A i k G i j A j l. -/
def normalMat {N M : ℕ} (L : LSQ N M) :
    Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun k l => ∑ i, ∑ j, L.A i k * L.G i j * L.A j l

/-- The statement that C is a two-sided inverse of the normal matrix,
written entry by entry: for a full-rank design matrix, C is the
covariance matrix of the adjusted constants, from which the recommended
values together with their uncertainties and covariances are obtained
(section XII). -/
def IsCov {N M : ℕ} (L : LSQ N M) (C : Matrix (Fin M) (Fin M) ℝ) : Prop :=
  (∀ k l, ∑ j, normalMat L k j * C j l = if k = l then 1 else 0) ∧
    (∀ k l, ∑ j, C k j * normalMat L j l = if k = l then 1 else 0)

/-- The statement that a square real matrix is symmetric and strictly
positive definite: the associated quadratic form is positive on every
nonzero vector. -/
def IsSPD {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, G i j = G j i) ∧
    ∀ v : Fin N → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * G i j * v j

/-- The covariance matrix of the input data: the entry in position
(i, j) is the correlation coefficient r i j multiplied by the two
standard uncertainties. -/
def covMat {N M : ℕ} (L : LSQ N M) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => L.r i j * L.u i * L.u j

/-- The number of degrees of freedom of an adjustment with N input data
and M adjusted constants, nu = N - M as in section XII: 133 - 79 = 54
for the main 2022 adjustment, and 16 - 1 = 15 for the separate
adjustment of the sixteen values of the Newtonian constant of
gravitation. -/
def dof (N M : ℕ) : ℕ := N - M

/-- The Birge ratio of an adjustment at the parameter vector x:
R_B = sqrt(chiSq/nu) with nu = N - M, as defined in section XII
(R_B = sqrt(chi^2/nu) is the Birge ratio; the printed values of the
2022 adjustment are 0.90 for the main adjustment and 0.93 for the
Newtonian constant of gravitation). -/
noncomputable def birge {N M : ℕ} (L : LSQ N M) (x : Fin M → ℝ) : ℝ :=
  Real.sqrt (chiSq L x / (dof N M : ℝ))

end CODATA


