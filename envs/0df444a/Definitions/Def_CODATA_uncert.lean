-- Prove2me | Definitions.Def_CODATA_uncert
-- name    : CODATA_uncert
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T01:29:59.306489+00:00
-- url     : https://prove2.me/theorems/9747730e-62a8-4e8e-8fe4-d3ed29ee38c9
-- title:
--   Correlations, uncertainty expansion, and the propagation of relative uncertainty
-- statement:
--   The second layer of the adjustment formalism. The correlation
--   coefficient of an entry of a covariance matrix is the entry divided
--   by the square roots of the two diagonal entries. The expansion of a
--   covariance matrix V by a family of positive factors fs is the matrix
--   with entries fs k * fs l * V k l: when the same factor is applied to
--   both members of a pair, the covariance is multiplied by the square of
--   the factor, and the correlation coefficient is unchanged. This is the
--   mechanism by which the 2022 adjustment applies an expansion factor to
--   the uncertainties of a group of input data (1.7 and 2.5 in the main
--   adjustment, 3.9 in the separate adjustment of the Newtonian constant
--   of gravitation) while maintaining the original relative weights and
--   correlations of the data. The relative variance of a value x with
--   standard uncertainties u and covariance matrix V, under a linear
--   combination with sensitivity vector p, is the law of propagation of
--   uncertainty for relative uncertainties: the double sum of
--   p k * p l * (correlation of k and l) * (u k / |x k|) * (u l / |x l|),
--   by which the recommended values and their uncertainties are obtained
--   from the adjusted constants.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII: the expansion factors 1.7 and 2.5 applied to the uncertainties of groups of data so as to reduce all normalized residuals to two or less while maintaining their original relative weights and correlations, the expansion factor 3.9 of the separate adjustment of the sixteen values of G, and the propagation of the covariances of the adjusted constants to the recommended values.

import Mathlib
import Definitions.Def_CODATA_lsa

/-!
# The CODATA 2022 adjustment: correlations and uncertainty propagation

The second definition bundle of the mission: the correlation
coefficient of a covariance matrix, the expansion of a covariance
matrix by per-entry factors, and the law of propagation of
uncertainty for a linear combination, in the form used by section XII
of the 2022 CODATA report (J. Phys. Chem. Ref. Data 54, 033105 (2025);
Rev. Mod. Phys. 97, 025002 (2025)). The adjustment applies expansion
factors to the uncertainties of groups of input data (1.7 and 2.5 in
the main adjustment, 3.9 in the separate adjustment of the Newtonian
constant of gravitation) so as to reduce all normalized residuals to
two or less, while maintaining the original relative weights and
correlations of the data; the recommended values are then obtained from
the adjusted constants by propagating their covariances.
-/

namespace CODATA

/-- The correlation coefficient of the (i, j) entry of a covariance
matrix V: the entry divided by the square roots of the two diagonal
entries. -/
noncomputable def corr {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  V i j / Real.sqrt (V i i * V j j)

/-- The expansion of a covariance matrix V by per-entry factors fs:
the (k, l) entry is fs k * fs l * V k l. When the same factor is
applied to both members of a pair, the covariance is multiplied by the
square of the factor, and the ratio defining the correlation
coefficient is unchanged; this is the mechanism by which an expansion
factor applied to the uncertainties of a group of data maintains their
original relative weights and correlations (section XII). -/
def expandD {N : ℕ} (fs : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k l => fs k * fs l * V k l

/-- The relative variance of a value x with standard uncertainties u
and covariance matrix V, under the linear combination with sensitivity
vector p: the law of propagation of uncertainty applied to relative
uncertainties, the covariance matrix entering through its correlation
coefficients. -/
noncomputable def relVar {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ)
    (u x p : Fin N → ℝ) : ℝ :=
  ∑ k, ∑ l, p k * p l * corr V k l * (u k / abs (x k)) * (u l / abs (x l))

end CODATA


