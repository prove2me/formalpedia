-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_KPolynomials
-- name    : DetSupportRank_DeterminantSupport_KPolynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:57.094192+00:00
-- url     : https://prove2.me/theorems/3d309afc-67a5-491b-a5da-ccf34ebfb6e3
-- title:
--   Resolution-defined Laurent K-polynomials
-- statement:
--   For an actual finite graded free resolution $F_\bullet\to M$, with basis shifts $s_{i,j}$, set
--   $$\operatorname{Euler}(F_\bullet)=\sum_{i=0}^{\ell}(-1)^i\sum_j t^{s_{i,j}}.$$
--   The resolution-defined K-polynomial selects the Euler polynomial of a finite graded free resolution if one exists; its total extension is zero otherwise. Theorem 5.9 supplies existence on the source domain. A separate supporting theorem states equality with the Euler polynomial of every resolution, so independence is mathematical content. Regrading acts by the corresponding map of integer exponent vectors.
--
--   This construction remains a finite Laurent polynomial when the regraded homogeneous components are infinite dimensional. It never substitutes a finite rank for those infinite dimensions.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §5.3, resolution-defined K-polynomials, p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_FreeResolutions

noncomputable section
open scoped BigOperators
universe uDSK

namespace DetSupportRank.DeterminantSupport

/-- Alternating Laurent polynomial of the shifts in a genuine free resolution (§5.3, p.19). -/
def resolutionEuler {K : Type uDSK} [Field K] {V D : Type}
    {p : V → D → ℤ} {M : GradedModuleData K V D}
    (R : FiniteGradedResolution p M) : AddMonoidAlgebra ℤ (D → ℤ) :=
  ∑ i ∈ Finset.range (R.length + 1), ∑ j : Fin (R.rank i),
    AddMonoidAlgebra.single (R.shift i j) ((-1 : ℤ) ^ i)

/-- Resolution-defined K-polynomial. Resolution independence is not assumed in this definition.
The source's existence/independence statements are separate theorem targets. The fallback is zero
only if no finite graded free resolution exists, outside the finitely generated graded domain. -/
def kPolynomial {K : Type uDSK} [Field K] {V D : Type}
    (p : V → D → ℤ) (M : GradedModuleData K V D) : AddMonoidAlgebra ℤ (D → ℤ) := by
  classical
  exact if h : Nonempty (FiniteGradedResolution p M) then
    resolutionEuler (Classical.choice h) else 0

/-- The integer degree map on Laurent monomials; also encodes forgetting one grading. -/
def regradeLaurent {D E : Type} (L : (D → ℤ) → (E → ℤ))
    (Q : AddMonoidAlgebra ℤ (D → ℤ)) : AddMonoidAlgebra ℤ (E → ℤ) :=
  Q.coeff.sum fun u c => AddMonoidAlgebra.single (L u) c

end DetSupportRank.DeterminantSupport


