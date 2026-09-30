-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ElementaryLocusSamples
-- name    : WeierstrassEllipticZeta_ElementaryLocusSamples
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T16:34:37.045191+00:00
-- url     : https://prove2.me/theorems/8505586a-b843-47cf-99ad-245d2c6686df
-- title:
--   Finite sample sets for elementary affine loci
-- statement:
--   For an elementary affine locus with anchor r in covering coordinates (t,z,u),
--   define a finite set of sample points for a polynomial of bidegree (m,n):
--
--   - Point: just r.
--   - Line of slope α: r+(j,0,αj), for integers 0≤j≤m+n.
--   - Whole fibre: r+(i,0,j), for integers 0≤i≤m and 0≤j≤n.
--
--   The integers are mapped into ℂ. The definition contains only these points. Its
--   sample cardinalities, containment in the locus, and sufficiency for testing
--   polynomial vanishing are proved in the companion theorem. It does not choose
--   the complex anchor or slope, and does not bound the canonical chart cost.
-- source:
--   Derived finite interpolation criterion for the mission's elementary locus-vanishing condition. At a fixed elliptic coordinate, substituting univariate polynomials T,U gives degree at most m*deg(T)+n*deg(U). The line restriction has degree at most m+n and is tested at m+n+1 integer parameters. A whole fibre is tested on an (m+1) by (n+1) integer grid, using the separate degree bounds m and n. The proof uses Mathlib's polynomial root-count theorem, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean. This is supporting coordinate algebra for the locus-selection framework, not a claim that Philippon (1986), section 5, is fully formalized: https://www.numdam.org/item/10.24033/bsmf.2060.pdf. No platform theorem dependencies are used by the complete proof. The forward sketch and full converse preserve all witnesses, the local cost, and C. Selecting a successful complex anchor/slope and proving the global cost bound remain open; the finite sample count is not an integer-search bound.

import Definitions.Def_WeierstrassEllipticZeta_ElementaryLoci
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

/-- Integer parameter samples sufficient to test a bihomogeneous polynomial on an
elementary affine locus. The theorem establishing sufficiency is separate. -/
def elementaryLocusSamples (shape : ElementaryLocusShape) (r : Fin 3 → ℂ)
    (m n : ℕ) : Finset (Fin 3 → ℂ) :=
  match shape with
  | .point => {r}
  | .line α => (Finset.range (m + n + 1)).image
      (fun j : ℕ => r + ![(j : ℂ), 0, α * (j : ℂ)])
  | .fibre => ((Finset.range (m + 1)).product (Finset.range (n + 1))).image
      (fun ij : ℕ × ℕ => r + ![(ij.1 : ℂ), 0, (ij.2 : ℂ)])

end WeierstrassEllipticZeta


