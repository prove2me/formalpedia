-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_FourThirdsBoundary
-- name    : ConsistentSubmodular_Deterministic_Certificates_FourThirdsBoundary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:23.225323+00:00
-- url     : https://prove2.me/theorems/209bd9ba-7b68-42ea-b67f-4b5113883701
-- title:
--   Four-thirds boundary edge: discriminant, base and boundary margin, and the boundary polynomial
-- statement:
--   The actual-constructor descent in the $3/4$-certificate selector has a threshold parameter $4/3$, and the edge on the credit boundary is analysed through explicit real-valued expressions in $p$ (parent residual), $d$ (designated residual), the relay parameter $q$ and the edge coordinate $z \in [0,1]$.
--
--   - `fourThirdsDiscriminant p d` is $-3d^2 + (2p - \tfrac14)\,d + (-p^2 + \tfrac p2)$.
--   - `fourThirdsBaseDelta p d` is $-\tfrac5{16} + \tfrac92 d - 2p$ and `fourThirdsBaseOverlap p d` is $\tfrac{25}{16} - \tfrac{23}2 d + 3p$; these are the linear and overlap coefficients at $q = 4/3$.
--   - `fourThirdsBoundaryWeight p d q` is $w = 2(1-d) - 3(1-4d)/q - (p+d)$.
--   - `fourThirdsBoundaryDelta p d q` is $\delta = \bigl((3-q)\,w - (p+d) - 3d\bigr)/q$.
--   - `fourThirdsBoundaryOverlap p d q` is $o = 1 - d - \delta - w$.
--   - `fourThirdsBoundaryMargin p d q z` is the edge margin $\tfrac14 - d - \delta z - o\,z(1-z)$, with $\delta, o$ as above.
--   - `fourThirdsBoundaryPolynomial p d q z` is
--   $$q^2\bigl(\tfrac14 - d + (1-p-2d)z + (1-d)z^2\bigr) + q\bigl((-3+12d)z + (-6+13d+4p)z^2\bigr) + (9-36d)z^2,$$
--   the numerator of the margin after clearing denominators.
--
--   The file also proves that the margin is nonnegative on the unit interval: for the base edge at $q = 4/3$ and for the credit-boundary edge for every parameter $q \ge 4/3$, under the standing bounds on $p$ and $d$. The residuals involved need not form a feasible atomic profile.
--
--   These expressions certify the boundary edge in the four-thirds descent of the selector used for the $3/4$ checkpoint certificates (Theorem 7).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/FourThirdsBoundary.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry

noncomputable section

namespace ConsistentSubmodular

def fourThirdsDiscriminant (p d : ℝ) : ℝ :=
  -3 * d ^ 2 + (2 * p - 1 / 4) * d + (-p ^ 2 + p / 2)

def fourThirdsBaseDelta (p d : ℝ) : ℝ := -5 / 16 + (9 : ℝ) / 2 * d - 2 * p

def fourThirdsBaseOverlap (p d : ℝ) : ℝ := 25 / 16 - (23 : ℝ) / 2 * d + 3 * p

def fourThirdsBoundaryWeight (p d q : ℝ) : ℝ :=
  2 * (1 - d) - 3 * (1 - 4 * d) / q - (p + d)

def fourThirdsBoundaryDelta (p d q : ℝ) : ℝ :=
  ((3 - q) * fourThirdsBoundaryWeight p d q - (p + d) - 3 * d) / q

def fourThirdsBoundaryOverlap (p d q : ℝ) : ℝ :=
  1 - d - fourThirdsBoundaryDelta p d q - fourThirdsBoundaryWeight p d q

def fourThirdsBoundaryMargin (p d q z : ℝ) : ℝ :=
  1 / 4 - d - fourThirdsBoundaryDelta p d q * z -
    fourThirdsBoundaryOverlap p d q * z * (1 - z)

def fourThirdsBoundaryPolynomial (p d q z : ℝ) : ℝ :=
  q ^ 2 * (1 / 4 - d + (1 - p - 2 * d) * z + (1 - d) * z ^ 2) +
    q * ((-3 + 12 * d) * z + (-6 + 13 * d + 4 * p) * z ^ 2) +
    (9 - 36 * d) * z ^ 2

end ConsistentSubmodular

end


