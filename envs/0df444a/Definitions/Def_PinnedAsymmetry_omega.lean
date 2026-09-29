-- Prove2me | Definitions.Def_PinnedAsymmetry_omega
-- name    : PinnedAsymmetry_omega
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-23T22:29:32.068982+00:00
-- url     : https://prove2.me/theorems/7d1fcac9-7c6f-4633-8138-5bff9e340b53
-- title:
--   Upper-branch frequency $\omega(q)$ on a uniform gyroscopic ring
-- statement:
--   Fix real numbers $K$ (on-site stiffness), $c$ (neighbour coupling), $\beta$ (gyroscopic strength) and a wavenumber $q$. The **upper-branch frequency** of a wave with wavenumber $q$ on a uniform ring is
--
--   $$
--   \omega(q) = \beta c \sin q + \sqrt{\bigl(\beta c \sin q\bigr)^2 + K + 2c\,(1 - \cos q)} .
--   $$
--
--   When the quantity under the square root is non-negative, $\omega(q)$ is a root of the dispersion relation $\omega^2 - 2\beta c \sin q\,\omega - (K + 2c(1-\cos q)) = 0$ (milestone M1).
--
--   **Formalization Note** The square root is `Real.sqrt`, which returns $0$ on negative inputs; no sign conditions are placed on $K, c, \beta, q$.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §7, Theorem 7.1 (dispersion relation): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", "Related: the pinned asymmetry (Section 7)": https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib

open Real

namespace PinnedAsymmetry

/-- Upper-branch frequency on a uniform ring: stiffness K, neighbour coupling c,
gyroscopic strength β, wavenumber q. -/
noncomputable def omega (K c β q : ℝ) : ℝ :=
  β * c * sin q + Real.sqrt ((β * c * sin q) ^ 2 + K + 2 * c * (1 - cos q))

end PinnedAsymmetry


