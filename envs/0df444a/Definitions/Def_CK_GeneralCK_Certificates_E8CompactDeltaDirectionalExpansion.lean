-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8CompactDeltaDirectionalExpansion
-- name    : CK_GeneralCK_Certificates_E8CompactDeltaDirectionalExpansion
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:41:35.790536+00:00
-- url     : https://prove2.me/theorems/876a4f3b-3860-4f77-b7cf-a5d9fe42b047
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8CompactDeltaDirectionalExpansion` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8CompactDeltaDirectionalExpansion` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8CompactDeltaDirectionalExpansion` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8CompactDeltaDirectionalExpansion (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8CompactDeltaDirectionalExpansion.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorDeltaJet
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisMixedCoefficients

-- ===== source module GeneralCK.Certificates.E8CompactDeltaDirectionalExpansion =====
section

/-!
# Exact directional expansion of the regular E8 determinant jet

These are raw derivative coefficients: no Taylor factorial is hidden in a
`Jet5.dn` field.  The mixed terms are the existing bivariate product-rule
polynomials in `E8TAxisMixedCoefficients`.  The identities are algebraic and
therefore hold for arbitrary real inputs and directions, independently of
inverse-domain and dyadic enclosure premises.
-/

namespace GeneralCK.Certificates.E8CompactDeltaDirectionalExpansion

open GeneralCK
open GeneralCK.Certificates.E8CompactAnchorDeltaJet
open GeneralCK.Certificates.E8TAxisDeltaDirectionalJet
open GeneralCK.Certificates.E8TAxisMixedCoefficients

/-- First raw derivative along `(ds,dt)` from the two pure jets. -/
theorem deltaJet_directional_d1_expansion (s t ds dt : ℝ) :
    (deltaJet s t ds dt).d1 0 =
      (deltaJet s t 1 0).d1 0 * ds +
      (deltaJet s t 0 1).d1 0 * dt := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, zero_mul, mul_zero, add_zero, one_mul]
  ring

/-- Second raw derivative: the coefficient of `ds*dt` is twice the
mixed `(1,1)` derivative. -/
theorem deltaJet_directional_d2_expansion (s t ds dt : ℝ) :
    (deltaJet s t ds dt).d2 0 =
      (deltaJet s t 1 0).d2 0 * ds ^ 2 +
      2 * mixed qJet s t 1 1 * ds * dt +
      (deltaJet s t 0 1).d2 0 * dt ^ 2 := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, mixed, zero_mul, mul_zero, add_zero, one_mul]
  ring

/-- Third raw derivative, including the two order-three mixed coefficients.
The factors three are the binomial multiplicities, not Taylor normalizers. -/
theorem deltaJet_directional_d3_expansion (s t ds dt : ℝ) :
    (deltaJet s t ds dt).d3 0 =
      (deltaJet s t 1 0).d3 0 * ds ^ 3 +
      3 * mixed qJet s t 2 1 * ds ^ 2 * dt +
      3 * mixed qJet s t 1 2 * ds * dt ^ 2 +
      (deltaJet s t 0 1).d3 0 * dt ^ 3 := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, mixed, zero_mul, mul_zero, add_zero, one_mul]
  ring

/-- Translation of the directional third raw derivative to its current
point.  This makes the whole-square pure and mixed boxes available at the
unknown Taylor remainder point. -/
theorem deltaJet_directional_d3_translate (s0 t0 ds dt v : ℝ) :
    (deltaJet s0 t0 ds dt).d3 v =
      (deltaJet (s0 + ds * v) (t0 + dt * v) ds dt).d3 0 := by
  simp only [deltaJet, deltaGraph, sub, affine, Jet5.add, Jet5.neg,
    Jet5.mul, zero_mul, mul_zero, add_zero, one_mul]
  rw [show 2 * s0 + t0 + (2 * ds + dt) * v =
      2 * (s0 + ds * v) + (t0 + dt * v) by ring,
    show s0 + t0 + (ds + dt) * v =
      (s0 + ds * v) + (t0 + dt * v) by ring]

/-- Third derivative at any segment point in the raw pure/mixed
coefficient basis used by the checked whole-square boxes. -/
theorem deltaJet_directional_d3_expansion_at (s0 t0 ds dt v : ℝ) :
    (deltaJet s0 t0 ds dt).d3 v =
      (deltaJet (s0 + ds * v) (t0 + dt * v) 1 0).d3 0 * ds ^ 3 +
      3 * mixed qJet (s0 + ds * v) (t0 + dt * v) 2 1 * ds ^ 2 * dt +
      3 * mixed qJet (s0 + ds * v) (t0 + dt * v) 1 2 * ds * dt ^ 2 +
      (deltaJet (s0 + ds * v) (t0 + dt * v) 0 1).d3 0 * dt ^ 3 := by
  rw [deltaJet_directional_d3_translate]
  exact deltaJet_directional_d3_expansion (s0 + ds * v) (t0 + dt * v) ds dt

#print axioms deltaJet_directional_d1_expansion
#print axioms deltaJet_directional_d2_expansion
#print axioms deltaJet_directional_d3_expansion
#print axioms deltaJet_directional_d3_translate
#print axioms deltaJet_directional_d3_expansion_at

end GeneralCK.Certificates.E8CompactDeltaDirectionalExpansion

end


