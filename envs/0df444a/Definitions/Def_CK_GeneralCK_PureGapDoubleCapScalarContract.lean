-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapScalarContract
-- name    : CK_GeneralCK_PureGapDoubleCapScalarContract
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:02:40.244387+00:00
-- url     : https://prove2.me/theorems/19e62a7c-f9bc-4fdf-8ced-c7f1f1a56344
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapScalarContract` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapScalarContract` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapScalarContract` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapScalarContract (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapScalarContract.lean)

import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_RadialConvexity

-- ===== source module GeneralCK.PureGapDoubleCapScalarContract =====
section

/-!
# Exact scalar contract for the zero-cutoff double-cap endpoint

This removes the piecewise entropy floor and unfolds `phi` into the actual
entropy inverse and radial contact.  It is a reduction only: no numerical
sign is asserted here.
-/

namespace GeneralCK

noncomputable def doubleCapEndpointResidual (m h : ℝ) : ℝ :=
  4 * (H m - h) -
    ((1 - 2 * entropyInverse h) * J (entropyInverse h) -
      (1 - 2 * m) * J (radialContact (1 - 2 * m) h))

theorem doubleCap_endpoint_iff_residual_nonneg {m h : ℝ}
    (hm : 0 < m) (hm1 : m < 1 / 2) (hh : 0 < h) (hh1 : h ≤ 1) :
    phi m h ≤ 4 * (H m - h) ↔ 0 ≤ doubleCapEndpointResidual m h := by
  have hz : 0 < 1 - 2 * m := by linarith
  unfold phi
  rw [eta_eq_profile hh.le hh1]
  simp only [F, abs_of_pos hz, if_neg hz.ne']
  unfold doubleCapEndpointResidual
  constructor <;> intro hineq <;> linarith

noncomputable def doubleCapLowResidual (m : ℝ) : ℝ :=
  doubleCapEndpointResidual m (H (2 * m) / 2)

noncomputable def doubleCapHighResidual (m : ℝ) : ℝ :=
  doubleCapEndpointResidual m ((1 + H (2 * m - 1 / 2)) / 2)

/-- Exact one-dimensional certificate interface.  The two fields have
disjoint interiors and share only the explicit switch point through `low`. -/
structure CanonicalDoubleCapResidualCertificate : Prop where
  low : ∀ m, 0 < m → m ≤ 1 / 4 → 0 ≤ doubleCapLowResidual m
  high : ∀ m, 1 / 4 < m → m < 1 / 2 → 0 ≤ doubleCapHighResidual m

theorem strict_doubleCap_endpoint_of_residual_certificate
    (cert : CanonicalDoubleCapResidualCertificate) :
    ∀ m, 0 < m → m < 1 / 2 →
      phi m (capEntropyFloor m) ≤ 4 * (H m - capEntropyFloor m) := by
  intro m hm hm1
  unfold capEntropyFloor
  split_ifs with hquarter
  · have hh : 0 < H (2 * m) / 2 :=
      div_pos (H_pos (by linarith) (by linarith)) two_pos
    have hh1 : H (2 * m) / 2 ≤ 1 := by
      linarith [H_le_one (2 * m)]
    exact (doubleCap_endpoint_iff_residual_nonneg hm hm1 hh hh1).2
      (cert.low m hm hquarter)
  · have hx0 : 0 < 2 * m - 1 / 2 := by linarith
    have hx1 : 2 * m - 1 / 2 < 1 := by linarith
    have hH0 : 0 ≤ H (2 * m - 1 / 2) := (H_pos hx0 hx1).le
    have hh : 0 < (1 + H (2 * m - 1 / 2)) / 2 := by linarith
    have hh1 : (1 + H (2 * m - 1 / 2)) / 2 ≤ 1 := by
      linarith [H_le_one (2 * m - 1 / 2)]
    exact (doubleCap_endpoint_iff_residual_nonneg hm hm1 hh hh1).2
      (cert.high m (lt_of_not_ge hquarter) hm1)

theorem canonicalDoubleCapEntropyEndpoints_of_residual_certificate
    (cert : CanonicalDoubleCapResidualCertificate) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_strict
    (strict_doubleCap_endpoint_of_residual_certificate cert)

#print axioms doubleCap_endpoint_iff_residual_nonneg
#print axioms strict_doubleCap_endpoint_of_residual_certificate
#print axioms canonicalDoubleCapEntropyEndpoints_of_residual_certificate

end GeneralCK

end


