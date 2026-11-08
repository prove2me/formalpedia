-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:42:12.136498+00:00
-- url     : https://prove2.me/theorems/017a0db6-aa1c-4618-af66-9ca4e2aa91f3
-- title:
--   LPSOriginal Native Holomorphic Extension
-- statement:
--   Definitions and structural lemmas for LPSOriginal Native Holomorphic Extension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeHolomorphicExtension.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_chart

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
lemma lpsOriginalNormalizedFilledCovector_meromorphic
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma) :
    lpsOriginalFilledCovectorChartMeromorphic N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro x z hz
  have he : lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) x =ᶠ[𝓝 z]
      toMeromorphicNFOn (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
        (chartAt ℂ x).target := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz] with w hw
    exact lpsOriginalNormalizedFilledCovector_chart N hN sigma hmer x w hw
  exact (meromorphicNFOn_toMeromorphicNFOn _ _ hz).meromorphicAt.congr
    (he.symm.filter_mono nhdsWithin_le_nhds)
def lpsOriginalNormalizedMeromorphicCovectorRepresentative
    (sigma : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :
    LPSOriginalFilledMeromorphicCovectorRepresentatives N hN :=
  ⟨lpsOriginalNormalizedFilledCovector N hN sigma.val,
    lpsOriginalNormalizedFilledCovector_meromorphic N hN sigma.val sigma.property⟩
end
end QEC.Coding.TannerLiftedProduct


