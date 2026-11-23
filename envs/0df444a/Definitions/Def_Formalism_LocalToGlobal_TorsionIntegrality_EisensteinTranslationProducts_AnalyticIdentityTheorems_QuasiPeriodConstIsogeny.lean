-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:16.132825+00:00
-- url     : https://prove2.me/theorems/449d24a8-dd24-4b27-9a6c-9e20c759fc32
-- title:
--   Quasi Period Const Isogeny
-- statement:
--   Definitions and structural lemmas for Quasi Period Const Isogeny, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstIsogeny.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace S2IsogenyPsi
def dom (L : PeriodPair) (α : ℂ) : Set ℂ := {z | α * z ∉ L.lattice}
def psi (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (z : ℂ) : ℂ :=
  α * wZeta L (α * z) - wZeta L z - ∑ P ∈ S, wZeta L (z + P) - (∑ P ∈ S, L.weierstrassP P) * z
end S2IsogenyPsi
end Formalism.L2.Th1.F


