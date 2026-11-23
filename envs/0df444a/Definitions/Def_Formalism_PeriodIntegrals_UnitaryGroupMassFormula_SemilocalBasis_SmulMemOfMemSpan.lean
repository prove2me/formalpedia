-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_SmulMemOfMemSpan
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_SmulMemOfMemSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:31.951498+00:00
-- url     : https://prove2.me/theorems/b38fd4b6-5977-4ef9-8e68-07bf8f823fbf
-- title:
--   Smul Mem Of Mem Span
-- statement:
--   Definitions and structural lemmas for Smul Mem Of Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemilocalBasis/SmulMemOfMemSpan.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisSemi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocBasisSemi
variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
abbrev T : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) (Ideal.span {(p : ℤ)}).primeCompl
theorem T_le : T K p ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
    (Ideal.primeCompl_le_nonZeroDivisors _)
abbrev A : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (T K p) (T_le K p)
variable {K p}
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end PI.UnitaryGroupMassFormula.LocBasisSemi


