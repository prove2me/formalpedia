-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:06.341323+00:00
-- url     : https://prove2.me/theorems/95cda792-1ef6-491e-8e95-fbd2c08647dc
-- title:
--   WModel
-- statement:
--   Definitions and structural lemmas for WModel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace Formalism.InvariantFactorPaths.G7
namespace WModel
variable (p : ℕ) [hp : Fact p.Prime]
abbrev WW : Type := WittVector p (AlgebraicClosure (ZMod p))
abbrev KK : Type := FractionRing (WW p)
theorem one_lt_b : (1 : ℝ≥0) < (p : ℝ≥0) := by exact_mod_cast hp.out.one_lt
def abv : AbsoluteValue (KK p) ℝ :=
  (IsDiscreteValuationRing.maximalIdeal (WW p)).adicAbv (one_lt_b p)
theorem frob_nzd : nonZeroDivisors (WW p) ≤
    Submonoid.comap (WittVector.frobenius : WW p →+* WW p) (nonZeroDivisors (WW p)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (WittVector.frobenius_bijective p _).injective
def sig : KK p →+* KK p :=
  IsLocalization.map (KK p) (WittVector.frobenius : WW p →+* WW p) (frob_nzd p)
@[reducible] def nf : NormedField (KK p) := (abv p).toNormedField
attribute [local instance] nf
end WModel
end Formalism.InvariantFactorPaths.G7


