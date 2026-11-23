-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:21:35.162529+00:00
-- url     : https://prove2.me/theorems/8bb4e28f-fb78-45ed-b694-4bad67618c7d
-- title:
--   Semidirect Exists Of Parts
-- statement:
--   Definitions and structural lemmas for Semidirect Exists Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemidirectExistsOfParts.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SubgroupLocallyCompactHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProdHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.ExS
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.VolSemiDirect.W
open scoped TensorProduct
def SCAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], SecondCountableTopology (Af F)
section Ext
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
def SemiNHS : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    Semi (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)
def ConjNH : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ConjInv (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)
variable {F E σ M J}
end Ext
def SemiNHSAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => SemiNHS F E σ M J
def ConjNHAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => ConjNH F E σ M J
end PI.LevelKSplit.W.ExS


