-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_SmallRowEigenvalues
-- name    : Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_SmallRowEigenvalues
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:09.937907+00:00
-- url     : https://prove2.me/theorems/a017ab1b-cde8-45c6-90d4-b55116229e3d
-- title:
--   Small Row Eigenvalues
-- statement:
--   Definitions and structural lemmas for Small Row Eigenvalues, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/SmallRowEigenvalues.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N
def RowEigSmall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) :
    Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
    ∀ w : PlE H, IsSplitPl H w → A.unr (A.locW i σ w) →
      ∀ α ∈ A.frobEig (A.locW i σ w), ‖α‖ < ((normV w : ℕ) : ℝ) ^ (((R.t : ℝ) - 1) / 2)
end GlobalTheory.IndefiniteRowSideFullHecke.SmallBlockEigenvalues


