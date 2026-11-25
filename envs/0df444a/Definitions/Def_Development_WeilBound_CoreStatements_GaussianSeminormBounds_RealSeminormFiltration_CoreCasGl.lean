-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:13.411825+00:00
-- url     : https://prove2.me/theorems/4b232441-9fc2-5b78-a22d-6886151b008a
-- title:
--   Core Cas Gl
-- statement:
--   Definitions and structural lemmas for Core Cas Gl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasGl.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_FockRL_sameBlock_symm
import Theorems.Thm_PI_FHS_sameBlock_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
namespace CasGl
variable {r s : ℕ}
abbrev KI (r s : ℕ) : Type := {ab : Ix r s × Ix r s // sameBlock ab.1 ab.2}
abbrev PIx (r s : ℕ) : Type := {ab : Ix r s × Ix r s // ¬ sameBlock ab.1 ab.2}
def swK (k : KI r s) : KI r s := ⟨(k.1.2, k.1.1), PI.FHS.sameBlock_symm k.2⟩
def adC (k : KI r s) : Matrix (PIx r s) (PIx r s) ℂ := fun j i =>
  ((Eab k.1.1 k.1.2 * Eab i.1.1 i.1.2 - Eab i.1.1 i.1.2 * Eab k.1.1 k.1.2 : Mat r s)) j.1.1 j.1.2
end CasGl
end PositivityTheory.KReal
end


