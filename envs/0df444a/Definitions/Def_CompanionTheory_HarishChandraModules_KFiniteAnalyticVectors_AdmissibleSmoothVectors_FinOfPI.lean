-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:15.409665+00:00
-- url     : https://prove2.me/theorems/b4d35717-3412-40f4-afdf-93731e98772e
-- title:
--   Fin Of PI
-- statement:
--   Definitions and structural lemmas for Fin Of PI, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinOfPI.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace CompanionTheory.D.gk.admitted
namespace FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def diag (T : H →L[ℂ] H) : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm : (ι → H) →L[ℂ] PiLp 2 (fun _ : ι => H)).comp
    (ContinuousLinearMap.pi fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i))
def incl (j : ι) : H →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm : (ι → H) →L[ℂ] PiLp 2 (fun _ : ι => H)).comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) j)
section Rank
variable (E : H →L[ℂ] H) (M : ℕ) (φ : ℕ → H →L[ℂ] ℂ) (x : ℕ → H)
end Rank
end FinOfPIAux
end CompanionTheory.D.gk.admitted


