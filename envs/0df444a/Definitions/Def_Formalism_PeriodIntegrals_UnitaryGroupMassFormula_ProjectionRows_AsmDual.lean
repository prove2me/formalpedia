-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmDual
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:45.479557+00:00
-- url     : https://prove2.me/theorems/5719d1dc-4652-45fa-b8fa-597a89c3a369
-- title:
--   Asm Dual
-- statement:
--   Definitions and structural lemmas for Asm Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmDual.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
def Adapted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∃ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) ∧
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e ∧
      Submodule.span K (Set.range u) = U ∧
      (∀ i, Fin.append u z i ∈ cutE A e A.L) ∧
      LinearIndependent K y ∧ (∀ i, y i ∈ lamSub A e h U) ∧
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) ∧
      (cutE A e A.L).FG ∧ (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)).FG ∧
      Submodule.span K (cutE A e A.L : Set A.V) = Submodule.span K (Set.range (Fin.append u z)) ∧
      Submodule.span K ((cutE A e A.L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) A.V) : Set A.V) =
        Submodule.span K (Set.range u)
end PI.DvRows


