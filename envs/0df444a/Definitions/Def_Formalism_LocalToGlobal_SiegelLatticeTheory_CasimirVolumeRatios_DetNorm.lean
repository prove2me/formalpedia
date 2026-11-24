-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirVolumeRatios_DetNorm
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirVolumeRatios_DetNorm
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:14.918247+00:00
-- url     : https://prove2.me/theorems/fd3ad363-51b6-4805-ac3a-1f3758eed9cb
-- title:
--   Det Norm
-- statement:
--   Definitions and structural lemmas for Det Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CasimirVolumeRatios/DetNorm.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.S.S7.GLOne
open NumberField
open scoped TensorProduct
open Formalism.MainNotions.S
variable (I : AutInst)
abbrev AEf : Type := I.E ⊗[I.F] Af I.F
abbrev GLf (j : ℕ) : Type := GL (Fin j) (AEf I)
abbrev GLinf (j : ℕ) : Type := InfinitePlace I.F → GL (Fin j) ℂ
abbrev GLA (j : ℕ) : Type := GLinf I j × GLf I j
def ratGL (j : ℕ) : GL (Fin j) I.E →* GLA I j :=
  MonoidHom.prod (MonoidHom.pi fun v => Matrix.GeneralLinearGroup.map (I.φ v))
    (Matrix.GeneralLinearGroup.map (Formalism.UG.inclE (F := I.F) (Af I.F)))
def idl (u : (AEf I)ˣ) : Submodule (𝓞 I.E) I.E :=
  Submodule.span (𝓞 I.E)
    {e : I.E | ((u⁻¹ : (AEf I)ˣ) : AEf I) * Formalism.UG.inclE (F := I.F) (Af I.F) e ∈ IntAf I.F I.E}
open Classical in

def nrmF (u : (AEf I)ˣ) : ℝ :=
  if h : IsFractional (nonZeroDivisors (𝓞 I.E)) (idl I u) then
    ((FractionalIdeal.absNorm (⟨idl I u, h⟩ : FractionalIdeal (nonZeroDivisors (𝓞 I.E)) I.E) : ℚ) : ℝ)⁻¹
  else 0
def detNorm {j : ℕ} (m : GLA I j) : ℝ :=
  nrmF I (Matrix.GeneralLinearGroup.det m.2) *
    ∏ v, ‖((Matrix.GeneralLinearGroup.det (m.1 v) : ℂˣ) : ℂ)‖ ^ 2
end Formalism.L2.S.S7.GLOne
end


