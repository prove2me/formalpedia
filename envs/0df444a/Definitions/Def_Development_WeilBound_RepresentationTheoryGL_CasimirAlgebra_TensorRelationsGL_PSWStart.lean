-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStart
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:22.444275+00:00
-- url     : https://prove2.me/theorems/1a7ead35-b578-437c-9ddd-32b0ff467e32
-- title:
--   PSWStart
-- statement:
--   Definitions and structural lemmas for PSWStart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PSWStart.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix MeasureTheory
namespace PositivityTheory.Rg.Cz
namespace SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
section Int
variable [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
variable {M : Type} [AddCommGroup M] [Module ℂ M]
end Int
end SWS
end PositivityTheory.Rg.Cz
end


