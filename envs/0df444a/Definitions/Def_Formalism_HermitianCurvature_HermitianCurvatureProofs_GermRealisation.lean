-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:50:55.077152+00:00
-- url     : https://prove2.me/theorems/236c1f97-7b6b-41ea-90fb-d1f5026b5263
-- title:
--   Germ Realisation
-- statement:
--   Definitions and structural lemmas for Germ Realisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermRealisation.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
section L2
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def gramL {ι : Type} (μ : Measure ℂ) (F G : ι × ℂ → ℂ → H) (p q : ι × ℂ) : ℂ :=
  ∫ D, ⟪F p D, G q D⟫_ℂ ∂μ
end L2
end
end Formalism.FourierDecayAlt.P.PBK


