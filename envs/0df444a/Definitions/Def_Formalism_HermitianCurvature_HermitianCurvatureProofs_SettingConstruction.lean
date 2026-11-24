-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:07.815099+00:00
-- url     : https://prove2.me/theorems/da5e33af-89bc-4248-bda7-ce29422fbba1
-- title:
--   Setting Construction
-- statement:
--   Definitions and structural lemmas for Setting Construction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section forms
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
variable [DecidableEq ι]
def rk (d : ι → ℂ) (θ β : ℂ) : Matrix ι ι ℂ := θ • (1 : Matrix ι ι ℂ) + β • (vecMulVec d (star d) * H)
end forms
section hb
variable (k : ℕ)
def nu (w s : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  1 + vecMulVec ((star w - 1) • Pi.single 0 1 + s • Pi.single (Fin.last k) 1) (Pi.single 0 1) +
    vecMulVec (s • Pi.single 0 1 + (w - 1) • Pi.single (Fin.last k) 1) (Pi.single (Fin.last k) 1)
end hb
section mid
variable (k r : ℕ)
end mid
end Formalism.FourierDecayAlt.P.SettingConstruction
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P


