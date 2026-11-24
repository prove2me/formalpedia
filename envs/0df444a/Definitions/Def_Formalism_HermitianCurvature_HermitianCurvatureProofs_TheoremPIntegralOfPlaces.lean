-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:14.10281+00:00
-- url     : https://prove2.me/theorems/4f945c01-3520-4f9c-9978-6feb566823c4
-- title:
--   Theorem PIntegral Of Places
-- statement:
--   Definitions and structural lemmas for Theorem PIntegral Of Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TheoremPIntegralOfPlaces.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1
open NumberField
end Formalism.FourierDecayAlt.P.JCx1
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
section cutf
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.JCx1
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.JCx1
namespace Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
end cutf
section lemE
open Formalism.FourierDecayAlt Filter Topology
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end lemE
section decayPart
open Finset Formalism.FourierDecayAlt
noncomputable section decayNC
namespace Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)
end Formalism.FourierDecayAlt.P.JCx1.decay
end decayNC
end decayPart
section needsPart
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
namespace Formalism.FourierDecayAlt.P.JCx1.needs
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.JCx1.needs
noncomputable section
section meas
open scoped Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
def cpx (c : J.CV E) : {w : InfinitePlace E // w.IsComplex} → ℂ := (Formalism.FourierDecayAlt.P.Jx2.ee E c).2
variable {E} {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
def eqv (S : C.HidaSetting E Wp Wq) : Fin S.f ≃ {w : InfinitePlace E // w.IsComplex} :=
  S.pl.trans (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w)).symm
def Qm (S : C.HidaSetting E Wp Wq) (c : J.CV E) : Fin S.f → ℂ :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (eqv S).symm (cpx E c)
end meas
end
end Formalism.FourierDecayAlt.P.JCx1.needs
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end needsPart


