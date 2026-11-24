-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionConjugacy
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionConjugacy
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:21.888313+00:00
-- url     : https://prove2.me/theorems/b837615c-8c0a-4572-9ed4-5702c929a9a2
-- title:
--   Reduction Conjugacy
-- statement:
--   Definitions and structural lemmas for Reduction Conjugacy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
namespace Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
section
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))
def ivH : (Fin I.n → I.E) →+ (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  AddMonoidHom.mk' (iv I) (DictLat.iv_add I)
def TH (x : I.Gf) : (Fin I.n → I.E ⊗[I.F] Af I.F) →+ (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  (Matrix.mulVecLin (I.fmat x)).toAddMonoidHom
end
end Formalism.L2.SG.Pf.RedConj0Pf


