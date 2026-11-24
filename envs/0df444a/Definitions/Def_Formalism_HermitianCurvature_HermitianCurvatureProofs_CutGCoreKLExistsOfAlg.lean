-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:35.152822+00:00
-- url     : https://prove2.me/theorems/5aa860b7-2e21-4001-b5be-27e8b5557a3e
-- title:
--   Cut GCore KLExists Of Alg
-- statement:
--   Definitions and structural lemmas for Cut GCore KLExists Of Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
section Int
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
end Int
section Restr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
def resE (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) : Fin n → Fin n → Module.End ℂ S :=
  fun a b => (E a b).restrict (hS a b)
end Restr
section Proj
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}
def projI (h : DirectSum.IsInternal S) (i : ι) : V →ₗ[ℂ] S i :=
  (DirectSum.component ℂ ι (fun j => S j) i).comp (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm.toLinearMap
end Proj
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA


