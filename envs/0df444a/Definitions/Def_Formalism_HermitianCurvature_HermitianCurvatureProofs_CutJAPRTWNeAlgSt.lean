-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:41.357573+00:00
-- url     : https://prove2.me/theorems/2b885a05-cf20-404f-beda-578328a1720e
-- title:
--   Cut JAPRTWNe Alg St
-- statement:
--   Definitions and structural lemmas for Cut JAPRTWNe Alg St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlgSt.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
def TWNeAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V') (β β' : ℂ) (L L' : Fin (n + 1) → ℤ) (M M' : Fin n → ℤ) (i : Fin n),
    Hyp E β L → Hyp E' β' L' → Box L M → Box L' M' → Box L (Function.update M i (M i + 1)) →
    Box L' (Function.update M' i (M' i + 1)) → shf β M = shf β' M' →
    ∀ J : V' →ₗ[ℂ] V, J ≠ 0 → (∀ a b v, J (subA E' a b v) = subA E a b (J v)) →
    (∀ v, J v ∈ CapSp (subA E) (shf β M)) →
    ∃ v' : V', (∑ c, etaK E c (J (yK E' c v'))) ≠ 0 ∧
      (∑ c, etaK E c (J (yK E' c v'))) ∈ CapSp (subA E) (shf β (Function.update M i (M i + 1)))
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW


