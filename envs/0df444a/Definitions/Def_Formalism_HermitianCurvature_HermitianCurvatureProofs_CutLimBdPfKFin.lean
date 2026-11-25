-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLimBdPfKFin
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLimBdPfKFin
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:25:42.242209+00:00
-- url     : https://prove2.me/theorems/5c03dd09-c2e2-552c-b44e-ed4a5b33884b
-- title:
--   Cut Lim Bd Pf KFin
-- statement:
--   Definitions and structural lemmas for Cut Lim Bd Pf KFin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutLimBdPfKFin.lean

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_HermitianCurvature_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.CutBP
noncomputable section
def KFinDSCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : B.Mat k r → (H →L[ℂ] H)) (Pm : H →L[ℂ] Wp) (Qm : Wq →L[ℂ] H),
    PI.UpqRep.IsHCParam lam ∧ PI.UpqRep.IsDSHpk k r ε lam σ ∧
    (∀ w, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (Qm w)) ∧
    (∀ x, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (ContinuousLinearMap.adjoint Pm x)) ∧
    ∀ g ∈ B.GV k r, F g = Pm.comp ((σ g).comp Qm)
end
end Formalism.FourierDecayAlt.P.CutBP


