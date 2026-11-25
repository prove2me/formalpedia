-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ImportsAlt
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_ImportsAlt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:11:40.678353+00:00
-- url     : https://prove2.me/theorems/8ed30cb2-bd2a-590e-8865-286fd3224fbb
-- title:
--   Imports Alt
-- statement:
--   Definitions and structural lemmas for Imports Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/ImportsAlt.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.TopVec
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
def tv {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ) :
    PiLp 2 (fun _ : Wd.Ix (Fin w.length) × M.Ty P => PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) :=
  WithLp.toLp 2 fun x =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ) •
      B.hsVec ((p.TP.E x.2).comp (p.V (p.Θ.Θ w x.1 H) (TBB.bigPt P.r c)))
end
end GlobalTheory.TopVec


