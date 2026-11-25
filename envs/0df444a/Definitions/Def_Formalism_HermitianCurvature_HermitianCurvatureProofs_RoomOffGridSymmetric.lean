-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:46.93054+00:00
-- url     : https://prove2.me/theorems/2354ae76-4ab2-466f-860b-2719ab3d1bb3
-- title:
--   Room Off Grid Symmetric
-- statement:
--   Definitions and structural lemmas for Room Off Grid Symmetric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField
def RoomOffGrid : Prop :=
  ∀ (P : M.Par) (l0 : ℕ) (lo hi : ℝ), (∀ Y, lo ≤ Y → Y ≤ hi → I.OnCut P.u P.u' l0 Y) →
    ∀ (w : List C.Letter) (m : ℕ) (B : Finset ℝ), KB.CutWord P l0 w →
      10 * ((w.length : ℝ) + m + B.card + 1) ≤ hi - lo →
      ∃ ys : List ℝ, ys.length = m ∧ (∀ y ∈ ys, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B) ∧
        ys.Pairwise (fun y y' => 4 < |y - y'|) ∧ KB.CutWord P l0 (KB.plusW ys w) ∧
        KB.CutWord P l0 (KB.minusW ys w)
def RoomOffGridS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → KB.CutInside S → ∀ (v : Fin S.f) (w : List C.Letter) (m : ℕ) (B : Finset ℝ),
      KB.CutWord (D.parOf S v) (S.l + 1) w → w.length + m + B.card ≤ 2 * S.Ntop →
      ∃ ys : List ℝ, ys.length = m ∧ (∀ y ∈ ys, S.cutLo v ≤ y ∧ y + 1 ≤ S.cutHi v ∧ y ∉ B ∧ y + 1 ∉ B) ∧
        ys.Pairwise (fun y y' => 4 < |y - y'|) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW ys w) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW ys w)
end Formalism.FourierDecayAlt.P.PBD


