-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:21:09.516421+00:00
-- url     : https://prove2.me/theorems/392edac5-8155-540e-b77f-263efa4febb6
-- title:
--   Capelli Two By Two
-- statement:
--   Definitions and structural lemmas for Capelli Two By Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliTwoByTwo.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CapelliTwoByTwo
section Eval
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Eval
section Zero
end Zero
section Frame
variable {k r : ℕ}
def gd (k r : ℕ) (y x : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  herm (Hpk k r) y y * herm (Hpk k r) x x - herm (Hpk k r) x y * herm (Hpk k r) y x
theorem idx {j : Fin (mdim k r (Fin.last r))} (h0 : ¬ j.val = 0) (h1 : ¬ j.val = 1) : j.val - 2 < k - 1 := by
  have hj := j.isLt
  simp only [mdim, Fin.val_last, Nat.sub_self, mul_zero, zero_add] at hj
  omega
def bc (k r : ℕ) (y x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) : Fin (2 * r + k + 1) → ℂ :=
  if h0 : j.val = 0 then y else if h1 : j.val = 1 then x else Bs ⟨j.val - 2, idx h0 h1⟩
def qrow (k r : ℕ) (y x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) (v : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  if h0 : j.val = 0 then
    (herm (Hpk k r) x x * herm (Hpk k r) v y - herm (Hpk k r) x y * herm (Hpk k r) v x) / gd k r y x
  else if h1 : j.val = 1 then
    (herm (Hpk k r) y y * herm (Hpk k r) v x - herm (Hpk k r) y x * herm (Hpk k r) v y) / gd k r y x
  else herm (Hpk k r) v (Bs ⟨j.val - 2, idx h0 h1⟩)
end Frame
end CapelliTwoByTwo
end Formalism.FourierDecayAlt.P


