-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_FrameMinor
-- name    : Formalism_HermitianCurvature_FrameMinor
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:14:48.065137+00:00
-- url     : https://prove2.me/theorems/41479268-40a8-457d-963f-fec3e7a5c846
-- title:
--   Frame Minor
-- statement:
--   Definitions and structural lemmas for Frame Minor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/FrameMinor.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
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
namespace Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def RZLin : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)), IsOpen D →
    ∀ (c : Fin (mdim k r i) → Fin (mdim k r i) → ℂ) (F : Mx k r → E), SmoothLev k r i D F → ∀ g ∈ Glev k r i ∩ D,
      RZ (Hpk k r) (∑ a, ∑ b, c a b • Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) F g =
        ∑ a, ∑ b, c a b • EH k r (posL k r i a) (posL k r i b) F g
def FrameMinor : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (D : Set (Mx k r)), IsOpen D →
    ∀ (Bs : Fin m → Fin (2 * r + k + 1) → ℂ), (∀ a, inWb k r (Bs a)) →
    ∀ (P Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ)
      (ι : Fin m → Fin (mdim k r (Fin.last r))), Function.Injective ι →
    (∀ a c, P c (ι a) = Bs a (posL k r (Fin.last r) c)) →
    (∀ b d, Q (ι b) d = herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (Bs b)) →
    ∀ (w : ℂ) (φ : SV k r (Fin.last r) D E), ∀ g ∈ Glev k r (Fin.last r) ∩ D,
      (qminor (Econj (EV k r (Fin.last r) D E) P Q) ι ι w φ).1 g = capR k r Bs w φ.1 g
end Formalism.FourierDecayAlt.Qr


