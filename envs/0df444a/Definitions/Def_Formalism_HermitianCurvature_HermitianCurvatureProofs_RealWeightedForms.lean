-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:00.67879+00:00
-- url     : https://prove2.me/theorems/f54f36b9-200a-4033-833b-87d14b90126a
-- title:
--   Real Weighted Forms
-- statement:
--   Definitions and structural lemmas for Real Weighted Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
section admitted
variable {S : Type}
def Cnd (l l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |l.pt.re - l'.pt.re| ∧ 2 < |l.pt.re - l'.pt.re + 1| ∧ 2 < |l.pt.re - l'.pt.re - 1|
  else
    2 < |l'.pt.re - l.pt.re| ∧ 2 < |l'.pt.re - l.pt.re - 1| ∧ 2 < |l'.pt.re - l.pt.re - 2|
def CndY (Y : ℝ) (l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |Y - l'.pt.re| ∧ 2 < |Y - l'.pt.re + 1| ∧ 2 < |Y - l'.pt.re - 1|
  else
    2 < |l'.pt.re - Y| ∧ 2 < |l'.pt.re - Y - 1| ∧ 2 < |l'.pt.re - Y - 2|
end admitted
section Rep
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
end Rep
end Formalism.FourierDecayAlt.P.RealWeightedForms


