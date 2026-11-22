-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:17.20993+00:00
-- url     : https://prove2.me/theorems/bba71d9a-2da2-496b-9215-a319c74c2476
-- title:
--   Gram Product Identities
-- statement:
--   Definitions and structural lemmas for Gram Product Identities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramProductIdentities.lean

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
section Rep
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
theorem act_add (M : SlopeTestRemainingChoices S A) (X Y : Ix S → V) : act M (X + Y) = act M X + act M Y := by
  funext z; simp [act, smul_add, Finset.sum_add_distrib]
theorem act_smul (M : SlopeTestRemainingChoices S A) (c : ℂ) (X : Ix S → V) : act M (c • X) = c • act M X := by
  funext z
  simp only [act, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun z' _ => (smul_comm c (M z z') (X z')).symm
def frmS (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) : F7.Sesq (Ix S → V) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun X X' => frm ρ M X X')
    (fun X Y Z => by simp [frm, pair, act_add, map_add, Finset.sum_add_distrib])
    (fun c X Z => by simp [frm, pair, act_smul, Finset.mul_sum])
    (fun X Y Z => by simp [frm, pair, map_add, Finset.sum_add_distrib])
    (fun c X Z => by simp [frm, pair, Finset.mul_sum])
end Rep
section CS
variable {M : Type} [AddCommGroup M] [Module ℂ M]
end CS
end Formalism.FourierDecayAlt.P.GramProductIdentities


