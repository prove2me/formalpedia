-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:44:41.357946+00:00
-- url     : https://prove2.me/theorems/b3c50d98-ae4c-4657-9789-1b85bad77557
-- title:
--   Eff Cartier Iff Forall Cart At
-- statement:
--   Definitions and structural lemmas for Eff Cartier Iff Forall Cart At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/EffCartierIffForallCartAt.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.AnForm.R
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
def CartAt {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) : Prop :=
  ∃ (U : X.affineOpens) (f : Γ(X, U.1)), x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ J.ideal U = Ideal.span {f}
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver


