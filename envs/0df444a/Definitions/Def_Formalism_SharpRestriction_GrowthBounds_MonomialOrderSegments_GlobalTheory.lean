-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:36.61667+00:00
-- url     : https://prove2.me/theorems/1a78b36d-eab6-49f0-b316-cab88530ea85
-- title:
--   Global Theory
-- statement:
--   Definitions and structural lemmas for Global Theory, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K)
def outB : D.ML → Bool :=
  Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (Sum.elim (fun _ => false) (fun _ => true)))
abbrev outP (i : D.ML) : Prop := D.outB i = true
def SameBlockAlt (ζ ζ' : D.EM) : Prop :=
  (∀ i, ldeg ζ' i = ldeg ζ i) ∧ (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧
    (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))
def dUp : D.ML → ℕ :=
  Sum.elim D.dB (Sum.elim (fun _ => 0) (Sum.elim D.dT (fun _ => 0)))
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
def kapC (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K) (ζ : D.EM) : K :=
  (∏ t, cst t (D.labF ζ t) (ldeg ζ (D.mw t))) /
    ((∏ t : D.Tau, ∏ a, (ζ (D.mlab t, a)).factorial : ℕ) : K)
end TwistData
end Formalism.MainNotions.PlaneGram


