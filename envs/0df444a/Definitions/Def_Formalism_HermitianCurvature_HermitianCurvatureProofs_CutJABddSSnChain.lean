-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:04.734856+00:00
-- url     : https://prove2.me/theorems/2bec1d70-f496-4251-a358-79c69030ea92
-- title:
--   Cut JABdd SSn Chain
-- statement:
--   Definitions and structural lemmas for Cut JABdd SSn Chain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChain.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def ChainBd : Prop :=
  ∀ (k r : ℕ) (V E' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (Ψ : V → E'), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
    ∀ (F : Mat k r → V) (U K : Set (Mat k r)), IsOpen U → CkOn ⊤ (U ∩ GV k r) F → K ⊆ U → K ⊆ GV k r →
    ∀ Bg : ℝ, 0 ≤ Bg →
    (∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v F g‖ ≤ C * gN g ^ (Bg * m)) →
    ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ K, ‖dLR u v (fun g => Ψ (F g)) g‖ ≤ C * gN g ^ (Bg * m)
end
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn


