-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EdgeExponent
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EdgeExponent
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:16.727865+00:00
-- url     : https://prove2.me/theorems/3622d58d-1d7a-43d0-a4d7-891a24c36640
-- title:
--   Edge Exponent
-- statement:
--   Definitions and structural lemmas for Edge Exponent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/EdgeExponent.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
def EdgeExponent : Prop :=
  ∀ (ι : Type) (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (wj X : ι → ℤ) (i : ℕ),
    NprimeZ Ev Od lam wj i + ∑ s ∈ Ev, ((i : ℤ) * wj s - X s) + ∑ s ∈ Od, (X s - (i : ℤ) * wj s) =
      ∑ s ∈ Od, X s + ∑ s ∈ Ev, (∑ a ∈ Icc 1 i, (lam s a + wj s) - X s)
def EdgeNonneg : Prop :=
  ∀ (μ : YoungDiagram) (B : Type) [DecidableEq B] (I : ℕ → Finset B) (J : Finset B),
    (∀ c, (I c).card = μ.colLen c) →
    ∑ c ∈ range (μ.rowLen 0), (I c ∩ J).card ≤ ∑ a ∈ range J.card, μ.rowLen a
end Formalism.InvariantFactorPaths.G7


