-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:28.498527+00:00
-- url     : https://prove2.me/theorems/577a7a29-c4f3-474d-b5ed-42fe0fbffb73
-- title:
--   Coeff Ev WMem
-- statement:
--   Definitions and structural lemmas for Coeff Ev WMem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section
variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}
noncomputable def evW (w : Fin (N + 1) → B) :
    MvPolynomial (UXVar D N) R →ₐ[R] MvPolynomial (Fin (D + 2) × Fin (N + 1)) B :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (w j))
def CoeffIn (W : Submodule R B) (m : ℕ) (p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) : Prop :=
  ∀ β, coeff β p ∈ W ^ m
variable (W : Submodule R B)
end
end ReciprocityTheory.ChartRestriction.G.T0


