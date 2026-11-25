-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:25:55.548081+00:00
-- url     : https://prove2.me/theorems/a96808c6-1f82-4fca-9991-3452ce7169a4
-- title:
--   Snapper Hyperplane St
-- statement:
--   Definitions and structural lemmas for Snapper Hyperplane St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/SnapperHyperplaneSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
def SnapperHyperplane.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp → ∀ a : ℤ,
    ∃ (r : ℕ) (qq : Fin r → Ideal (Poly k N)) (b : Fin r → ℤ),
      (∀ m, (qq m).IsPrime ∧ (∀ f ∈ qq m, ∀ d : ℕ, homogeneousComponent d f ∈ qq m) ∧ pp ≤ qq m ∧
        (X i : Poly k N) ∈ qq m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        pieceChar k pp a L n (c + 1) - pieceChar k pp a L n c = ∑ m, pieceChar k (qq m) (b m) L n c
end
end GroundTheory.Heights₂.Heights.Kleiman


