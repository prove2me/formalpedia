-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TypeBound
-- name    : Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TypeBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:45.084816+00:00
-- url     : https://prove2.me/theorems/d581b720-cc8e-49c9-a59d-46af23f86fca
-- title:
--   Type Bound
-- statement:
--   Definitions and structural lemmas for Type Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TwistedSubstitution/TypeBound.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
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
namespace Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G
def TypeBound : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (e : (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K)),
    (∀ mu, IsIsoProj (glOps K n LL S) mu (e mu)) →
    (∀ G : MvPolynomial (ι × Fin n) K, ∃ T : Finset (Fin n → ℤ),
      G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K n LL S) mu) →
    ∀ (G : MvPolynomial (ι × Fin n) K) (lam : Fin n → ℤ), e lam G ≠ 0 →
      (∀ M : ℤ, lam1S LL S G ≤ (M : WithBot ℤ) → lam 0 ≤ M) ∧
      (∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → th ≤ lam (lastIdx n))
end Formalism.MainNotions.TestSideWords


