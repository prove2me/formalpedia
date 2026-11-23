-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:56.901698+00:00
-- url     : https://prove2.me/theorems/5884bf3b-6534-486f-8e26-16d0b8a8915e
-- title:
--   Fin Red Statement
-- statement:
--   Definitions and structural lemmas for Fin Red Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/FinRedStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.LocalUnitReduction
def FinRedStatement : Prop :=
  ∀ (K' Fr : Type) [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
    (ι : Type) [Fintype ι] (R : ι → Type) [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
    (φ : ∀ c, Fr →ₐ[K'] R c),
    (∀ f : Fr, (∀ c, φ c f = 0) → f = 0) →
    (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q → RingHom.ker (φ c') ≤ Q → c = c') →
    (∀ c (r : R c), ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a) →
    (∀ c, FiniteDimensional K' (R c ⧸ Ideal.map (φ c) J) ∧ IsReduced (R c ⧸ Ideal.map (φ c) J)) →
    FiniteDimensional K' (Fr ⧸ J) ∧ IsReduced (Fr ⧸ J)
end Formalism.L2.Pj.LocalUnitReduction


