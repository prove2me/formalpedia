-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_CharRealisedOverRootsOfUnity
-- name    : Formalism_UnipotentAdelicQuotients_CharRealisedOverRootsOfUnity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:36.196+00:00
-- url     : https://prove2.me/theorems/318a400b-f59f-42d7-bdbf-5ffc76c2437d
-- title:
--   Char Realised Over Roots Of Unity
-- statement:
--   Definitions and structural lemmas for Char Realised Over Roots Of Unity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/CharRealisedOverRootsOfUnity.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.D.Classical
def CharRealisedOverRootsOfUnity : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] [CharZero K] (z : K), IsPrimitiveRoot z (Nat.card Γ) →
    ∀ χ : Γ → K,
      (∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) Γ (Fin n → AlgebraicClosure K)),
        ρ.IsIrreducible ∧ ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t)) →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K)),
        (Nontrivial (Fin m → K) ∧ Function.Surjective τ.asAlgebraHom) ∧
          ∀ g, LinearMap.trace K (Fin m → K) (τ g) = χ g
end Formalism.D.Classical


