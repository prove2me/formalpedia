-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:26.102626+00:00
-- url     : https://prove2.me/theorems/df637f03-cd00-4fa7-b6d2-a51f52f7b7fb
-- title:
--   Standard Functors Finite Length
-- statement:
--   Definitions and structural lemmas for Standard Functors Finite Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/StandardFunctorsFiniteLength.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.Published
def StandardFunctorsFiniteLength : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) (d : Fin r → ℕ),
    (∀ a, 0 < d a) →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (∑ a, d a)) k) V),
      IsSmooth π → HasFiniteLength π → HasFiniteLength (jac (m := fun a => Fin (d a)) finSigmaFinEquiv π)) ∧
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W),
      IsSmooth ρ → HasFiniteLength ρ → HasFiniteLength (parInd (m := fun a => Fin (d a)) finSigmaFinEquiv ρ)
end GlobalTheory.Published
end


