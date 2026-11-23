-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:58.984204+00:00
-- url     : https://prove2.me/theorems/5dbfd36a-6f69-42d0-ab52-7ec863ae1945
-- title:
--   NZType D
-- statement:
--   Definitions and structural lemmas for NZType D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeD.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
def tens (x : ∀ i, MonoidAlgebra k (G i)) : MonoidAlgebra k (∀ i, G i) :=
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g => ∏ i, (x i).coeff (g i)
variable {L : I → Type} [∀ i, Fintype (L i)] [DecidableEq I] (E : ∀ i, L i → MonoidAlgebra k (G i))
  (S : (∀ i, L i) → Prop)
open Classical in

def eSum : MonoidAlgebra k (∀ i, G i) := ∑ a : (∀ i, L i), if S a then tens (fun i => E i (a i)) else 0
variable (hidem : ∀ i l, E i l * E i l = E i l) (hcen : ∀ i l a, E i l * a = a * E i l)
  (horth : ∀ i l l', l ≠ l' → E i l * E i l' = 0)
end Formalism.BasicNotions.Examples₂.NZ


