-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:00.825056+00:00
-- url     : https://prove2.me/theorems/b7f6835a-4c93-4e19-a269-e57b334009a9
-- title:
--   Conj OMem Conj Ideal
-- statement:
--   Definitions and structural lemmas for Conj OMem Conj Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
structure IsStep (P : Ideal (𝓞 K)) (A B : Submodule (𝓞 K) V) (y : V) : Prop where
  le : A ≤ B
  mem : y ∈ B
  notMem : y ∉ A
  smul : ∀ π ∈ P, π • y ∈ A
  gen : ∀ x ∈ B, ∃ c : 𝓞 K, x - c • y ∈ A
def col (I : Ideal (𝓞 K)) (z : 𝓞 K) : Ideal (𝓞 K) where
  carrier := {c | c * z ∈ I}
  add_mem' := fun {a c} ha hc => by
    change (a + c) * z ∈ I
    rw [add_mul]; exact I.add_mem ha hc
  zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
  smul_mem' := fun c a ha => by
    change (c • a) * z ∈ I
    rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha
namespace IsStep
variable {P : Ideal (𝓞 K)} {A B : Submodule (𝓞 K) V} {y : V}
end IsStep
end Formalism.HermitianLattices.Ext.L3.BallB


