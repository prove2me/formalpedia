-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
-- name    : GroundTheory_AutomorphicForms_StableConjCyclic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:21.834043+00:00
-- url     : https://prove2.me/theorems/0186b0a0-29e0-47ae-8922-6c4275775f9b
-- title:
--   Stable Conj Cyclic
-- statement:
--   Definitions and structural lemmas for Stable Conj Cyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjCyclic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Polynomial Module Matrix
section AlgClosed
variable {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]
end AlgClosed
section Krylov
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
def krylov (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i k => (M ^ (k : ℕ) *ᵥ v) i
variable {E : Type*} [Field E]
variable [Infinite E]
end Krylov
section Cyclic
variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
end Cyclic
section Consequences
variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
def IsCyclicVector (f : Module.End E V) (v : V) : Prop :=
  LinearIndependent E (fun k : Fin (finrank E V) => (f ^ (k : ℕ)) v)
variable {f : Module.End E V} {v : V}
noncomputable def cyclicBasis (hv : IsCyclicVector f v) : Basis (Fin (finrank E V)) E V :=
  basisOfLinearIndependentOfCardEqFinrank' _ hv (Fintype.card_fin _)
end Consequences
end GroundTheory.Automorphic


