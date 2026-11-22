-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:27.964317+00:00
-- url     : https://prove2.me/theorems/aa6bc76d-59c6-4b85-89c2-dd3f5219fec0
-- title:
--   Exists Has Leading Coeff Of Mem Span Below
-- statement:
--   Definitions and structural lemmas for Exists Has Leading Coeff Of Mem Span Below, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.P
section Base
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Base
section Base2
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Base2
section CaseA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}
end CaseA
section Gram
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Gram
section V0
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end V0
section Sig
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
end Sig
section Perp
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
def perpS (H : HermSpace K V) (S : Submodule K V) : Submodule K V where
  carrier := {v | ∀ s ∈ S, H.B s v = 0}
  add_mem' := by intro a b ha hb s hs; simp [ha s hs, hb s hs]
  zero_mem' := by intro s _; simp
  smul_mem' := by intro c a ha s hs; simp [ha s hs]
end Perp
section DetBlocks
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
def Esing (p : n) (s : R) : Matrix n n R := Matrix.of fun a b => if a = p ∧ b = p then s else 0
end DetBlocks
section Lift
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
def GoodMap (F F' : FlagD H r) (g : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (g x) (g y) = H.B x y) ∧ Function.Bijective g ∧ (∀ y ∈ V0 F F', g y = y) ∧
  (∀ y : V, (∀ u ∈ II F F', H.B u y = 0) → g y - y ∈ II F F')
end Lift
end Formalism.HermitianLatticeCounting.P


