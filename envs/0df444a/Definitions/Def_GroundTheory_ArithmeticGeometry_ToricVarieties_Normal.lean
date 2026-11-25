-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
-- name    : GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:26:56.281823+00:00
-- url     : https://prove2.me/theorems/c9b7788a-bb01-4a77-8eab-21ab0d08b054
-- title:
--   Normal
-- statement:
--   Definitions and structural lemmas for Normal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Normal.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial
section HalfSpace
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)
def LowerBound (f : AddMonoidAlgebra k G) (a : ℤ) : Prop :=
  ∀ m ∈ f.coeff.support, a ≤ φ m
noncomputable def degPart (f : AddMonoidAlgebra k G) (a : ℤ) : AddMonoidAlgebra k G :=
  ofCoeff (f.coeff.filter fun m => φ m = a)
variable {φ}
theorem LowerBound.add {f g : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g a) : LowerBound φ (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (Finsupp.support_add (by simpa using hm)) with h | h
  · exact hf m h
  · exact hg m h
end HalfSpace
section GroupAlgebra
variable (k : Type*) [CommRing k] [IsDomain k] [IsIntegrallyClosed k]
variable {k} {G : Type*} [AddCommGroup G] {ι : Type*} (b : Basis ι ℤ G)
noncomputable def natCombination : (ι →₀ ℕ) →+ G where
  toFun c := Finsupp.linearCombination ℤ b (c.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero)
  map_zero' := by simp
  map_add' c d := by
    rw [← map_add]
    congr 1
    exact Finsupp.mapRange_add (fun _ _ => Nat.cast_add _ _) c d
theorem repr_natCombination (c : ι →₀ ℕ) :
    b.repr (natCombination b c) = c.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero :=
  b.repr_linearCombination _
theorem natCombination_injective : Function.Injective (natCombination b) := by
  intro c d h
  have := congrArg b.repr h
  rw [repr_natCombination, repr_natCombination] at this
  ext i
  have := congrArg (fun f => f i) this
  simpa using this
variable (k) in

noncomputable def mvPolynomialEquiv :
    MvPolynomial ι k ≃ₐ[k] semigroupAlgebra k (AddMonoidHom.mrange (natCombination b)) :=
  (AlgEquiv.ofInjective (AddMonoidAlgebra.mapDomainAlgHom k k (natCombination b))
      (mapDomain_injective (natCombination_injective b))).trans
    (Subalgebra.equivOfEq _ _ (by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        induction f using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
        | single c a =>
          have e : mapDomainAlgHom k k (natCombination b) (single c a) =
              single (natCombination b c) a := by simp
          change mapDomainAlgHom k k (natCombination b) (single c a) ∈ _
          rw [e]
          exact single_mem_semigroupAlgebra (AddMonoidHom.mem_mrange.2 ⟨c, rfl⟩) a
      · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
        rintro _ ⟨s, ⟨c, rfl⟩, rfl⟩
        exact ⟨single c 1, by simp⟩))
end GroupAlgebra
section Normal
variable {k : Type*} [CommRing k] [IsDomain k] [IsIntegrallyClosed k]
variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
end Normal
end GroundTheory.Arith.Toric


