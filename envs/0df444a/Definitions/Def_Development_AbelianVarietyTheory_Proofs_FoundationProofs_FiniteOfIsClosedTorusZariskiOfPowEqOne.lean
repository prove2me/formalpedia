-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:03.537688+00:00
-- url     : https://prove2.me/theorems/4c67c678-7eb6-4013-a9e4-fec3a2650bf5
-- title:
--   Finite Of Is Closed Torus Zariski Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for Finite Of Is Closed Torus Zariski Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
namespace GlobalTheory
section Constructible
variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [ContinuousInv G]
end Constructible
section Characters
variable {X H : Type*} [MulOneClass H]
end Characters
section Torus
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
noncomputable def torusEval (t : Multiplicative X →* Rˣ) : AddMonoidAlgebra R X →ₐ[R] R :=
  AddMonoidAlgebra.lift R R X ((Units.coeHom R).comp t)
@[simp] theorem torusEval_single (t : Multiplicative X →* Rˣ) (x : X) (a : R) :
    torusEval t (single x a) = a * t (Multiplicative.ofAdd x) := by
  simp [torusEval]
def torusChar (x : X) : (Multiplicative X →* Rˣ) →* R where
  toFun t := t (Multiplicative.ofAdd x)
  map_one' := by simp
  map_mul' s t := by simp
@[simp] theorem torusChar_apply (x : X) (t : Multiplicative X →* Rˣ) :
    torusChar x t = t (Multiplicative.ofAdd x) := rfl
noncomputable def torusTranslate (s : Multiplicative X →* Rˣ) :
    AddMonoidAlgebra R X →ₐ[R] AddMonoidAlgebra R X :=
  AddMonoidAlgebra.lift R _ X
    { toFun x := single x.toAdd (s x : R)
      map_one' := by simp [one_def]
      map_mul' x y := by simp [single_mul_single] }
noncomputable def torusInvert : AddMonoidAlgebra R X →ₐ[R] AddMonoidAlgebra R X :=
  AddMonoidAlgebra.lift R _ X
    { toFun x := single (-x.toAdd) (1 : R)
      map_one' := by simp [one_def]
      map_mul' x y := by simp [single_mul_single, add_comm] }
variable [IsDomain R]
noncomputable def torusPrime (t : Multiplicative X →* Rˣ) : PrimeSpectrum (AddMonoidAlgebra R X) :=
  PrimeSpectrum.comap (torusEval t).toRingHom ⟨⊥, Ideal.isPrime_bot⟩
@[simp] theorem mem_torusPrime (t : Multiplicative X →* Rˣ) (f : AddMonoidAlgebra R X) :
    f ∈ (torusPrime t).asIdeal ↔ torusEval t f = 0 := by
  simp [torusPrime]
variable (R X) in

@[reducible] noncomputable def torusZariski : TopologicalSpace (Multiplicative X →* Rˣ) :=
  TopologicalSpace.induced torusPrime inferInstance
variable (R X) in

def torusPowTorsion (n : ℕ) : Subgroup (Multiplicative X →* Rˣ) where
  carrier := {t | ∃ j, t ^ n ^ j = 1}
  one_mem' := ⟨0, one_pow _⟩
  mul_mem' := by
    rintro s t ⟨i, hi⟩ ⟨j, hj⟩
    refine ⟨i + j, ?_⟩
    rw [mul_pow, pow_add, pow_mul, hi, mul_comm (n ^ i), pow_mul, hj, one_pow, one_pow, one_mul]
  inv_mem' := by
    rintro s ⟨i, hi⟩
    exact ⟨i, by rw [inv_pow, hi, inv_one]⟩
end Torus
section Coordinates
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] {ι : Type*}
variable (R) in

noncomputable def torusCoord (b : Module.Basis ι ℤ X) : (Multiplicative X →* Rˣ) ≃* (ι → Rˣ) where
  toFun t i := t (Multiplicative.ofAdd (b i))
  invFun u := AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ fun i => Additive.ofMul (u i)).toAddMonoidHom
  left_inv t := by
    have : (b.constr ℤ fun i => Additive.ofMul (t (Multiplicative.ofAdd (b i)))) =
        (AddMonoidHom.toMultiplicativeLeft.symm t).toIntLinearMap := b.ext fun i => by simp
    beta_reduce
    rw [this]
    rfl
  right_inv u := by
    funext i
    simp
  map_mul' s t := rfl
noncomputable def laurentEval (u : ι → Rˣ) : AddMonoidAlgebra R (ι →₀ ℤ) →ₐ[R] R :=
  torusEval ((torusCoord R Finsupp.basisSingleOne).symm u)
end Coordinates
end GlobalTheory


