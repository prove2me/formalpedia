-- Prove2me | solution 1 for Algebra.levelSet_finite_free_finrank_of_flat_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9491ed0d-9b9d-5ffe-9d47-19eb5d66e636

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial

set_option autoImplicit false

universe u

open Polynomial
open scoped TensorProduct

namespace U4b

section Identification

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s)

abbrev lsIdeal : Ideal (S ⊗[R] A) := Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}

noncomputable def fwd : S ⊗[R] A →ₐ[S] S ⊗[R[X]] A :=
  AlgHom.liftEquiv R S A (S ⊗[R[X]] A)
    ((Algebra.TensorProduct.includeRight (R := R[X]) (A := S) (B := A)).restrictScalars R)

@[scoped simp] theorem fwd_tmul (x : S) (a : A) : fwd R A S (x ⊗ₜ[R] a) = x ⊗ₜ[R[X]] a := by
  rw [fwd, AlgHom.liftEquiv_tmul, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hf hs in
theorem fwd_rel : fwd R A S ((1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)) = 0 := by
  rw [map_sub, fwd_tmul, fwd_tmul, ← hf, ← hs, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, sub_self]

noncomputable def fwdQ : (S ⊗[R] A ⧸ lsIdeal R A S f s) →ₐ[S] S ⊗[R[X]] A :=
  Ideal.Quotient.liftₐ (lsIdeal R A S f s) (fwd R A S) (by
    intro a ha
    rw [← RingHom.mem_ker]
    refine (Ideal.span_le.mpr ?_) ha
    rintro _ rfl
    exact fwd_rel R A S f s hf hs)

@[scoped simp] theorem fwdQ_mk (t : S ⊗[R] A) :
    fwdQ R A S f s hf hs (Ideal.Quotient.mk _ t) = fwd R A S t := rfl

noncomputable def bwdA₀ : A →ₐ[R] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  (Ideal.Quotient.mkₐ R (lsIdeal R A S f s)).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A))

@[scoped simp] theorem bwdA₀_apply (a : A) :
    bwdA₀ R A S f s a = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] a) := rfl

include hf hs in

theorem bwdA₀_comp :
    (bwdA₀ R A S f s).comp (IsScalarTower.toAlgHom R R[X] A) =
      IsScalarTower.toAlgHom R R[X] (S ⊗[R] A ⧸ lsIdeal R A S f s) := by
  refine Polynomial.algHom_ext ?_
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', bwdA₀_apply, hf]
  rw [IsScalarTower.algebraMap_apply R[X] (S ⊗[R] A) (S ⊗[R] A ⧸ lsIdeal R A S f s),
    Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply, hs,
    Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

noncomputable def bwdA : A →ₐ[R[X]] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  { bwdA₀ R A S f s with
    commutes' := fun p => by
      have := congrArg (fun φ : R[X] →ₐ[R] _ => φ p) (bwdA₀_comp R A S f s hf hs)
      simpa using this }

@[scoped simp] theorem bwdA_apply (a : A) :
    bwdA R A S f s hf hs a = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] a) := rfl

noncomputable def bwd : S ⊗[R[X]] A →ₐ[S] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  AlgHom.liftEquiv R[X] S A _ (bwdA R A S f s hf hs)

@[scoped simp] theorem bwd_tmul (x : S) (a : A) :
    bwd R A S f s hf hs (x ⊗ₜ[R[X]] a) = Ideal.Quotient.mk _ (x ⊗ₜ[R] a) := by
  rw [bwd, AlgHom.liftEquiv_tmul, bwdA_apply]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply S (S ⊗[R] A) (S ⊗[R] A ⧸ lsIdeal R A S f s),
    Ideal.Quotient.algebraMap_eq, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

noncomputable def levelSetEquiv : (S ⊗[R] A ⧸ lsIdeal R A S f s) ≃ₐ[S] S ⊗[R[X]] A :=
  AlgEquiv.ofAlgHom (fwdQ R A S f s hf hs) (bwd R A S f s hf hs)
    (by
      refine Algebra.TensorProduct.ext' fun x a => ?_
      simp)
    (by
      refine Ideal.Quotient.algHom_ext _ (Algebra.TensorProduct.ext' fun x a => ?_)
      simp)

end Identification

end U4b
p2m_reactivate "P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b"

namespace U4b

theorem main
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (f : A) (d : ℕ)
    (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
    (hflat : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Flat)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
      Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : A)}) = d)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = d := by

  letI algA : Algebra R[X] A := (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] A := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R A r = (Polynomial.aeval f : R[X] →ₐ[R] A) (algebraMap R R[X] r)
    rw [AlgHom.commutes]
  haveI : Module.Finite R[X] A := hfin
  haveI : Module.Flat R[X] A := hflat
  have hf : algebraMap R[X] A X = f := by
    show (Polynomial.aeval f : R[X] →ₐ[R] A) X = f
    exact Polynomial.aeval_X f
  letI algS : Algebra R[X] S := (Polynomial.aeval s : R[X] →ₐ[R] S).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] S := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R S r = (Polynomial.aeval s : R[X] →ₐ[R] S) (algebraMap R R[X] r)
    rw [AlgHom.commutes]
  have hs : algebraMap R[X] S X = s := by
    show (Polynomial.aeval s : R[X] →ₐ[R] S) X = s
    exact Polynomial.aeval_X s

  let e : (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ≃ₗ[S] S ⊗[R[X]] A :=
    (levelSetEquiv R A S f s hf hs).toLinearEquiv
  haveI hfinS : Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) :=
    Module.Finite.equiv e.symm
  haveI hflatS : Module.Flat S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) :=
    Module.Flat.of_linearEquiv e
  haveI hfree : Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) :=
    Module.free_of_flat_of_isLocalRing
  refine ⟨hfinS, hfree, ?_⟩

  let κ := IsLocalRing.ResidueField S
  have hsκ : algebraMap R[X] κ X = IsLocalRing.residue S s := by
    rw [IsScalarTower.algebraMap_apply R[X] S κ, hs]; rfl
  have h1 : Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) =
      Module.finrank S (S ⊗[R[X]] A) := e.finrank_eq
  haveI : Module.Free S (S ⊗[R[X]] A) := Module.Free.of_equiv e
  have h2 : Module.finrank S (S ⊗[R[X]] A) = Module.finrank κ (κ ⊗[S] (S ⊗[R[X]] A)) :=
    (Module.finrank_baseChange (R := κ) (S := S) (M' := S ⊗[R[X]] A)).symm
  have h3 : Module.finrank κ (κ ⊗[S] (S ⊗[R[X]] A)) = Module.finrank κ (κ ⊗[R[X]] A) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R[X] S κ κ A).finrank_eq
  have h4 : Module.finrank κ (κ ⊗[R[X]] A) =
      Module.finrank κ (κ ⊗[R] A ⧸ Ideal.span {(1 : κ) ⊗ₜ[R] f - (IsLocalRing.residue S s) ⊗ₜ[R] (1 : A)}) :=
    (levelSetEquiv R A κ f (IsLocalRing.residue S s) hf hsκ).toLinearEquiv.finrank_eq.symm
  rw [h1, h2, h3, h4]
  exact hrank κ (IsLocalRing.residue S s)

end U4b
p2m_reactivate "P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b"

open Polynomial in
open scoped TensorProduct in
theorem solution
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (f : A) (d : ℕ)
    (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
    (hflat : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Flat)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
      Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : A)}) = d) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = d :=
  fun S _ _ _ s => U4b.main R A f d hfin hflat hrank S s

end S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial
end P2MW
export P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial (solution)
