-- Prove2me | Definitions.Def_MazurTransfer_OfficialFLTPolynomialLevelSetEquiv
-- name    : MazurTransfer_OfficialFLTPolynomialLevelSetEquiv
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:03:06.102664+00:00
-- url     : https://prove2.me/theorems/babd8b90-a383-4a1d-8c72-d5dc4dc8839b
-- title:
--   Official FLT polynomial level-set tensor equivalence
-- statement:
--   Let $R$ be a commutative ring, let $A$ and $S$ be compatible $R[T]$-algebras, and let the images of $T$ be $f$ and $s$. The literal evaluated tensor quotient $Q=(S\otimes_R A)/(1\otimes f-s\otimes1)$ has the specified $S$-algebra isomorphism $Q\cong S\otimes_{R[T]}A$. These are the original forward and backward maps and their structural identities from the official Anthropic FLT formalization.
-- source:
--   Complete Identification section from the official Anthropic FLT polynomial level-set source at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. All fourteen declarations and every retained constructor and embedded proof body are unchanged, with original attribution retained. The twelve kernel-boundary definitions plus two reflexive structural identities form this data interface; the separate substantial finite-flat rank theorem is excluded. All fourteen original closed types and seven constructor values are compared in the kernel; native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: both actual order-thirteen finite-chart level-set bases.

/- Complete official Anthropic FLT mathematical source, Apache-2.0, pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Every original declaration and hypothesis retained. Design boundary: actual zero schemes of module sections and finite free level sets of finite flat polynomial maps. Named downstream consumer: finite-map data on the actual order-13 curve and genuine Picard representability. -/
import Mathlib
namespace P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial


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
end P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial

#print axioms P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv


