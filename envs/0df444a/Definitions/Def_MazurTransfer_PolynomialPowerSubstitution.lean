-- Prove2me | Definitions.Def_MazurTransfer_PolynomialPowerSubstitution
-- name    : MazurTransfer_PolynomialPowerSubstitution
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-10T11:03:59.606976+00:00
-- url     : https://prove2.me/theorems/bd5408fe-c9cb-490f-a7b1-e17437476c75
-- title:
--   Polynomial parameter-power root presentation and basis constructor
-- statement:
--   Let $R$ be a commutative ring. A separate coefficient parameter acts on $R[X]$ by $T\mapsto X^n$. The literal monic root presentation $R[T][Y]/(Y^n-T)$ is identified with this polynomial algebra, with the coefficient map and the root image retained. For nontrivial $R$ and $n>0$, its monic power basis transports to a basis of $R[X]$ over the parameter algebra, indexed by $\mathrm{Fin}(n)$. The file contains the type, maps, inverse checks required by the constructor, and this constructor. The downstream theorem exposes the ordinary polynomial-ring interface, and the actual order-13 parameter powers use it to raise finite-map degrees.
-- source:
--   Owned constructor formalization in PolynomialPowerSubstitutionPresentation.lean and PolynomialPowerSubstitutionBasis.lean for the MazurTheorem campaign, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Uses Mathlib AdjoinRoot.lift, AdjoinRoot.powerBasis' and Module.Basis.map at exact revision 0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean . Apache-2.0 headers retained. No open statements and no original FLT source count increment.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: literal polynomial parameter-power root presentation and its finite basis constructor.
Named downstream consumer: the public power-substitution basis theorem and actual curve parameter powers. -/
import Mathlib

namespace PolynomialPowerSubstitutionLibrary

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the polynomial ring with coefficient parameter acting by
X^n is the literal monic root algebra of Y^n-T.
Named downstream consumer: the power-substitution finite free basis used to
raise the degree of actual order-13 FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.PolynomialPowerSubstitutionPresentation
open Polynomial
variable (R : Type u) [CommRing R] (n : ℕ)

def Source (_n : ℕ) : Type u := Polynomial R
instance sourceCommRing : CommRing (Source R n) := inferInstanceAs (CommRing (Polynomial R))
instance sourceBaseAlgebra : Algebra R (Source R n) := inferInstanceAs (Algebra R (Polynomial R))

def sourceX : Source R n := (X : Polynomial R)
def powerMap : Source R n →+* Polynomial R := (aeval ((X : Polynomial R)^n)).toRingHom
scoped instance powerAlgebra : Algebra (Source R n) (Polynomial R) := (powerMap R n).toAlgebra

def relation : Polynomial (Source R n) := X^n - C (sourceX R n)
abbrev RootRing := AdjoinRoot (relation R n)

theorem relation_eval : (relation R n).eval₂ (powerMap R n) (X : Polynomial R) = 0 := by
  rw [relation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change X^n - aeval ((X : Polynomial R)^n) X = 0
  rw [aeval_X, sub_self]

def forward : RootRing R n →+* Polynomial R :=
  AdjoinRoot.lift (powerMap R n) X (relation_eval R n)
def backward : Polynomial R →+* RootRing R n :=
  eval₂RingHom ((AdjoinRoot.of (relation R n)).comp (C : R →+* Source R n))
    (AdjoinRoot.root (relation R n))

theorem root_power : AdjoinRoot.root (relation R n)^n =
    AdjoinRoot.of (relation R n) (sourceX R n) := by
  have h := AdjoinRoot.eval₂_root (relation R n)
  change eval₂ (AdjoinRoot.of (relation R n)) (AdjoinRoot.root (relation R n))
    (X^n - C (sourceX R n)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem backward_powerMap : (backward R n).comp (powerMap R n) =
    AdjoinRoot.of (relation R n) := by
  apply Polynomial.ringHom_ext
  · intro r
    change backward R n (aeval ((X : Polynomial R)^n) (C r)) =
      AdjoinRoot.of (relation R n) (C r)
    rw [aeval_C]
    change eval₂ _ _ (C r) = _
    rw [eval₂_C]
    rfl
  · change backward R n (aeval ((X : Polynomial R)^n) X) = AdjoinRoot.of (relation R n) X
    rw [aeval_X, map_pow]
    simpa only [backward, coe_eval₂RingHom, eval₂_X, sourceX] using root_power R n

theorem forward_backward : (forward R n).comp (backward R n) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    change forward R n (backward R n (C r)) = C r
    rw [backward, coe_eval₂RingHom, eval₂_C]
    change forward R n (AdjoinRoot.of (relation R n) (C r)) = C r
    exact (AdjoinRoot.lift_of (relation_eval R n) (x := (C r : Source R n))).trans
      (aeval_C ((X : Polynomial R)^n) r)
  · simp [forward, backward]

theorem backward_forward : (backward R n).comp (forward R n) = RingHom.id _ := by
  have h : ((backward R n).comp (forward R n)).comp (AdjoinRoot.mk (relation R n)) =
      AdjoinRoot.mk (relation R n) := by
    apply Polynomial.ringHom_ext
    · intro p
      change backward R n (forward R n (AdjoinRoot.of (relation R n) p)) =
        AdjoinRoot.of (relation R n) p
      simpa only [forward, AdjoinRoot.lift_of, RingHom.comp_apply] using
        RingHom.congr_fun (backward_powerMap R n) p
    · simp [forward, backward, AdjoinRoot.mk_X]
  apply RingHom.ext
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih p => exact RingHom.congr_fun h p

def presentationEquiv : RootRing R n ≃ₐ[Source R n] Polynomial R where
  toFun := forward R n
  invFun := backward R n
  left_inv x := RingHom.congr_fun (backward_forward R n) x
  right_inv x := RingHom.congr_fun (forward_backward R n) x
  map_add' := (forward R n).map_add
  map_mul' := (forward R n).map_mul
  commutes' p := by
    change forward R n (AdjoinRoot.of (relation R n) p) = powerMap R n p
    simp [forward]

end MazurTransfer.PolynomialPowerSubstitutionPresentation

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a monic presentation gives the polynomial power-substitution
basis, and scalar towers raise any existing polynomial basis by a factor n.
Named downstream consumers: both actual order-13 parameter powers and their
level-set bases in arbitrarily large whole-curve FiniteMapData.
-/

noncomputable section
universe u v
namespace MazurTransfer.PolynomialPowerSubstitutionBasis
open Polynomial Module
open PolynomialPowerSubstitutionPresentation
variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

def powerBasis (hn : n ≠ 0) : Basis (Fin n) (Source R n) (Polynomial R) := by
  letI : Nontrivial (Source R n) := inferInstanceAs (Nontrivial (Polynomial R))
  have hd : (relation R n).natDegree = n := natDegree_X_pow_sub_C
  let b := (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (sourceX R n) hn)).basis
  exact (b.map (presentationEquiv R n).toLinearEquiv).reindex (finCongr hd)


end MazurTransfer.PolynomialPowerSubstitutionBasis

end
end

end PolynomialPowerSubstitutionLibrary
#print axioms PolynomialPowerSubstitutionLibrary.MazurTransfer.PolynomialPowerSubstitutionBasis.powerBasis


