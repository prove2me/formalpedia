-- Prove2me | Definitions.Def_MTT_Cohomology
-- name    : MTT_Cohomology
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-06T13:58:23.530643+00:00
-- url     : https://prove2.me/theorems/e1071a6e-f650-406b-94af-c5d9a4ff3e07
-- title:
--   Compactly supported group cohomology and integral modular-symbol evaluations
-- statement:
--   Define degree-one relative group cohomology as Gamma-equivariant additive divisor-pair functions with homogeneous binary polynomial values. This is Hom_Gamma(Div^0(P^1(Q)), Sym^n R^2), over an arbitrary commutative ring. Define the integral coefficient evaluations, coefficientwise extension and canonical tensor base change, the explicitly normalized prime-Hecke and reflection formulas, nebentype/sign eigenpackets, and analytic integration comparison predicates. No analytic or arithmetic theorem is assumed in this definition file. Integral group cohomology is distinguished from cohomology of the coarse quotient at elliptic stabilizers.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions, Definition 4.1 and Proposition 4.2, pp. 861–863; https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf. The degree-one relative group-cohomology model is used over Z.

import Definitions.Def_MTT_Arithmetic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.TensorProduct.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace MTT.Cohomology
abbrev Cusp := OnePoint ℚ
abbrev Binary (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R
/-- Homogeneous-polynomial model of Sym^n(R²). -/
abbrev Sym (R : Type*) [CommRing R] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R n
/-- Left coefficient action P(X,Y) ↦ P((X,Y)γ). -/
def act {R : Type*} [CommRing R] (γ : Matrix (Fin 2) (Fin 2) ℤ) :
    Binary R →ₗ[R] Binary R :=
  (MvPolynomial.aeval fun i : Fin 2 =>
    ∑ a : Fin 2, (γ a i : R) • MvPolynomial.X a).toLinearMap

def cuspAct (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : Cusp) : Cusp :=
  Matrix.SpecialLinearGroup.mapGL ℚ γ • x
/-- Relative group cohomology in the modular-symbol model
Hom_Γ(Div⁰(P¹(ℚ)), Sym^n(R²)). Pairs represent [x] − [y].
This is not coarse-quotient cohomology with integral coefficients. -/
def compactSupport (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (n : ℕ) (R : Type*) [CommRing R] :
    Submodule R ((Cusp × Cusp) → Binary R) where
  carrier := {φ | (∀ x y, φ (x,y) ∈ Sym R n) ∧
    (∀ x y z, φ (x,y) + φ (y,z) = φ (x,z)) ∧
    (∀ γ : Γ, ∀ x y, φ (cuspAct γ.val x, cuspAct γ.val y) = act γ.val.val (φ (x,y)))}
  zero_mem' := by simp [MvPolynomial.isHomogeneous_zero]
  add_mem' := by
    rintro φ ψ ⟨hφ, aφ, eφ⟩ ⟨hψ, aψ, eψ⟩
    refine ⟨fun x y => (Sym R n).add_mem (hφ x y) (hψ x y), ?_, ?_⟩
    · intro x y z
      change (φ (x,y) + ψ (x,y)) + (φ (y,z) + ψ (y,z)) = φ (x,z) + ψ (x,z)
      rw [add_add_add_comm, aφ, aψ]
    · intro γ x y
      change φ _ + ψ _ = act γ.val.val (φ _ + ψ _)
      rw [map_add, eφ, eψ]
  smul_mem' := by
    rintro a φ ⟨hφ, aφ, eφ⟩
    refine ⟨fun x y => (Sym R n).smul_mem a (hφ x y), ?_, ?_⟩
    · intro x y z
      change a • φ (x,y) + a • φ (y,z) = a • φ (x,z)
      rw [← smul_add, aφ]
    · intro γ x y
      change a • φ _ = act γ.val.val (a • φ _)
      rw [map_smul, eφ]
abbrev Hc (N n : ℕ) (R : Type*) [CommRing R] :=
  compactSupport (CongruenceSubgroup.Gamma1 N) n R
/-- Integral coefficient evaluation on [∞] − [r]. -/
def evaluation {N n : ℕ} {R : Type*} [CommRing R] (j : ℕ) (r : ℚ) :
    Hc N n R →ₗ[R] R where
  toFun φ := MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm
    (fun i : Fin 2 => if i = 0 then j else n-j)) (φ.val (OnePoint.infty, (r : Cusp)))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
/-- Coefficientwise extension, without presupposing base change. -/
def Extends {N n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ι : R →+* S) (φ : Hc N n R) (ψ : Hc N n S) : Prop :=
  ∀ x y, ψ.val (x,y) = MvPolynomial.map ι (φ.val (x,y))
/-- Canonical base-change isomorphism specified on pure tensors. -/
def BaseChange (N n : ℕ) (R : Type*) [CommRing R] : Prop :=
  ∃ e : (R ⊗[ℤ] Hc N n ℤ) ≃ₗ[R] Hc N n R,
    ∀ φ : Hc N n ℤ, Extends (Int.castRingHom R) φ (e (1 ⊗ₜ[ℤ] φ))

/-- Fractional-linear action, also used for positive-determinant Hecke matrices. -/
def fractional (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) : Cusp :=
  match x with
  | none => if g 1 0 = 0 then OnePoint.infty else ((g 0 0 : ℚ) / g 1 0 : ℚ)
  | some r => if (g 1 0 : ℚ)*r + g 1 1 = 0 then OnePoint.infty
      else (((g 0 0 : ℚ)*r + g 0 1) / ((g 1 0 : ℚ)*r + g 1 1) : ℚ)

/-- Integral adjugate normalization: det(g)^(k−1)(cz+d)^(-k)
on analytic forms of weight k. -/
def slash {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) ℤ)
    (φ : (Cusp × Cusp) → Binary R) : (Cusp × Cusp) → Binary R :=
  fun D => act (Matrix.adjugate g) (φ (fractional g D.1, fractional g D.2))

def primeHecke {R : Type*} [CommRing R] (e : R) (l : ℕ)
    (φ : (Cusp × Cusp) → Binary R) : (Cusp × Cusp) → Binary R :=
  (∑ b : Fin l, slash !![1, (b.val : ℤ); 0, (l : ℤ)] φ) +
    e • slash !![(l : ℤ), 0; 0, 1] φ

def reflection {R : Type*} [CommRing R]
    (φ : (Cusp × Cusp) → Binary R) : (Cusp × Cusp) → Binary R :=
  fun D => act !![-1, 0; 0, 1]
    (φ (fractional !![-1, 0; 0, 1] D.1, fractional !![-1, 0; 0, 1] D.2))

/-- Full prime-Hecke, nebentype and sign conditions; primes dividing N are included. -/
def Packet {N n : ℕ} {R : Type*} [CommRing R]
    (e : ZMod N → R) (a : ℕ → R) (s : Bool) (φ : Hc N n R) : Prop :=
  (∀ l : ℕ, l.Prime → primeHecke (e l) l φ.val = a l • φ.val) ∧
  (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
    φ.val (cuspAct γ.val x, cuspAct γ.val y) =
      e (γ.val 1 1 : ZMod N) • act γ.val.val (φ.val (x,y))) ∧
  reflection φ.val = (MTT.sign s : R) • φ.val

/-- Integration is normalized by −2πi; the coefficient functional has a binomial factor. -/
def IntegralClass {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (φ : Hc N (k-2) ℂ) : Prop :=
  ∀ j r, j ≤ k-2 → evaluation j r φ =
    ((k-2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r

/-- Both signs retain the half in the analytic normalization. -/
def SignedClass {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (s : Bool) (φ : Hc N (k-2) ℂ) : Prop :=
  ∀ j r, j ≤ k-2 → evaluation j r φ =
    ((k-2).choose j : ℂ) * MTT.signedIntegral f s j r

/-- Precise Hecke-equivariance, using the analytic normalization already in MTT. -/
def HeckeEquivariant {N k : ℕ}
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ) : Prop :=
  ∀ (e : DirichletCharacter ℂ N) (l : ℕ), l.Prime →
  ∀ f g : CuspForm (MTT.GammaOne N) (k : ℤ),
    (∀ z, g z = MTT.heckePrime k (e l) l f z) →
    (I g).val = primeHecke (e l) l (I f).val

end MTT.Cohomology


