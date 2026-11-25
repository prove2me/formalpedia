-- Prove2me | Definitions.Def_JacPoisson_Defs
-- name    : JacPoisson_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:31:43.786669+00:00
-- url     : https://prove2.me/theorems/daf98447-7c06-5b34-a662-8bd739000cfc
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Zayn Blore (zblore/fc-jacobian-poisson; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned The Jacobian conjecture in dimension 2n implies the Poisson conjecture in dimension n development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Defs.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace MvPolynomial
variable {k : Type*} [CommRing k]
variable {σ τ ι : Type*}
variable (k σ τ) in
/-- The type of regular functions from $k^σ$ to $k^τ$. -/
abbrev RegularFunction := τ → MvPolynomial σ k
namespace RegularFunction
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix σ τ (MvPolynomial σ k) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (F j)
noncomputable def comp
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι) :
    RegularFunction k σ ι :=
  fun (i : ι) ↦ MvPolynomial.bind₁ F (G i)
variable (k σ) in
noncomputable def id : RegularFunction k σ σ := MvPolynomial.X
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)
end RegularFunction
end MvPolynomial
namespace MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]
noncomputable def poissonBracket (f g : MvPolynomial (σ ⊕ σ) R) : MvPolynomial (σ ⊕ σ) R :=
  ∑ i : σ, (pderiv (Sum.inl i) f * pderiv (Sum.inr i) g -
    pderiv (Sum.inr i) f * pderiv (Sum.inl i) g)
end MvPolynomial
namespace JacobianConjecture
open MvPolynomial RegularFunction
def JacobianConjectureProp (k σ : Type*) [CommRing k] [Fintype σ] [DecidableEq σ] : Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ
end JacobianConjecture
namespace Arxiv.«math.0608009»
open MvPolynomial JacobianConjecture
variable {K : Type*} [Field K] [CharZero K]
def IsPoissonEndomorphism {n : ℕ}
    (φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K) : Prop :=
  ∀ v w, poissonBracket (φ (X v)) (φ (X w)) = poissonBracket (X v) (X w)
variable (K) in
/-- The Poisson Conjecture in dimension `n` ($PC_n$ in the notation of [AvdE07]): every
endomorphism of the `n`-th canonical Poisson algebra over `K` is an automorphism.
An endomorphism is an automorphism iff it is bijective, since the inverse of a bijective
algebra endomorphism preserving the Poisson bracket is again such. -/
def PoissonConjectureFor (n : ℕ) : Prop :=
  ∀ φ : MvPolynomial (Fin n ⊕ Fin n) K →ₐ[K] MvPolynomial (Fin n ⊕ Fin n) K,
    IsPoissonEndomorphism φ → Function.Bijective φ
end Arxiv.«math.0608009»


