-- Prove2me | Definitions.Def_JacPoisson_FormalTarget
-- name    : JacPoisson_FormalTarget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:35:51.364463+00:00
-- url     : https://prove2.me/theorems/dde7c601-5bd1-455a-8579-7979fce4b51e
-- title:
--   Formal Target
-- statement:
--   Definitions and structural lemmas for Formal Target, from Zayn Blore (zblore/fc-jacobian-poisson; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned The Jacobian conjecture in dimension 2n implies the Poisson conjecture in dimension n development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/FormalTarget.lean

module
public import Definitions.Def_JacPoisson_Main
public import Theorems.Thm_JacPoisson_jacobian_implication

set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Arxiv.«math.0608009»
open MvPolynomial JacobianConjecture
variable {K : Type*} [Field K] [CharZero K]
theorem poisson_conjecture.variants.jacobian_implication (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n :=
  JacPoisson.jacobian_implication n h
end Arxiv.«math.0608009»
namespace PoissonConjecture
open MvPolynomial JacobianConjecture Arxiv.«math.0608009»
variable {K : Type*} [Field K] [CharZero K]
theorem poisson_conjecture.variants.jacobian_implication (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n :=
  Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication n h
end PoissonConjecture
section
universe w
example : type_of% @Arxiv.«math.0608009».poisson_conjecture.variants.jacobian_implication.{w} =
    type_of% @PoissonConjecture.poisson_conjecture.variants.jacobian_implication.{w} :=
  rfl
end


