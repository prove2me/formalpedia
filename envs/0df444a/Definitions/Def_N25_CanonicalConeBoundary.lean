-- Prove2me | Definitions.Def_N25_CanonicalConeBoundary
-- name    : N25_CanonicalConeBoundary
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:27.714675+00:00
-- url     : https://prove2.me/theorems/2a47303e-3a1e-48c1-ac7b-f20d2c80bbe3
-- title:
--   The boundary coefficient ring of the canonical cone
-- statement:
--   Defines the quotient of the cone’s coefficient ring by the normalizing form $A$, its quotient homomorphism, and its domain structure. This is a technical boundary carrier for analyzing the specialization $A=0$ in the monic tower presentation of the cone.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalConeTower
/-! The boundary base of the monic cone presentation: the coefficient ring modulo the normalizing form A, a domain. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

abbrev CanonicalConeBoundaryBase25 := CanonicalConeBase25 K ⧸
  Ideal.span ({canonicalConeBaseA25 K} : Set (CanonicalConeBase25 K))

@[reducible] instance canonicalConeBoundaryBaseSemiring25 : Semiring (CanonicalConeBoundaryBase25 K) :=
  (Ideal.Quotient.commRing _).toSemiring

def canonicalConeBoundaryMap25 : CanonicalConeBase25 K →+* CanonicalConeBoundaryBase25 K :=
  Ideal.Quotient.mk _

instance canonicalConeBoundaryBase25_isDomain : IsDomain (CanonicalConeBoundaryBase25 K) := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mpr
  exact (Ideal.span_singleton_prime (Polynomial.prime_X.ne_zero)).mpr Polynomial.prime_X

end N25


