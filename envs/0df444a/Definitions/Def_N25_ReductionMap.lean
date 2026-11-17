-- Prove2me | Definitions.Def_N25_ReductionMap
-- name    : N25_ReductionMap
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:57.018679+00:00
-- url     : https://prove2.me/theorems/f85c60ca-8a4d-4387-a87d-0b3ea64e0226
-- title:
--   Reduction from rational invariants to Frobenius invariants
-- statement:
--   Defines the reduction homomorphism from arithmetic Galois-fixed points of the geometric Jacobian to Frobenius-fixed points of its good reduction, with a definition independent of the theorem guaranteeing Frobenius invariance. It is the map used to compare rational torsion and divisor classes with finite-field Jacobians.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
set_option autoImplicit false
noncomputable section
namespace N25.Endgame

/-- Reduction restricted to arithmetic Galois invariants and Frobenius invariants.
The codomain restriction is taken when reduction of every rational point is Frobenius fixed, which always holds
(`red_mem_fixed25`); the zero map in the other case keeps this definition independent of that theorem.
Use `coe_redM25` to compute it. -/
noncomputable def redM25
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ25 : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) : ↥N25.M →+ ↥(RedFixed25 D) :=
  open Classical in
  if h : ∀ z : ↥N25.M, ((red25 D).comp N25.M.subtype) z ∈ RedFixed25 D then
    ((red25 D).comp N25.M.subtype).codRestrict _ h
  else 0

end N25.Endgame


