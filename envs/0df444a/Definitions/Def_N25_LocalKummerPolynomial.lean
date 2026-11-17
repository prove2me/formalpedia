-- Prove2me | Definitions.Def_N25_LocalKummerPolynomial
-- name    : N25_LocalKummerPolynomial
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:41.336211+00:00
-- url     : https://prove2.me/theorems/c80cc23d-5aa7-4162-9531-e4bca4c76f8a
-- title:
--   The order-five endomorphism relation
-- statement:
--   Defines the explicit endomorphism $ρ=−28−26γ−16γ^2−37γ^3$ of $J$ and the proposition $(1+γ+γ^2+γ^3+γ^4)x=0$ for every $x∈J$. The relation is the polynomial input used to control the selected kernel and its $F_{71}$-module structure.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_LocalKummerKernel
noncomputable section
namespace N25
def rhoEnd : J →+ J :=
  (-28 : ℤ) • AddMonoidHom.id J +
    (-26 : ℤ) • gamma +
    (-16 : ℤ) • (gamma.comp gamma) +
    (-37 : ℤ) • (gamma.comp (gamma.comp gamma))

def PhiFiveZero : Prop :=
  ∀ x : J,
    x + gamma x + gamma (gamma x) +
      gamma (gamma (gamma x)) +
      gamma (gamma (gamma (gamma x))) = 0



end N25


