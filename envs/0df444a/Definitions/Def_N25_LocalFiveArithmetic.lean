-- Prove2me | Definitions.Def_N25_LocalFiveArithmetic
-- name    : N25_LocalFiveArithmetic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:13.859377+00:00
-- url     : https://prove2.me/theorems/13922122-98e3-423c-8a90-f620b2e6f15b
-- title:
--   Finite quotients with divisible kernel
-- statement:
--   Introduces the $5$-adic integer ring and its residue field, and defines the condition that an abelian group $G$ contain a subgroup $U$ of finite index for which multiplication by $n$ is surjective on $U$. This technical arithmetic carrier isolates the finite-quotient criterion used for local $71$-divisibility at $5$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
noncomputable section

local instance instL_N25_LocalFiveArithmetic_bfd51b : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

abbrev R5 : Type := ℤ_[5]
abbrev k5 : Type := IsLocalRing.ResidueField R5

/-- A finite quotient whose kernel admits division by the given scalar. -/
def FiniteQuotientSurj (G : Type*) [AddCommGroup G]
    (n : ℕ) : Prop :=
  ∃ U : AddSubgroup G,
    Finite (G ⧸ U) ∧ Function.Surjective (fun u : U => n • u)

end N25.LocalFive


