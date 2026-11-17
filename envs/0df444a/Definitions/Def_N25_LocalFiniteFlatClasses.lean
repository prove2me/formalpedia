-- Prove2me | Definitions.Def_N25_LocalFiniteFlatClasses
-- name    : N25_LocalFiniteFlatClasses
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:55.899868+00:00
-- url     : https://prove2.me/theorems/eb92f19b-d2e3-4e92-afac-f94818aeebc0
-- title:
--   Finite-flat local cohomology at $71$
-- statement:
--   Restricts $V$, the order-five character line, and the cyclotomic quotient line to the local Galois group at $71$, and defines the subgroup of $H^1$ whose associated upper-triangular extension has a finite-flat model. It also pulls this condition back to continuous cohomology, providing the local condition at $71$ for the Selmer-style argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace N25.GlobalKummer
local instance instL_N25_LocalFiniteFlatClasses_23397f : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The literal selected kernel restricted to the local Galois group at 71. -/
abbrev localKernelRep (hPhi : PhiFiveZero) :
    Rep (ZMod 71) (PadicAlgCl 71 ≃ₐ[ℚ_[71]] PadicAlgCl 71) :=
  Rep.res (localGaloisToGlobal 71) (vRep hPhi)

/-- The character line restricted to the same local Galois group. -/
abbrev localPsiRep : Rep (ZMod 71) (PadicAlgCl 71 ≃ₐ[ℚ_[71]] PadicAlgCl 71) :=
  Rep.res (localGaloisToGlobal 71) psiRep

/-- The multiplicative quotient line restricted to the same local Galois group. -/
abbrev localCyclotomicRep : Rep (ZMod 71) (PadicAlgCl 71 ≃ₐ[ℚ_[71]] PadicAlgCl 71) :=
  Rep.res (localGaloisToGlobal 71) cyclotomicRep

/-- The finite-flat condition on the literal local kernel in ordinary H1. -/
def localFiniteFlatClasses (hPhi : PhiFiveZero) :
    Submodule (ZMod 71) (groupCohomology.H1 (localKernelRep hPhi)) :=
  groupCohomology.finiteFlatClasses 71 (localKernelRep hPhi).ρ

/-- The continuous finite-flat local condition, obtained by restricting the ordinary
H1 condition along the actual continuous-cohomology inclusion. -/
def continuousLocalFiniteFlatClasses (hPhi : PhiFiveZero) :
    Submodule (ZMod 71)
      (groupCohomology.continuousH1 (localGaloisToGlobal 71) (localKernelRep hPhi)) :=
  (localFiniteFlatClasses hPhi).comap
    (groupCohomology.continuousH1 (localGaloisToGlobal 71) (localKernelRep hPhi)).subtype

end N25.GlobalKummer


