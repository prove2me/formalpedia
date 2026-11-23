-- Prove2me | Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles
-- name    : Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:43.000561+00:00
-- url     : https://prove2.me/theorems/ac702f8e-5502-4a70-9e1b-7bf0bfd389bc
-- title:
--   Finite Cocycles Le Cocycles
-- statement:
--   Definitions and structural lemmas for Finite Cocycles Le Cocycles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/FrobeniusContractionProofs/FiniteCocyclesLeCocycles.lean

import Definitions.Def_Formalism_FrobeniusContraction_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WachCohomologyFacts.PCoh
open Formalism.WachCohomologyFacts
section One
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
  [IsScalarTower O AA V] (W : WachDatum E n V)
end One
section Two
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]
  {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)
end Two
end Formalism.WachCohomologyFacts.PCoh


