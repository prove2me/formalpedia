-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelC
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:27.688303+00:00
-- url     : https://prove2.me/theorems/48b5818e-ff8d-4557-8aee-bce7fa4a598e
-- title:
--   Model C
-- statement:
--   Definitions and structural lemmas for Model C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelC.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
attribute [local instance] locRel
example (ι : Ω →+* PadicAlgCl p) : algebraMap 𝒪[Kloc F ι] (AlgebraicClosure (Kloc F ι)) =
    (algebraMap (Kloc F ι) (AlgebraicClosure (Kloc F ι))).comp (algebraMap 𝒪[Kloc F ι] (Kloc F ι)) := rfl
end ReciprocityTheory.Neutral.Cmp


