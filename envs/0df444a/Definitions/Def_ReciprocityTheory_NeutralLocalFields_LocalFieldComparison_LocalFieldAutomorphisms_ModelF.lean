-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:26:08.483534+00:00
-- url     : https://prove2.me/theorems/faff68a2-e315-5898-874a-80de77dc1dba
-- title:
--   Model F
-- statement:
--   Definitions and structural lemmas for Model F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/LocalFieldAutomorphisms/ModelF.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_mem_integer_Kloc

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
theorem norm_algebraMap_padicInt_Kloc (ι : Ω →+* PadicAlgCl p) (x : ℤ_[p]) :
    ‖((algebraMap ℤ_[p] (Kloc F ι) x : Kloc F ι) : PadicAlgCl p)‖ ≤ 1 := by
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1
  exact (PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2
def zpToInteger (ι : Ω →+* PadicAlgCl p) : ℤ_[p] →+* 𝒪[Kloc F ι] :=
  (algebraMap ℤ_[p] (Kloc F ι)).codRestrict _
    fun x => (mem_integer_Kloc ι _).2 (norm_algebraMap_padicInt_Kloc ι x)
@[instance_reducible]
def zpAlgInteger (ι : Ω →+* PadicAlgCl p) : Algebra ℤ_[p] 𝒪[Kloc F ι] := (zpToInteger (F := F) ι).toAlgebra
attribute [local instance] zpAlgInteger
end ReciprocityTheory.Neutral.Cmp


