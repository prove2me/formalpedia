-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:31:36.724615+00:00
-- url     : https://prove2.me/theorems/1b8c89f9-2305-567f-a446-b5d30ac5b2ae
-- title:
--   Val Units D
-- statement:
--   Definitions and structural lemmas for Val Units D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/ValUnitsD.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
def OK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))
theorem mem_OK_iff (x : K) : x ∈ OK p K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := mem_Obar_iff
theorem norm_algebraMap_padicInt (x : ℤ_[p]) : ‖((algebraMap ℤ_[p] K x : K) : PadicAlgCl p)‖ ≤ 1 := by
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) (x : ℚ_[p])‖ ≤ 1
  exact (PadicAlgCl.norm_extends p (x : ℚ_[p])).le.trans x.2
def zpToOK : ℤ_[p] →+* OK p K :=
  (algebraMap ℤ_[p] K).codRestrict _ fun x => (mem_OK_iff p K _).2 (norm_algebraMap_padicInt p K x)
@[instance_reducible]
def zpAlgOK : Algebra ℤ_[p] (OK p K) := (zpToOK p K).toAlgebra
attribute [local instance] zpAlgOK
def toObar : OK p K →+* Obar p :=
  ((algebraMap K (PadicAlgCl p)).comp (OK p K).subtype).codRestrict (Obar p) fun x => x.2
def resMap : OK p K →+* kbar p := (IsLocalRing.residue (Obar p)).comp (toObar p K)
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


