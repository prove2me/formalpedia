-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:10.186798+00:00
-- url     : https://prove2.me/theorems/40623ed8-7172-4f87-bc53-8652cde4ef8a
-- title:
--   NDLoc B
-- statement:
--   Definitions and structural lemmas for NDLoc B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocB.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  (j : Ω →+* PadicAlgCl l)
def jE : E →+* PadicAlgCl l := j.comp (algebraMap E Ω)
def KwF : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => jE (E := E) j (Module.finBasis ℚ E i))
instance KwF_fin : FiniteDimensional ℚ_[l] (KwF (E := E) j) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
def clE : Subfield (PadicAlgCl l) := (jE (E := E) j).fieldRange.topologicalClosure
end Formalism.BasicNotions.Examples₂.LB


