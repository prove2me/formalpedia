-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:51.393723+00:00
-- url     : https://prove2.me/theorems/4848f9a0-14da-4547-94fc-22efb7f4beec
-- title:
--   Det Adm B
-- statement:
--   Definitions and structural lemmas for Det Adm B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DetAdmB.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
section Boxes
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
def boxS (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (ι → Af F) :=
  {y | ∀ c v, y c v ∈ D c v}
def IsBoxD (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Prop :=
  (∀ c v, IsClopen (D c v) ∧ IsCompact (D c v)) ∧
    ∀ᶠ v in cofinite, ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))
variable (F ι) in

def boxes : Set (Set (ι → Af F)) := {s | ∃ D, IsBoxD D ∧ s = boxS D}
open Classical in

def upd (D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (c : ι)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fv F v)) : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
  fun c' => if c' = c then Function.update (D c) v (D c v ∩ C) else D c'
end Boxes
end PI.VolStabW.DeterminantAdmissible


