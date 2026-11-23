-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM
-- name    : Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:01.432391+00:00
-- url     : https://prove2.me/theorems/4d1199b8-1eda-4835-9fff-893a4e2c32fd
-- title:
--   Id Trans SM
-- statement:
--   Definitions and structural lemmas for Id Trans SM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NumberFieldFamilies/IdTransSM.lean

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology
namespace Formalism.L2.Fam.IdTrans
section Top
variable {L : Type} [Field L] [NumberField L]
end Top
section UnitsTriv
variable {L : Type} [Field L] [NumberField L]
def compAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* (w.adicCompletion L)ˣ :=
  Units.map { toFun := fun a => a.2 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
variable (L) in

def UnitsTrivP : Prop :=
  ∀ (χ : Ideles L →* ℂˣ), Continuous χ → ∀ (T : Set (HeightOneSpectrum (𝓞 L))), T.Finite →
    (∀ v ∉ T, ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ (localIdele L v x) = 1) →
    ∀ u : Ideles L, (u : AdeleRing (𝓞 L) L).1 = 1 → (∀ v, IsUnitAt v (compAt v u)) → (∀ v ∈ T, compAt v u = 1) → χ u = 1
end UnitsTriv
section UnitsTrivPf
variable {L : Type} [Field L] [NumberField L]
def infU : Ideles L →* (InfiniteAdeleRing L)ˣ :=
  Units.map { toFun := fun a => a.1, map_one' := rfl, map_mul' := fun _ _ => rfl }
end UnitsTrivPf
end Formalism.L2.Fam.IdTrans


