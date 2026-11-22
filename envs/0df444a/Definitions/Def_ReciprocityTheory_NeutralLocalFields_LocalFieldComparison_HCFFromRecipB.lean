-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:43.661104+00:00
-- url     : https://prove2.me/theorems/65fedf1f-13b8-48da-a683-b4ec09d2252a
-- title:
--   HCFFrom Recip B
-- statement:
--   Definitions and structural lemmas for HCFFrom Recip B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
namespace ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
open Classical in

def infIdele (w : InfinitePlace K) : (w.Completion)ˣ →* Ideles K :=
  Units.map
    { toFun := fun x => ((Pi.mulSingle w x : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K))
      map_one' := Prod.ext (Pi.mulSingle_one w) rfl
      map_mul' := fun x y => Prod.ext (Pi.mulSingle_mul w x y) (mul_one 1).symm }
def infPart : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K where
  toFun x := (x.1, 1)
  map_one' := rfl
  map_mul' x y := Prod.ext rfl (mul_one 1).symm
def finPart : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K where
  toFun x := (1, x.2)
  map_one' := rfl
  map_mul' x y := Prod.ext (mul_one 1).symm rfl
def fstU : Ideles K →* InfiniteAdeleRing K :=
  (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (Units.coeHom (AdeleRing (𝓞 K) K))
def sndU : Ideles K →* FiniteAdeleRing (𝓞 K) K :=
  (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (Units.coeHom (AdeleRing (𝓞 K) K))
end ReciprocityTheory.Neutral.Bridge.HCFR


