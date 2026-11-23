-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_FinOrdValGen
-- name    : Formalism_UnipotentAdelicQuotients_FinOrdValGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:30.303927+00:00
-- url     : https://prove2.me/theorems/757b32ad-9c42-4f88-a513-f1a80c2ed6ee
-- title:
--   Fin Ord Val Gen
-- statement:
--   Definitions and structural lemmas for Fin Ord Val Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/FinOrdValGen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace HeckeValGen
variable (L : Type) [Field L] [NumberField L]
abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ
def diagUnits : Lˣ →* Ideles L :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom
open Classical in

def finiteSingle (v : HeightOneSpectrum (𝓞 L)) :
    v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v x
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y
def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing L), finiteSingle L v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle L v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle L v) x y) }
def FinOrdValGen : Prop :=
  ∀ χ : Ideles L →* ℂˣ, Continuous χ → (∀ k : Lˣ, χ (diagUnits L k) = 1) → (∃ n : ℕ, 0 < n ∧ χ ^ n = 1) →
    ∀ ϖ : (v : HeightOneSpectrum (𝓞 L)) → (v.adicCompletion L)ˣ,
      (∀ v, Valued.v ((ϖ v : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ)) →
    ∀ S : Set (HeightOneSpectrum (𝓞 L)), S.Finite →
    ∀ (P : HeightOneSpectrum (𝓞 L)) (x : (P.adicCompletion L)ˣ),
      χ (localIdele L P x) ∈ Subgroup.closure {z : ℂˣ | ∃ v, v ∉ S ∧
        (∀ y : (v.adicCompletion L)ˣ, Valued.v (y : v.adicCompletion L) = 1 → χ (localIdele L v y) = 1) ∧
        z = χ (localIdele L v (ϖ v))}
end HeckeValGen


