-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:26.678395+00:00
-- url     : https://prove2.me/theorems/876a912c-996a-44e1-b58c-7d0b1b6329fd
-- title:
--   Valued Algebra Map Eq One
-- statement:
--   Definitions and structural lemmas for Valued Algebra Map Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ValuedAlgebraMapEqOne.lean

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
namespace GlobalTheory.Mem.Chr
variable (L : Type) [Field L] [NumberField L]
abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ
def diagUnits : Lˣ →* Ideles L := Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom
open Classical in

def finSingle (v : HeightOneSpectrum (𝓞 L)) : v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L where
  toFun x := ⟨Pi.mulSingle v x, by
    refine Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset ?_)
    intro w hw
    by_contra h
    apply hw
    have h' : w ≠ v := h
    rw [Pi.mulSingle_eq_of_ne h']
    exact one_mem _⟩
  map_one' := by
    apply Subtype.ext
    exact Pi.mulSingle_one v
  map_mul' x y := by
    apply Subtype.ext
    exact Pi.mulSingle_mul v x y
def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp (finSingle L v))
open Classical in

def infIdele (w : InfinitePlace L) : (w.Completion)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (MonoidHom.mulSingle (fun w : InfinitePlace L => w.Completion) w))
end GlobalTheory.Mem.Chr


