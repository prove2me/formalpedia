-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
-- name    : GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:30.02181+00:00
-- url     : https://prove2.me/theorems/1c7615eb-0c95-4c47-8bce-11f7e175bcb5
-- title:
--   Infinite Proj Infinite Embedding Of Ne
-- statement:
--   Definitions and structural lemmas for Infinite Proj Infinite Embedding Of Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
abbrev IdeleGroup : Type _ := (𝔸[K])ˣ
namespace IdeleGroup
example : IsTopologicalGroup (IdeleGroup K) := inferInstance
def prodEquiv :
    IdeleGroup K ≃ₜ* (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_toFun
  continuous_invFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_invFun
@[simp]
theorem prodEquiv_apply_fst (x : IdeleGroup K) :
    ((prodEquiv K x).1 : InfiniteAdeleRing K) = (x : 𝔸[K]).1 := rfl
@[simp]
theorem prodEquiv_apply_snd (x : IdeleGroup K) :
    ((prodEquiv K x).2 : FiniteAdeleRing (𝓞 K) K) = (x : 𝔸[K]).2 := rfl
def toInfinite : IdeleGroup K →* (InfiniteAdeleRing K)ˣ :=
  (MonoidHom.fst _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom
def toFinite : IdeleGroup K →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (MonoidHom.snd _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom
def diagonal : Kˣ →* IdeleGroup K :=
  Units.map (algebraMap K 𝔸[K]).toMonoidHom
@[simp]
theorem coe_diagonal (x : Kˣ) : ((diagonal K x : IdeleGroup K) : 𝔸[K]) = algebraMap K 𝔸[K] x :=
  rfl
end IdeleGroup
abbrev IdeleClassGroup : Type _ := IdeleGroup K ⧸ (IdeleGroup.diagonal K).range
namespace IdeleClassGroup
example : CommGroup (IdeleClassGroup K) := inferInstance
example : IsTopologicalGroup (IdeleClassGroup K) := inferInstance
def mk : IdeleGroup K →* IdeleClassGroup K := QuotientGroup.mk' _
end IdeleClassGroup
namespace IdeleGroup
section Finite
variable {K}
open Classical in

def finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletionIntegers K) v x
  map_one' := Subtype.ext (Pi.mulSingle_one (M := fun w : HeightOneSpectrum (𝓞 K) ↦
    w.adicCompletion K) v)
  map_mul' x y := Subtype.ext (Pi.mulSingle_mul v x y)
def finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod 1 (finiteAdeleSingle v) :
    v.adicCompletion K →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
def finiteProj (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup K →* (v.adicCompletion K)ˣ :=
  Units.map (((RestrictedProduct.evalMonoidHom
      (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v).comp
    (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :
    InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* v.adicCompletion K)
end Finite
section Infinite
variable {K}
open Classical in

def infiniteAdeleSingle (w : InfinitePlace K) : w.Completion →* InfiniteAdeleRing K :=
  MonoidHom.mulSingle (fun u : InfinitePlace K ↦ u.Completion) w
def infiniteEmbedding (w : InfinitePlace K) : (w.Completion)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod (infiniteAdeleSingle w) 1 :
    w.Completion →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
def infiniteProj (w : InfinitePlace K) : IdeleGroup K →* (w.Completion)ˣ :=
  Units.map (((Pi.evalMonoidHom (fun u : InfinitePlace K ↦ u.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :
    InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* w.Completion)
end Infinite
def integralAtFinite : Submonoid 𝔸[K] where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K}
  one_mem' v := one_mem (v.adicCompletionIntegers K)
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
def standardOpenSubgroup : Subgroup (IdeleGroup K) := (integralAtFinite K).units
end IdeleGroup
end
end GroundTheory.Global


