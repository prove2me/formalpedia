-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:05.633146+00:00
-- url     : https://prove2.me/theorems/4c00f75f-71df-4820-8152-5511da77a3a4
-- title:
--   Tendsto Under Cofinite
-- statement:
--   Definitions and structural lemmas for Tendsto Under Cofinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/HeckeCharacterChoice/TendstoUnderCofinite.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace KStar.Choice
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
noncomputable def complMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] : v.adicCompletion K →+* w.adicCompletion L :=
  ((adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L v w).continuous)).comp
    (adicCompletion.equiv K v).toRingHom
section
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
theorem continuous_complMap : Continuous (complMap v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)
theorem complMap_algebraMap (x : K) :
    complMap v w (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) := by
  apply adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe
    (uniformContinuous_algebraMap_liesOver K L v w).continuous (WithVal.toVal _ x)
theorem complMap_mem {x : v.adicCompletion K} (hx : x ∈ v.adicCompletionIntegers K) :
    complMap v w x ∈ w.adicCompletionIntegers L := by
  have hO : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isOpen_valuationSubring _
  have hC : IsClosed (w.adicCompletionIntegers L : Set (w.adicCompletion L)) :=
    Valued.isClosed_valuationSubring _
  have h := (denseRange_algebraMap K v).open_subset_closure_inter hO hx
  refine (hC.preimage (continuous_complMap v w)).closure_subset (closure_mono ?_ h)
  rintro _ ⟨h1, a, rfl⟩
  have h2 : v.valuation K a ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' v a]; exact h1
  rw [Set.mem_preimage, complMap_algebraMap]
  change Valued.v ((algebraMap K L a : L) : w.adicCompletion L) ≤ 1
  rw [valuedAdicCompletion_eq_valuation', ← valuation_liesOver L v w]
  exact pow_le_one' h2 _
end
instance liesOver_under (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
omit [NumberField K] [NumberField L] in
instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
variable (K L)
theorem tendsto_under_cofinite :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite
      Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w => w.asIdeal)
    ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).subset ?_)
    fun a _ b _ h => HeightOneSpectrum.ext h
  rintro _ ⟨w, hw, rfl⟩
  obtain rfl : w.under (𝓞 K) = v := hw
  exact ⟨w.isPrime, inferInstance⟩
noncomputable def finAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (B₁ := fun v => v.adicCompletionIntegers K) (B₂ := fun w => w.adicCompletionIntegers L)
    (fun w => w.under (𝓞 K)) (tendsto_under_cofinite K L)
    (fun w => complMap (w.under (𝓞 K)) w)
    (Filter.Eventually.of_forall fun w _ hx => complMap_mem _ w hx)
noncomputable def infAdeleMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w : InfinitePlace L =>
    (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) _)
noncomputable def adeleMap : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infAdeleMap K L) (finAdeleMap K L)
end KStar.Choice


