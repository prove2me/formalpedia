-- Prove2me | Definitions.Def_RiemannMasullo_AdelicExtensions
-- name    : RiemannMasullo_AdelicExtensions
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:40:48.060996+00:00
-- url     : https://prove2.me/theorems/0761b230-487b-42ec-9b2e-b86a6f58c341
-- title:
--   Adeles integral outside a finite set and adelic extensions of embeddings
-- statement:
--   The subring of adeles integral outside a finite set imposes the local valuation-ring condition at all remaining finite places. An adelic extension of a field embedding is a continuous ring map that agrees with the embedding on diagonal elements and respects the vanishing of each component at places above it.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L216-L252

import Mathlib

noncomputable section
namespace RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

def integralAdelesOutside (S : Finset (Primes(F))) : Subring 𝔸[F] :=
  ⨅ (v : Primes(F)) (_ : v ∉ S), (v.adicCompletionIntegers F).toSubring.comap
    ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F]))

def IsAdeleExtension {L : Type*} [Field L] [NumberField L] (σ : F →+* L) (f : 𝔸[F] →+* 𝔸[L]) :
    Prop :=
  Continuous f ∧ (∀ x, f (algebraMap F 𝔸[F] x) = algebraMap L 𝔸[L] (σ x)) ∧
  (∀ (w : InfinitePlace L) (a : 𝔸[F]), a.1 (w.comap σ) = 0 → (f a).1 w = 0) ∧
  (∀ (v : Primes(F)) (w : Primes(L)), v.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom σ) →
    ∀ a : 𝔸[F], a.2 v = 0 → (f a).2 w = 0)
end RiemannMasullo


