-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
-- name    : GroundTheory_AutomorphicForms_ReductionHeight
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:04.12807+00:00
-- url     : https://prove2.me/theorems/81a8ac24-1609-4c9a-a2e2-e7925557448f
-- title:
--   Reduction Height
-- statement:
--   Definitions and structural lemmas for Reduction Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
namespace GroundTheory.Automorphic
noncomputable section
namespace Reduction
section Euclid
variable {E : Type*} [NormedField E] {n : ℕ}
def euclidNorm (y : Fin n → E) : ℝ := √(∑ i, ‖y i‖ ^ 2)
end Euclid
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
def infComp (w : InfinitePlace K) (y : Fin n → 𝔸[K]) : Fin n → w.Completion := fun i => (y i).1 w
def finComp (v : HeightOneSpectrum (𝓞 K)) (y : Fin n → 𝔸[K]) : Fin n → v.adicCompletion K :=
  fun i => (y i).2 v
def infAt (w : InfinitePlace K) (g : AdelicGLn.AdelicGL K n) : GL (Fin n) w.Completion :=
  (AdelicGLn.restrictedProductEquiv K n g).1 w
def finAt (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    GL (Fin n) (v.adicCompletion K) :=
  (AdelicGLn.restrictedProductEquiv K n g).2 v
def infEval (w : InfinitePlace K) : 𝔸[K] →+* w.Completion :=
  (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
def finEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)
def adelicNorm (y : Fin n → 𝔸[K]) : ℝ :=
  (∏ w : InfinitePlace K, euclidNorm (infComp w y) ^ w.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖finComp v y‖
def HasFiniteContent (y : Fin n → 𝔸[K]) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖finComp v y‖ = 1
section LocalIntegral
variable (v : HeightOneSpectrum (𝓞 K))
end LocalIntegral
def ratVec (x : Fin n → K) : Fin n → 𝔸[K] := fun i => algebraMap K 𝔸[K] (x i)
def height (g : AdelicGLn.AdelicGL K n) (x : Fin n → K) : ℝ :=
  adelicNorm (ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]))
end Reduction
end
end GroundTheory.Automorphic


