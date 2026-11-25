-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:19.970164+00:00
-- url     : https://prove2.me/theorems/58ebbf15-1d58-4f77-8e73-0d39b29392bf
-- title:
--   Cayley Hamilton Statement
-- statement:
--   Definitions and structural lemmas for Cayley Hamilton Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk
namespace GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
section General
variable {A : Type*} [Ring A] [Algebra ℂ A]
def PolF (f : ℂ → A) : Prop := ∃ p : A[X], ∀ y : ℂ, p.eval (algebraMap ℂ A y) = f y
end General
variable {n : ℕ}
def liftL (V : Type) [AddCommGroup V] [Module ℂ V] (I : Type) :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (I → V) where
  toFun Z := Z.compLeft I
  map_one' := LinearMap.ext fun _ => funext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  map_zero' := LinearMap.ext fun _ => funext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  commutes' c := LinearMap.ext fun f => funext fun i => by
    show (algebraMap ℂ (Module.End ℂ V) c) (f i) = (algebraMap ℂ (Module.End ℂ (I → V)) c f) i
    simp [Module.algebraMap_end_apply]
end GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm


