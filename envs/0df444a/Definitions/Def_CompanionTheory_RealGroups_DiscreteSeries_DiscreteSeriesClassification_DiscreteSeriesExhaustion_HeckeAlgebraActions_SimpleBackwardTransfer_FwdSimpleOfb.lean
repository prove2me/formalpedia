-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
-- name    : CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:30.694908+00:00
-- url     : https://prove2.me/theorems/a4364eef-28ca-4ea6-8496-61b9d73758fd
-- title:
--   Fwd Simple Ofb
-- statement:
--   Definitions and structural lemmas for Fwd Simple Ofb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
variable {n : ℕ}
section maps
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
theorem fsb_glRel_surj {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hs : Function.Surjective f) (hf : ∀ a b v, f (E a b v) = E' a b (f v)) (hE : GlRel E) :
    GlRel E' := by
  intro a b c d
  have key := hE a b c d
  ext w
  obtain ⟨v, rfl⟩ := hs w
  have key' := congrArg (fun T => f (T v)) key
  split_ifs at key' ⊢ <;> simpa [hf] using key'
end maps
def fsbQuot (M : GMod n) (Z : Submodule ℂ M.V) (hZ : ∀ a b, ∀ x ∈ Z, M.E a b x ∈ Z) : GMod n where
  V := M.V ⧸ Z
  E := fun a b => Z.mapQ Z (M.E a b) (fun x hx => hZ a b x hx)
  gl := fsb_glRel_surj Z.mkQ (Submodule.mkQ_surjective Z) (fun a b v => by simp) M.gl
end CompanionTheory.RgExh.Hk


