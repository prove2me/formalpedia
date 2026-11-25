-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:18.521181+00:00
-- url     : https://prove2.me/theorems/1bed09db-b61d-4fee-ba2c-3e911115dbfb
-- title:
--   Acyclicity Lemma Depth Differential Cokernels Finite L
-- statement:
--   Definitions and structural lemmas for Acyclicity Lemma Depth Differential Cokernels Finite L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
namespace GlobalTheory
namespace FiniteLengthComplex
variable {R : Type} [CommRing R]
noncomputable def extCongrLeft {X X' : ModuleCat.{0} R} (e : X ≅ X') (Y : ModuleCat.{0} R) (n : ℕ) :
    Abelian.Ext.{0} X' Y n ≃ₗ[R] Abelian.Ext.{0} X Y n :=
  LinearEquiv.ofLinearMap ((Ext.mk₀ e.hom).precompOfLinear R Y (zero_add n))
    ((Ext.mk₀ e.inv).precompOfLinear R Y (zero_add n))
    (by ext x; simp) (by ext x; simp)
section Complex
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
noncomputable def opcyclesShortComplex (i : ℕ) : ShortComplex (ModuleCat.{0} R) :=
  ShortComplex.mk (C.fromOpcycles i (i + 1)) (C.pOpcycles (i + 1)) (by
    rw [← cancel_epi (C.pOpcycles i)]
    simp)
end Complex
end FiniteLengthComplex
end GlobalTheory


