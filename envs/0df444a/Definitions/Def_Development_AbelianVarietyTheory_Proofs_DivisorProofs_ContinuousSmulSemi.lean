-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:58.362691+00:00
-- url     : https://prove2.me/theorems/c3d8aa23-4145-48be-a587-ef3831ebac88
-- title:
--   Continuous Smul Semi
-- statement:
--   Definitions and structural lemmas for Continuous Smul Semi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
namespace GlobalTheory.DiffDecay
section Weak
variable {E : Type} [AddCommGroup E] [Module ℂ E]
def WithSemi (_p : Seminorm ℂ E) : Type := E
instance (p : Seminorm ℂ E) : AddCommGroup (WithSemi p) := inferInstanceAs (AddCommGroup E)
instance (p : Seminorm ℂ E) : Module ℂ (WithSemi p) := inferInstanceAs (Module ℂ E)
instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (WithSemi p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := WithSemi p) p.toAddGroupSeminorm
instance (p : Seminorm ℂ E) : NormedSpace ℂ (WithSemi p) where
  norm_smul_le a x := (map_smul_eq_mul p a x).le
end Weak
section Tame
variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]
def Tame (R : W → E →ₗ[ℂ] E) : Prop :=
  ∀ p : Seminorm ℂ E, Continuous p → ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧
    ∀ w f, p (R w f - f) ≤ ‖w‖ * (1 + ‖w‖) ^ M * q f
end Tame
section Heis
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Type} [SeminormedAddCommGroup W]
def heisOp (L : V →L[ℝ] ℝ) (k : ℝ) (a : V) : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k))).comp (SchwartzMap.compSubConstCLM ℂ (-a))
end Heis
end GlobalTheory.DiffDecay
end


