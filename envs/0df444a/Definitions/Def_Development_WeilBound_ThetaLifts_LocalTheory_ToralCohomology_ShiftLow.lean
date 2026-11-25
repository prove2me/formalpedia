-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:13:39.091541+00:00
-- url     : https://prove2.me/theorems/401ce19f-603e-59d0-9833-b0c598144b5f
-- title:
--   Shift Low
-- statement:
--   Definitions and structural lemmas for Shift Low, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ToralCohomology/ShiftLow.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
namespace PositivityTheory.ThKG.CayleyTransformDarboux
section Gen
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
def Lie (act : A →ₗ[ℂ] Module.End ℂ M) : Prop := ∀ X Y, act X * act Y - act Y * act X = act (X * Y - Y * X)
def St (act : A →ₗ[ℂ] Module.End ℂ M) (g : Submodule ℂ A) (N : Submodule ℂ M) : Prop := ∀ Z ∈ g, ∀ x ∈ N, act Z x ∈ N
def filt (act : A →ₗ[ℂ] Module.End ℂ M) (l : Submodule ℂ A) (V : Submodule ℂ M) : ℕ → Submodule ℂ M
  | 0 => V
  | n + 1 => filt act l V n ⊔ ⨆ Z ∈ l, (filt act l V n).map (act Z)
def low (T : Module.End ℂ M) (lam : ℂ) : Submodule ℂ M := ⨆ t : {t : ℝ // 0 < t}, T.eigenspace (lam - (t.1 : ℂ))
end Gen
section Units
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
def un (w : ι) (a b : I) : ι → Matrix I I ℂ := Pi.single w (Matrix.single a b 1)
def alg (ι : Type) (r : I → I → Prop) : Submodule ℂ (ι → Matrix I I ℂ) where
  carrier := {Z | ∀ w a b, ¬ r a b → Z w a b = 0}
  add_mem' := fun {x y} hx hy w a b h => by simp [hx w a b h, hy w a b h]
  zero_mem' := fun _ _ _ _ => rfl
  smul_mem' := fun c x hx w a b h => by simp [hx w a b h]
def stab (act : (ι → Matrix I I ℂ) →ₗ[ℂ] Module.End ℂ M) (N : Submodule ℂ M) : Submodule ℂ (ι → Matrix I I ℂ) where
  carrier := {Z | ∀ x ∈ N, act Z x ∈ N}
  add_mem' := fun {a b} ha hb x hx => by rw [map_add, LinearMap.add_apply]; exact add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c a ha x hx => by rw [map_smul, LinearMap.smul_apply]; exact N.smul_mem c (ha x hx)
def dg (ι : Type) (h : I → ℝ) : ι → Matrix I I ℂ := fun _ => Matrix.diagonal fun a => (h a : ℂ)
end Units
end PositivityTheory.ThKG.CayleyTransformDarboux
end


