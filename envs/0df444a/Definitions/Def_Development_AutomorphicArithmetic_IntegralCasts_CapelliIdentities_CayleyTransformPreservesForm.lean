-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:56.406432+00:00
-- url     : https://prove2.me/theorems/83b87366-7e26-417d-a853-21cc5190eb78
-- title:
--   Cayley Transform Preserves Form
-- statement:
--   Definitions and structural lemmas for Cayley Transform Preserves Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleyTransformPreservesForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ
noncomputable def UpperTheory.Reformulated.B.Qk20.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)
noncomputable def UpperTheory.Reformulated.B.Qk20.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qk20.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qk20.Hpk k r + UpperTheory.Reformulated.B.Qk20.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)
noncomputable def UpperTheory.Reformulated.B.Qk20.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qk20.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qk20.UH (UpperTheory.Reformulated.B.Qk20.Hpk k r)
noncomputable def UpperTheory.Reformulated.B.Qk20.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qk20.Mat k r → UpperTheory.Reformulated.B.Qk20.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)⁻¹


