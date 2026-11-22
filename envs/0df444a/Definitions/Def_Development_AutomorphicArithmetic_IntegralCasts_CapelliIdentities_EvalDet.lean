-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:04.333602+00:00
-- url     : https://prove2.me/theorems/77314ccb-b533-4a81-86dc-381ef33be5de
-- title:
--   Eval Det
-- statement:
--   Definitions and structural lemmas for Eval Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvalDet.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi25.UG :
    ℕ → Type :=
    fun (N : ℕ) ↦ ↥(Matrix.unitaryGroup (Fin N) ℂ)
noncomputable def UpperTheory.Reformulated.B.Qi25.ent :
    {N : ℕ} → UpperTheory.Reformulated.B.Qi25.UG N → Fin N × Fin N → ℂ :=
    fun {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) (ij : Fin N × Fin N) ↦ (↑g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2
noncomputable def UpperTheory.Reformulated.B.Qi25.IsPD :
    {N : ℕ} → (UpperTheory.Reformulated.B.Qi25.UG N → ℂ) → Prop :=
    fun {N : ℕ} (f : UpperTheory.Reformulated.B.Qi25.UG N → ℂ) ↦
      ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
        ∀ (g : UpperTheory.Reformulated.B.Qi25.UG N),
          f g * (↑g : Matrix (Fin N) (Fin N) ℂ).det ^ k =
            (MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g) : MvPolynomial (Fin N × Fin N) ℂ → ℂ) P


