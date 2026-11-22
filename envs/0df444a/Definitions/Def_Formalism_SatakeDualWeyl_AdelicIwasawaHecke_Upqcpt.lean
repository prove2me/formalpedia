-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:09.192648+00:00
-- url     : https://prove2.me/theorems/4ffe7663-a437-458c-8870-fdb2ec95a0d6
-- title:
--   Upqcpt
-- statement:
--   Definitions and structural lemmas for Upqcpt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Upqcpt.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  rw [Jpq_eq_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  rcases i with i | i <;> simp
def JpqUnit (p q : ℕ) : GL (Fin p ⊕ Fin q) ℂ :=
  ⟨Formalism.UG.Jpq p q, Formalism.UG.Jpq p q, Jpq_mul_self p q, Jpq_mul_self p q⟩
end Formalism.UG.P


