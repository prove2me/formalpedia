-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:23.6399+00:00
-- url     : https://prove2.me/theorems/c424f071-15f0-44fe-b61c-a021608f7b16
-- title:
--   Coef VFCont Diff On
-- statement:
--   Definitions and structural lemmas for Coef VFCont Diff On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoefVFContDiffOn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
namespace GlobalTheory.VFComp
variable {d : ℕ}
def coefB (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  if n ≤ m then ∑ j, c j x * fderiv ℝ (a n w) x (ev j) else 0
def coefA (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ) :
    (n : ℕ) → (Fin n → Fin d) → E d → ℂ
  | 0, _ => fun _ => 0
  | k + 1, w => fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0
def coefVF (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (n : ℕ) (w : Fin n → Fin d) (x : E d) : ℂ :=
  coefA m a c n w x + coefB m a c n w x
end GlobalTheory.VFComp
namespace GlobalTheory.VFComp
variable {d : ℕ}
end GlobalTheory.VFComp
namespace GlobalTheory.VFComp
variable {d : ℕ}
end GlobalTheory.VFComp
namespace GlobalTheory.VFComp
variable {d : ℕ}
end GlobalTheory.VFComp


