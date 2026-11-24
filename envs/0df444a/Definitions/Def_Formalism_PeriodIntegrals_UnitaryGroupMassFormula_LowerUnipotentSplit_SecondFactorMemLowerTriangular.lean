-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:31:07.871926+00:00
-- url     : https://prove2.me/theorems/af1a4750-59c1-47f0-a132-8a6e33734842
-- title:
--   Second Factor Mem Lower Triangular
-- statement:
--   Definitions and structural lemmas for Second Factor Mem Lower Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
def monoInv (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a i => if i = w a then (d a)⁻¹ else 0
abbrev Btw (i j : Fin m) : Type := {k : Fin m // j < k ∧ k < i}
variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)
def xs : Fin m → Fin m → ℂ
  | i, j => l i j - ∑ k : Btw i j,
      (if S i k.1 then xs i k.1 else 0) * (if S k.1 j then 0 else xs k.1 j)
termination_by i j => (i : ℕ) - j
decreasing_by
  all_goals
    have h1 := k.2.1
    have h2 := k.2.2
    simp only [Fin.lt_def] at h1 h2
    omega
def fac1 : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if j < i ∧ S i j then xs S l i j else 0
def fac2 : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i = j then 1 else if j < i ∧ ¬ S i j then xs S l i j else 0
end PI.LowUniSplit


