-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T08:11:52.771974+00:00
-- url     : https://prove2.me/theorems/029897e3-dbd5-456a-bc6f-8b634150020d
-- title:
--   Sandwich Of Of Charts
-- statement:
--   Definitions and structural lemmas for Sandwich Of Of Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/SandwichOfOfCharts.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
namespace PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
def NormRL : Prop := ∀ (k r : ℕ) (X : Mat k r), ‖RL X‖ = ‖X‖
def LogG : Prop := ∀ k r : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ L : Mat k r, ‖L‖ < δ →
  NormedSpace.exp L ∈ UH (Hpk k r) → L ∈ uH k r
def ChartFwd : Prop := ∀ (k r : ℕ) (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Vs k r, ‖v‖ < δ →
  ∃ Y ∈ uH k r, NormedSpace.exp Y = Phi k r v.1 v.2.1 v.2.2.1 v.2.2.2 ∧ ‖Y‖ ≤ (1 + η) * ‖Lm k r v‖
def ChartBwd : Prop := ∀ (k r : ℕ) (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ Y ∈ uH k r, ‖Y‖ < δ →
  ∃ v ∈ Vs k r, Phi k r v.1 v.2.1 v.2.2.1 v.2.2.2 = NormedSpace.exp Y ∧ ‖v‖ < η ∧
    (1 - η) * ‖Lm k r v‖ ≤ ‖Y‖
def ChartFwdOf : Prop :=
  NormRL → LogG → LongWeylElementSquare → BigCellG → PhiForm → PhiDeriv → LieWb → ExpN → LIso → ChartFwd
def ChartBwdOf : Prop :=
  NormRL → LogG → LongWeylElementSquare → BigCellG → PhiForm → PhiDeriv → LieWb → ExpN → LIso → ChartBwd
def SideB : Prop :=
  NormRL → LieG → LieWb → PhiForm → LieEN → LIso → ChartFwd →
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ UWb k r →
      Matrix.of n' ∈ Nset k r →
      Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ
def SideA : Prop :=
  NormRL → LieG → LieWb → GaussUniq → PhiForm → LongWeylElementSquare → LieEN → ExpN → LIso → ChartBwd →
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ UWb k r →
      Matrix.of n' ∈ Nset k r →
      Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)
end PI.SwSandwichOfWork


