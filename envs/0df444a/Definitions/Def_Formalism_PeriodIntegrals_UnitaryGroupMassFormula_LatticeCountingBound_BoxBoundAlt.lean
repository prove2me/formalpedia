-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:48.287719+00:00
-- url     : https://prove2.me/theorems/a040dffc-5be6-4979-9df6-1c0a2b1c069e
-- title:
--   Box Bound Alt
-- statement:
--   Definitions and structural lemmas for Box Bound Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/BoxBoundAlt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.UnitaryGroupMassFormula.LCG
def hsN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (Formalism.REAL.hs A)
def amat (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) :
    Matrix (Fin I.n) (Fin I.n) ℂ :=
  Formalism.MainNotions.S.uMat ((x.1 v)⁻¹) * ((I.P v)⁻¹ * δ.map (I.φ v) * I.P v) * Formalism.MainNotions.S.uMat (y.1 v)
def BoxBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε),
    hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt (n : ℝ) * Real.exp (PI.symD ε g)
def LatMap : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x y γ : I.GA) (g : GL (Fin I.n) I.E),
    I.fmat γ.2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) →
    (x⁻¹ * γ * y).2 ∈ I.Kset →
    ∀ u ∈ PI.LatCountG.latSet I y, (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u ∈ PI.LatCountG.latSet I x
def LatSub : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA) (u u' : Fin I.n → I.E),
    u ∈ PI.LatCountG.latSet I x → u' ∈ PI.LatCountG.latSet I x → u - u' ∈ PI.LatCountG.latSet I x
def Sep : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x y : I.GA), 0 < PI.LatCountG.tau1 I x → 0 < PI.LatCountG.tau1 I y →
    ∀ δ : Matrix (Fin I.n) (Fin I.n) I.E, δ ≠ 0 →
      (∀ u ∈ PI.LatCountG.latSet I y, δ *ᵥ u ∈ PI.LatCountG.latSet I x) →
      (PI.LatCountG.tau1 I x * PI.LatCountG.tau1 I y) ^ I.f ≤ ∏ v, hsN (amat I x y v δ)
def PackLem : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (R ρ : ι → ℝ), (∀ v, 0 < ρ v) → (∀ v, 0 ≤ R v) →
    ∀ T : Finset (ι → Matrix (Fin N) (Fin N) ℂ),
      (∀ p ∈ T, ∀ v, hsN (p v) ≤ R v) →
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∃ v, ρ v ≤ hsN (p v - q v)) →
      (T.card : ℝ) ≤ ∏ v, ((2 * R v + ρ v) / ρ v) ^ (2 * N ^ 2)
def NPos : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), 0 < PI.LatCountG.tau1 I x → 1 ≤ I.n
def CardPl : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, Fintype.card (InfinitePlace I.F) = I.f
end PI.UnitaryGroupMassFormula.LCG


