-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
-- name    : Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:10.001858+00:00
-- url     : https://prove2.me/theorems/849a6490-e4f2-40ba-83b4-4f4c2c338601
-- title:
--   UMGSmooth A
-- statement:
--   Definitions and structural lemmas for UMGSmooth A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKEst.UMGS
open Filter Topology Function
variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {ι : Type} [Fintype ι]
def pr {k : ℕ} (γ : Fin k → (Multiplicative ℝ →* G)) (t : Fin k → ℝ) : G :=
  (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod
def Gn (m : ι → G →* A) (γ : Multiplicative ℝ →* G) (Y : ι → A) : Prop :=
  ∀ w (t : ℝ), m w (γ (Multiplicative.ofAdd t)) = NormedSpace.exp (t • Y w)
def cj (x : G) (γ : Multiplicative ℝ →* G) : Multiplicative ℝ →* G := (MulAut.conj x⁻¹).toMonoidHom.comp γ
omit [TopologicalSpace G] [ContinuousMul G] in
theorem cj_apply (x : G) (γ : Multiplicative ℝ →* G) (s : Multiplicative ℝ) : cj x γ s = x⁻¹ * γ s * x := by
  simp [cj]
omit [TopologicalSpace G] [ContinuousMul G] [Fintype ι] in
theorem Gn.cj {m : ι → G →* A} {γ : Multiplicative ℝ →* G} {Y : ι → A} (h : Gn m γ Y) (x : G) :
    Gn m (cj x γ) fun w => m w x⁻¹ * Y w * m w x := by
  intro w t
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let u : Aˣ := Units.map (m w) (toUnits x⁻¹)
  have h1 : (u : A) = m w x⁻¹ := rfl
  have h2 : ((u⁻¹ : Aˣ) : A) = m w x := by simp [u]
  have := NormedSpace.exp_units_conj u (t • Y w)
  rw [h1, h2] at this
  rw [cj_apply, map_mul, map_mul, h w t, ← this, mul_smul_comm, smul_mul_assoc]
end PositivityTheory.ThKEst.UMGS
end


