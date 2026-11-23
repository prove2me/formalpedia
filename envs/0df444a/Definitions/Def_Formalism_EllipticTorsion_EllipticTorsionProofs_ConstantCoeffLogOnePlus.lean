-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:06.217257+00:00
-- url     : https://prove2.me/theorems/851a09f8-d2e7-4ce4-8338-89d6dd8f7c84
-- title:
--   Constant Coeff Log One Plus
-- statement:
--   Definitions and structural lemmas for Constant Coeff Log One Plus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ConstantCoeffLogOnePlus.lean

import Definitions.Def_Formalism_EllipticTorsion_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
def eulFun (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun d => (d.degree : K) * MvPowerSeries.coeff d F
theorem coeff_eulFun (F : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (eulFun F) = (d.degree : K) * MvPowerSeries.coeff d F := rfl
def eulLin : MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K where
  toFun := eulFun
  map_add' F G := by
    ext d
    simp only [coeff_eulFun, map_add, mul_add]
  map_smul' c F := by
    ext d
    simp only [coeff_eulFun, map_smul, smul_eq_mul, RingHom.id_apply]
    ring
theorem eulFun_mul (F G : MvPowerSeries σ K) :
    eulFun (F * G) = F • eulFun G + G • eulFun F := by
  ext d
  rw [smul_eq_mul, smul_eq_mul, mul_comm G, map_add, coeff_eulFun, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_eulFun, coeff_eulFun, ← hp, map_add, Nat.cast_add]
  ring
def eul : Derivation K (MvPowerSeries σ K) (MvPowerSeries σ K) :=
  Derivation.mk' eulLin fun a b => eulFun_mul a b
def Agree (N : ℕ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → MvPowerSeries.coeff d F = MvPowerSeries.coeff d G
theorem Agree.eulFun {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G) :
    Agree N (eulFun F) (eulFun G) := by
  intro d hd
  rw [coeff_eulFun, coeff_eulFun, h d hd]
def truncLog (N : ℕ) (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  ∑ n ∈ Finset.range N, PowerSeries.coeff n (PowerSeries.log K) • f ^ n
variable [IsUltrametricDist K]
end Formalism.ELL.EulerSeries
namespace Formalism.ELL
end Formalism.ELL


