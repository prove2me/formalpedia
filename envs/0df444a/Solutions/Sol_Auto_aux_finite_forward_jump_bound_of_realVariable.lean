-- Prove2me | solution 1 for Auto.aux_finite_forward_jump_bound_of_realVariable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:49.660862+00:00
-- url     : https://prove2.me/submissions/f9f32317-9ce8-4aa5-bee8-1a4724e7af3c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_memLp_liftedCuboidEmbed
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftedCuboidEmbed_le_count
public import Theorems.Thm_Auto_aux_CuboidNorm_natToInt_support_map
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_natToInt_eq_count
public import Theorems.Thm_Auto_aux_eLpNorm_truncate_le
public import Theorems.Thm_Auto_aux_finite_forward_jump_energy_lower
public import Theorems.Thm_Auto_aux_finite_continuous_to_discrete_constant_bridge
section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
@[simp] private theorem aux_orbit_zero {X : Type*} (S : Fin 0 → X → X)
    (k : Fin 0 → ℕ) : aux_orbit S k = id :=
  rfl
@[simp] private theorem aux_orbit_succ {X : Type*} {n : ℕ}
    (S : Fin (n + 1) → X → X) (k : Fin (n + 1) → ℕ) :
    aux_orbit S k = (S 0)^[k 0] ∘
      aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ) :=
  rfl
section
universe v
end
namespace aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
end aux_CuboidNorm
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
end aux_ErgodicBox
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n J : ℕ}
    (hn : 0 < n) (p : Fin n → ℝ≥0∞) (C : ℝ) (g : ℕ → ℝ)
    (hreal : realVariableJumpBound p C g) (hJ : 0 < J)
    (N : Fin (J + 1) → ℕ) (hN : StrictMono N)
    (hNpos : ∀ q, 0 < N q) (F : Fin n → (Fin n → ℕ) → ℝ)
    (A : Finset (Fin n → ℕ))
    (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞) :
    ∑ j : Fin J, ∑ k ∈ A,
      ‖aux_discreteAverage (N j.succ) F k -
        aux_discreteAverage (N j.castSucc) F k‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (((2 : ℝ) ^ (3 * n + 6)) * C) *
        ENNReal.ofReal (g J) *
          ∏ i, eLpNorm (F i) (p i) Measure.count ^ (2 : ℕ) := by
  let ε : ℝ := (1 : ℝ) / 8
  let δ : ℝ := (1 : ℝ) / 4
  let L : ℕ := N (Fin.last J)
  let B : Finset (Fin n → ℕ) := aux_localInputSupport A L
  let F' : Fin n → (Fin n → ℕ) → ℝ := fun i ↦ aux_truncate B (F i)
  let a : Fin n → aux_ZVector n → ℝ := fun i ↦ aux_natToInt (F' i)
  let f : Fin n → ctRealVector n → ℝ :=
    fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i))
  let D : ℝ≥0∞ := ∑ j : Fin J, ∑ k ∈ A,
    ‖aux_discreteAverage (N j.succ) F k -
      aux_discreteAverage (N j.castSucc) F k‖ₑ ^ (2 : ℝ)
  let E : ℝ≥0∞ := ctEndpointEnergy J (fun q ↦ (N q : ℝ))
    ctUnitIntervalKernel f
  have hε0 : 0 ≤ ε := by dsimp [ε]; norm_num
  have hε : ε < 1 := by dsimp [ε]; norm_num
  have hεδ : ε ≤ δ := by dsimp [ε, δ]; norm_num
  have hwidth : ε + δ < 1 := by dsimp [ε, δ]; norm_num
  have ht : StrictMono (fun q : Fin (J + 1) ↦ (N q : ℝ)) := by
    intro q r hqr
    change (N q : ℝ) < (N r : ℝ)
    exact_mod_cast hN hqr
  have hsupportF' : ∀ i k, k ∉ B → F' i k = 0 := by
    intro i k hk
    simp [F', aux_truncate, hk]
  have hsupport : ∀ i z, z ∉ B.map aux_CuboidNorm.natToIntEmbedding →
      a i z = 0 := by
    intro i z hz
    exact aux_CuboidNorm.natToInt_support_map B (F' i) (hsupportF' i) z hz
  have htlower :
      (ENNReal.ofReal ((1 : ℝ) / 8) ^ (2 : ℝ) *
        ENNReal.ofReal ((1 : ℝ) / 8) ^ n) * D ≤ E := by
    have hlow := aux_finite_forward_jump_energy_lower hn hε hεδ hwidth
      N hN hNpos F A
    rw [show δ - ε = (1 : ℝ) / 8 by dsimp [ε, δ]; norm_num] at hlow
    simpa only [D, E, ε, δ, L, B, F', a, f] using hlow
  have hmem : ∀ i, MemLp (f i) (p i) volume := by
    intro i
    dsimp [f]
    apply aux_CuboidNorm.memLp_liftedCuboidEmbed hε0 hε hwidth i
      (B.map aux_CuboidNorm.natToIntEmbedding) (a i) (hsupport i)
      (p i) (hp0 i) (hptop i)
  have hreal' := hreal J hJ (fun q ↦ (N q : ℝ)) ht
    (fun q ↦ by exact_mod_cast hNpos q) f hmem
  have hvolume : ∀ i : Fin n,
      ∏ j, ENNReal.ofReal (if j = i then δ else ε) ≤ 1 := by
    intro i
    apply Finset.prod_le_one'
    intro j hj
    rw [ENNReal.ofReal_le_one]
    by_cases hji : j = i <;> simp [hji, ε, δ] <;> norm_num
  have hnorm : ∀ i, eLpNorm (f i) (p i) volume ≤
      eLpNorm (F i) (p i) Measure.count := by
    intro i
    calc
      eLpNorm (f i) (p i) volume ≤ eLpNorm (a i) (p i) Measure.count := by
        dsimp [f]
        exact aux_CuboidNorm.eLpNorm_liftedCuboidEmbed_le_count hε0 hε
          hwidth i (B.map aux_CuboidNorm.natToIntEmbedding) (a i)
          (hsupport i) (p i) (hp0 i) (hptop i) (hvolume i)
      _ = eLpNorm (F' i) (p i) Measure.count := by
        exact aux_CuboidNorm.eLpNorm_natToInt_eq_count B (F' i)
          (hsupportF' i) (p i) (hp0 i) (hptop i)
      _ ≤ eLpNorm (F i) (p i) Measure.count :=
        aux_eLpNorm_truncate_le B (F i) (p i)
  apply aux_finite_continuous_to_discrete_constant_bridge C (g J) D E
    (fun i ↦ eLpNorm (f i) (p i) volume)
    (fun i ↦ eLpNorm (F i) (p i) Measure.count) htlower
  · exact hreal'
  · exact hnorm
end Auto
