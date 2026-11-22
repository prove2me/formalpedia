-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:07.254651+00:00
-- url     : https://prove2.me/theorems/af760a91-8b07-4019-958c-c05932bde8d1
-- title:
--   Exists Variable Change Eq Lattice Curve
-- statement:
--   Definitions and structural lemmas for Exists Variable Change Eq Lattice Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsVariableChangeEqLatticeCurve.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology
noncomputable section
namespace GlobalTheory
def latticeCurve (L : PeriodPair) : WeierstrassCurve ℂ := ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩
lemma latticeCurve_Δ (L : PeriodPair) : (latticeCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [latticeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring
def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp [τ.im_ne_zero] at h1
    simp [h1] at h2
    exact ⟨h1, h2⟩
theorem exists_lattice_eq_mul_tau (L : PeriodPair) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  have hi := LinearIndependent.pair_iff.mp L.indep
  have h2 : L.ω₂ ≠ 0 := fun h ↦ by simpa using (hi 0 1 (by simp [h])).2
  have him : (L.ω₁ / L.ω₂).im ≠ 0 := fun h ↦ by
    have h3 : L.ω₁ / L.ω₂ = ((L.ω₁ / L.ω₂).re : ℂ) := Complex.ext (by simp) (by simpa using h)
    have := (hi 1 (-(L.ω₁ / L.ω₂).re) (by
      simp only [Complex.real_smul, Complex.ofReal_neg, ← h3]
      field_simp
      simp)).1
    simp at this
  rcases lt_or_gt_of_ne him with h | h
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by simpa using h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩
section
variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h
theorem latticeG_eq_E {k : ℕ} (hk : 3 ≤ k) :
    L.G k = 2 * riemannZeta k * E hk τ / a ^ k := by
  let e : (Fin 2 → ℤ) → L.lattice := fun v ↦ ⟨a * (v 0 * (τ : ℂ) + v 1), (h _).mpr ⟨_, _, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro v w hvw
      have h0 : (v 0 * (τ : ℂ) + v 1) = w 0 * (τ : ℂ) + w 1 :=
        mul_left_cancel₀ ha (congrArg Subtype.val hvw)
      have h1 := congrArg Complex.im h0
      simp [τ.im_ne_zero] at h1
      rw [h1, add_right_inj] at h0
      ext i
      fin_cases i
      · exact h1
      · exact_mod_cast h0
    · rintro ⟨x, hx⟩
      obtain ⟨m, n, rfl⟩ := (h x).mp hx
      exact ⟨![m, n], rfl⟩
  have h1 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h2 : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [PeriodPair.G, ← (Equiv.ofBijective e he).tsum_eq, h2]
  have h3 : ∀ v, (((Equiv.ofBijective e he v : L.lattice) : ℂ) ^ k)⁻¹ =
      (a ^ k)⁻¹ * eisSummand k v τ := fun v ↦ by
    simp [e, eisSummand, mul_pow, mul_comm]
  simp_rw [h3]
  rw [tsum_mul_left, h1]
  field_simp
theorem g₂_eq_E₄ : L.g₂ = 4 * π ^ 4 / 3 * E₄ τ / a ^ 4 := by
  have := latticeG_eq_E ha h (k := 4) (by norm_num)
  rw [PeriodPair.g₂, this, Nat.cast_ofNat, riemannZeta_four]
  ring
theorem g₃_eq_E₆ : L.g₃ = 8 * π ^ 6 / 27 * E₆ τ / a ^ 6 := by
  have := latticeG_eq_E ha h (k := 6) (by norm_num)
  have h6 : riemannZeta 6 = π ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [PeriodPair.g₃, this, Nat.cast_ofNat, h6]
  ring
theorem latticeCurve_Δ_eq_discriminant :
    (latticeCurve L).Δ = (2 * π / a) ^ 12 * discriminant τ := by
  rw [latticeCurve_Δ, g₂_eq_E₄ ha h, g₃_eq_E₆ ha h, discriminant_eq_E₄_cube_sub_E₆_sq]
  field_simp
  ring
end
theorem latticeCurve_Δ_ne_zero (L : PeriodPair) : (latticeCurve L).Δ ≠ 0 := by
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [latticeCurve_Δ_eq_discriminant ha h]
  have := discriminant_ne_zero τ
  have := Real.pi_ne_zero
  simp [*]
instance latticeCurve_isElliptic (L : PeriodPair) : (latticeCurve L).IsElliptic :=
  ⟨(latticeCurve_Δ_ne_zero L).isUnit⟩
end GlobalTheory


