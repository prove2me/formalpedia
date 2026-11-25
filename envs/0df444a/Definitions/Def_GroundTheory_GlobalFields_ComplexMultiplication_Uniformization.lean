-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:31:06.744988+00:00
-- url     : https://prove2.me/theorems/db993ead-0d2b-53a9-a2e0-cbaf57832cb6
-- title:
--   Uniformization
-- statement:
--   Definitions and structural lemmas for Uniformization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Uniformization.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_degree_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_codiscrete_eval_weierstrassP_ne_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_nhdsNE_of_eventually_codiscrete
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_torusOrder
import Theorems.Thm_GroundTheory_Global_Elliptic_finsum_toNat_torusOrder_sub_const
import Theorems.Thm_GroundTheory_Global_Elliptic_isEllipticFunction_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_torusOrder_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable (L : PeriodPair)
def weierstrassCurve : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)
instance : (weierstrassCurve L).IsShortNF := ⟨rfl, rfl, rfl⟩
@[simp] lemma weierstrassCurve_a₁ : (weierstrassCurve L).a₁ = 0 := rfl
@[simp] lemma weierstrassCurve_a₂ : (weierstrassCurve L).a₂ = 0 := rfl
@[simp] lemma weierstrassCurve_a₃ : (weierstrassCurve L).a₃ = 0 := rfl
@[simp] lemma weierstrassCurve_a₄ : (weierstrassCurve L).a₄ = -(L.g₂ / 4) := rfl
@[simp] lemma weierstrassCurve_a₆ : (weierstrassCurve L).a₆ = -(L.g₃ / 4) := rfl
def discr : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2
theorem weierstrassCurve_Δ : (weierstrassCurve L).Δ = discr L := by
  rw [WeierstrassCurve.Δ_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  ring
variable {L}
lemma sum_le_finsum_of_finite {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (s : Finset α) : ∑ x ∈ s, u x ≤ ∑ᶠ x, u x := by
  classical
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset ∪ s) (fun x hx ↦ by simp [hx])]
  exact Finset.sum_le_sum_of_subset Finset.subset_union_right
lemma isEllipticFunction_weierstrassP_sub (c : ℂ) :
    IsEllipticFunction L (fun z ↦ ℘[L] z - c) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [isPeriodic_weierstrassP z l hl]⟩
  have := L.meromorphic_weierstrassP z
  fun_prop
lemma meromorphicOrderAt_weierstrassP_sub_ne_top (c z : ℂ) :
    meromorphicOrderAt (fun w ↦ ℘[L] w - c) z ≠ ⊤ := by
  intro htop
  have h1 := meromorphicOrderAt_eq_top_iff.1 htop
  have h2 := eventually_nhdsNE_of_eventually_codiscrete
    (eventually_codiscrete_eval_weierstrassP_ne_zero (L := L) (Polynomial.X_sub_C_ne_zero c)) z
  obtain ⟨w, hw1, hw2⟩ := (h1.and h2).exists
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hw2
  exact hw2 hw1
lemma le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) {n : ℕ}
    (h : ∀ i < n, iteratedDeriv i (fun w ↦ ℘[L] w - c) z = 0) :
    n ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat := by
  have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
    (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have hne := meromorphicOrderAt_weierstrassP_sub_ne_top (L := L) c z
  have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).2 h
  rw [torusOrder_mk (isEllipticFunction_weierstrassP_sub c), ha.meromorphicOrderAt_eq]
  rw [ha.meromorphicOrderAt_eq] at hne
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt (fun w ↦ ℘[L] w - c) z :=
    ENat.ne_top_iff_exists.1 (fun h ↦ hne (by simp [h]))
  rw [← hm] at hle ⊢
  simp only [ENat.map_natCast, WithTop.untopD_coe, Int.toNat_natCast]
  exact_mod_cast hle
lemma one_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c) :
    1 ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    obtain rfl : i = 0 := by omega
    simp [hc]
lemma two_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c)
    (h' : ℘'[L] z = 0) :
    2 ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    interval_cases i
    · simp [hc]
    · rw [iteratedDeriv_one, deriv_sub_const, L.deriv_weierstrassP]
      exact h'
lemma finsum_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 2 := by
  rw [finsum_toNat_torusOrder_sub_const isEllipticFunction_weierstrassP c, degree_weierstrassP]
lemma finite_support_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    (Function.support fun x ↦ (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat).Finite :=
  (finite_support_torusOrder (isEllipticFunction_weierstrassP_sub c)).subset fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    omega
lemma torus_mk_ne {z w : ℂ} (h : z - w ∉ L.lattice) : Torus.mk L z ≠ Torus.mk L w :=
  fun e ↦ h ((Torus.mk_eq_mk_iff L).1 e)
theorem derivWeierstrassP_eq_zero_of_two_mul_mem {w : ℂ} (h : 2 * w ∈ L.lattice) :
    ℘'[L] w = 0 := by
  have h1 : ℘'[L] (w - 2 * w) = ℘'[L] w := L.derivWeierstrassP_sub_coe w ⟨_, h⟩
  rw [show w - 2 * w = -w by ring, L.derivWeierstrassP_neg] at h1
  linear_combination -h1 / 2
theorem sub_mem_or_add_mem_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h : ℘[L] z = ℘[L] w) :
    z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hfin := finite_support_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have htot := finsum_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have oz := one_le_toNat_torusOrder_weierstrassP_sub hz h
  have hzw : Torus.mk L z ≠ Torus.mk L w := torus_mk_ne h1
  by_cases h2w : 2 * w ∈ L.lattice
  · have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w}
    rw [htot, Finset.sum_pair hzw] at hsum
    have ow := two_le_toNat_torusOrder_weierstrassP_sub hw rfl
      (derivWeierstrassP_eq_zero_of_two_mul_mem h2w)
    omega
  · have hzw' : Torus.mk L z ≠ Torus.mk L (-w) := torus_mk_ne (by rwa [sub_neg_eq_add])
    have hww' : Torus.mk L w ≠ Torus.mk L (-w) :=
      torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
    have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w, Torus.mk L (-w)}
    rw [htot, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hzw, hzw'⟩), Finset.sum_pair hww'] at hsum
    have ow := one_le_toNat_torusOrder_weierstrassP_sub hw rfl
    have ow' := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
    omega
lemma notMem_lattice_of_eq {x : ℂ} (α β : ℚ) (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬(α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by
  rw [hx]
  exact fun hm ↦ h (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice.1 hm)
lemma halfPeriod_facts :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₁ / 2) + ℘[L] (L.ω₂ / 2) + ℘[L] ((L.ω₁ + L.ω₂) / 2) = 0 ∧
      4 * (℘[L] (L.ω₁ / 2) ^ 2 + ℘[L] (L.ω₁ / 2) * ℘[L] (L.ω₂ / 2) + ℘[L] (L.ω₂ / 2) ^ 2) =
        L.g₂ ∧
      L.g₃ = 4 * ℘[L] (L.ω₁ / 2) ^ 3 - L.g₂ * ℘[L] (L.ω₁ / 2) := by
  set e1 := ℘[L] (L.ω₁ / 2)
  set e2 := ℘[L] (L.ω₂ / 2)
  set e3 := ℘[L] ((L.ω₁ + L.ω₂) / 2)
  have n1 : L.ω₁ / 2 ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have n2 : L.ω₂ / 2 ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice :=
    notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num)
  have root : ∀ u, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := fun u hu h2 ↦ by
    rw [← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]
    ring
  have f1 := root _ n1 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)
  have f2 := root _ n2 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice)
  have f3 := root _ n3 (by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)
  have d12 : e1 ≠ e2 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n2 h with h' | h'
    · exact notMem_lattice_of_eq (1 / 2) (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d13 : e1 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n3 h with h' | h'
    · exact notMem_lattice_of_eq 0 (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq 1 (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d23 : e2 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n2 n3 h with h' | h'
    · exact notMem_lattice_of_eq (-1 / 2) 0 (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) 1 (by push_cast; ring) (by norm_num) h'
  have s12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d12) (by linear_combination f1 - f2)
  have s13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d13) (by linear_combination f1 - f3)
  have hs : e1 + e2 + e3 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 d23) (by linear_combination (s12 - s13) / 4)
  exact ⟨d12, d13, d23, hs, s12, by linear_combination -f1⟩
variable (L)
theorem weierstrassP_halfPeriods_ne :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) :=
  let h := halfPeriod_facts (L := L)
  ⟨h.1, h.2.1, h.2.2.1⟩
theorem discr_eq :
    discr L = 16 * ((℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2)) *
      (℘[L] (L.ω₁ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2)) *
      (℘[L] (L.ω₂ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2))) ^ 2 := by
  obtain ⟨-, -, -, hs, s12, hg3⟩ := halfPeriod_facts (L := L)
  rw [discr, hg3, ← s12, show ℘[L] ((L.ω₁ + L.ω₂) / 2) = -℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2) by
    linear_combination hs]
  ring
theorem discr_ne_zero : discr L ≠ 0 := by
  obtain ⟨d12, d13, d23⟩ := weierstrassP_halfPeriods_ne L
  rw [discr_eq]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 d12)
    (sub_ne_zero.2 d13)) (sub_ne_zero.2 d23)))
theorem weierstrassCurve_Δ_ne_zero : (weierstrassCurve L).Δ ≠ 0 := by
  rw [weierstrassCurve_Δ]
  exact discr_ne_zero L
instance : (weierstrassCurve L).IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (weierstrassCurve_Δ_ne_zero L)⟩
end Elliptic
end GroundTheory.Global


