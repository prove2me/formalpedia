-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:59:41.073302+00:00
-- url     : https://prove2.me/theorems/54c90904-cb0b-446b-bf16-b7031031c733
-- title:
--   Pairing Triangular
-- statement:
--   Definitions and structural lemmas for Pairing Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PairingTriangular.lean

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
def pair (σ z : V f) : ℝ := ∑ v, 2 * (σ v * z v).re
lemma psi_mul (σ z : V f) :
    psi (σ * z) = Complex.exp (2 * Real.pi * Complex.I * (pair σ z : ℂ)) := by
  unfold Formalism.FourierDecayAlt.crystallineComparison.psi pair
  congr 2
  push_cast
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Complex.add_conj]
  simp
lemma pair_add_left (σ σ' z : V f) : pair (σ + σ') z = pair σ z + pair σ' z := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [add_mul, mul_add]
lemma pair_smul_left (r : ℝ) (σ z : V f) : pair (r • σ) z = r * pair σ z := by
  unfold pair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [Complex.smul_re, smul_mul_assoc]
  ring
lemma pair_add_right (σ z z' : V f) : pair σ (z + z') = pair σ z + pair σ z' := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [add_mul, mul_add]
lemma pair_smul_right (r : ℝ) (σ z : V f) : pair σ (r • z) = r * pair σ z := by
  unfold pair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [Complex.smul_re, mul_smul_comm]
  ring
def pairL : V f →ₗ[ℝ] V f →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pair pair_add_left (fun c m n => by rw [pair_smul_left, smul_eq_mul])
    pair_add_right (fun c m n => by rw [pair_smul_right, smul_eq_mul])
lemma pairL_apply (σ z : V f) : pairL σ z = pair σ z := rfl
lemma pair_conj (σ : V f) :
    pair σ (fun v => starRingEnd ℂ (σ v)) = ∑ v, 2 * Complex.normSq (σ v) := by
  unfold pair
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Complex.mul_conj, Complex.ofReal_re]
lemma eq_zero_of_pair (σ : V f) (h : ∀ z, pair σ z = 0) : σ = 0 := by
  have h0 := h (fun v => starRingEnd ℂ (σ v))
  rw [pair_conj] at h0
  have h1 : ∀ v ∈ (Finset.univ : Finset (Fin f)), 2 * Complex.normSq (σ v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))).mp h0
  funext v
  have h2 := h1 v (Finset.mem_univ v)
  simpa using h2
section Lat
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
def bR : Basis (Fin (finrank ℤ La)) ℝ (V f) := (Module.finBasis ℤ La).ofZLatticeBasis ℝ La
lemma bR_apply (j : Fin (finrank ℤ La)) : bR La j = ((Module.finBasis ℤ La) j : V f) := by
  simp [bR]
lemma bR_mem (j : Fin (finrank ℤ La)) : bR La j ∈ La := by
  rw [bR_apply]
  exact ((Module.finBasis ℤ La) j).2
lemma mem_iff (z : V f) : z ∈ La ↔ ∀ j, (bR La).repr z j ∈ Set.range (algebraMap ℤ ℝ) := by
  conv_lhs => rw [← Module.Basis.ofZLatticeBasis_span ℝ La (Module.finBasis ℤ La)]
  exact Module.Basis.mem_span_iff_repr_mem ℤ (bR La) z
def Tl : (Fin (finrank ℤ La) → ℝ) ≃L[ℝ] V f := (bR La).equivFun.symm.toContinuousLinearEquiv
lemma Tl_apply (y : Fin (finrank ℤ La) → ℝ) : Tl La y = ∑ j, y j • bR La j := by
  simp [Tl, Basis.equivFun_symm_apply]
lemma Tl_symm_apply (z : V f) : (Tl La).symm z = fun j => (bR La).repr z j := by
  funext j
  simp [Tl]
lemma pair_Tl (σ : V f) (y : Fin (finrank ℤ La) → ℝ) :
    pair σ (Tl La y) = ∑ j, y j * pair σ (bR La j) := by
  rw [Tl_apply, ← pairL_apply, map_sum]
  simp only [map_smul, pairL_apply, smul_eq_mul]
def Lm : V f →ₗ[ℝ] (Fin (finrank ℤ La) → ℝ) where
  toFun σ := fun j => pair σ (bR La j)
  map_add' σ σ' := by
    funext j
    simp only [Pi.add_apply, pair_add_left]
  map_smul' r σ := by
    funext j
    simp only [Pi.smul_apply, pair_smul_left, smul_eq_mul, RingHom.id_apply]
lemma Lm_inj : Function.Injective (Lm La) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro σ hσ
  apply eq_zero_of_pair
  intro z
  have hj : ∀ j, pair σ (bR La j) = 0 := fun j => congrFun hσ j
  rw [← (Tl La).apply_symm_apply z, pair_Tl]
  simp [hj]
lemma Lm_bij : Function.Bijective (Lm La) := by
  refine ⟨Lm_inj La, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact Lm_inj La
  · rw [Module.finrank_fin_fun, ZLattice.rank ℝ La]
def Le : V f ≃ₗ[ℝ] (Fin (finrank ℤ La) → ℝ) := LinearEquiv.ofBijective (Lm La) (Lm_bij La)
lemma Le_apply (σ : V f) (j) : Le La σ j = pair σ (bR La j) := rfl
def ψd (m : Fin (finrank ℤ La) → ℤ) : V f := (Le La).symm (fun j => (m j : ℝ))
lemma pair_ψd (m : Fin (finrank ℤ La) → ℤ) (j) : pair (ψd La m) (bR La j) = m j := by
  rw [← Le_apply, ψd, LinearEquiv.apply_symm_apply]
lemma ψd_inj : Function.Injective (ψd La) := by
  intro m m' h
  funext j
  have h1 := pair_ψd La m j
  rw [h, pair_ψd] at h1
  exact_mod_cast h1.symm
lemma pair_ψd_Tl (m : Fin (finrank ℤ La) → ℤ) (y : Fin (finrank ℤ La) → ℝ) :
    pair (ψd La m) (Tl La y) = ∑ j, y j * (m j : ℝ) := by
  rw [pair_Tl]
  simp [pair_ψd]
lemma psi_ψd_Tl (m : Fin (finrank ℤ La) → ℤ) (y : Fin (finrank ℤ La) → ℝ) :
    psi (ψd La m * Tl La y) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ)) := by
  rw [psi_mul, pair_ψd_Tl]
  congr 2
  push_cast
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
lemma ψd_mem (m : Fin (finrank ℤ La) → ℤ) : ψd La m ∈ dualSet La := by
  show ∀ z ∈ La, psi (ψd La m * z) = 1
  intro z hz
  obtain ⟨n, hn⟩ : ∃ n : Fin (finrank ℤ La) → ℤ, ∀ j, (bR La).repr z j = n j := by
    have h1 := (mem_iff La z).mp hz
    exact ⟨fun j => (h1 j).choose, fun j => by simpa using (h1 j).choose_spec.symm⟩
  rw [← (Tl La).apply_symm_apply z, psi_ψd_Tl, Tl_symm_apply]
  have hs : (∑ j, ((m j : ℝ) : ℂ) * (((bR La).repr z j : ℝ) : ℂ)) = ((∑ j, m j * n j : ℤ) : ℂ) := by
    push_cast
    simp [hn]
  rw [hs, mul_comm, Complex.exp_int_mul_two_pi_mul_I]
lemma ψd_surj (σ : V f) (hσ : σ ∈ dualSet La) : ∃ m, ψd La m = σ := by
  have hσ' : ∀ z ∈ La, psi (σ * z) = 1 := hσ
  have hint : ∀ j, ∃ n : ℤ, pair σ (bR La j) = n := by
    intro j
    have h1 := hσ' (bR La j) (bR_mem La j)
    rw [psi_mul, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have h2 : ((pair σ (bR La j) : ℝ) : ℂ) = (n : ℂ) := by
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hne
      rw [hn]
      ring
    exact_mod_cast h2
  choose m hm using hint
  refine ⟨m, ?_⟩
  apply (Le La).injective
  rw [ψd, LinearEquiv.apply_symm_apply]
  funext j
  rw [Le_apply, hm]
def eD : (Fin (finrank ℤ La) → ℤ) ≃ dualSet La :=
  Equiv.ofBijective (fun m => ⟨ψd La m, ψd_mem La m⟩)
    ⟨fun m m' h => ψd_inj La (congrArg Subtype.val h),
     fun σ => by
      obtain ⟨m, hm⟩ := ψd_surj La σ.1 σ.2
      exact ⟨m, Subtype.ext hm⟩⟩
end Lat
end
end Formalism.FourierDecayAlt.P.PairingConjugationLemmas
namespace Formalism.FourierDecayAlt.P
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.P.PairingConjugationLemmas
end Formalism.FourierDecayAlt.P


