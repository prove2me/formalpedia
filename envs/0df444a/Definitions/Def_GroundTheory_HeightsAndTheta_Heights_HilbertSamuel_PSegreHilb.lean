-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSegreHilb
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSegreHilb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:38:45.306264+00:00
-- url     : https://prove2.me/theorems/a368e59a-f931-42ee-bf05-70a4969f38c1
-- title:
--   PSegre Hilb
-- statement:
--   Definitions and structural lemmas for PSegre Hilb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSegreHilb.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreHilb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (F : Type) [Field F]
theorem weight_blockWeight_apply (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) e k = ∑ i, e ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem blockWeight_unit (v : Σ _ : Unit, ∀ k, ι k) :
    blockWeight (fun _ : Unit => ∀ k, ι k) v = fun _ => 1 := by
  funext u
  simp [blockWeight]
omit [∀ k, Fintype (ι k)] in

theorem segreMap_isMultiHomog {m : ℕ} {p : MRing (fun _ : Unit => ∀ k, ι k) F}
    (hp : IsWeightedHomogeneous (blockWeight (fun _ : Unit => ∀ k, ι k)) p (fun _ => m)) :
    IsWeightedHomogeneous (blockWeight ι) (segreMap F p) (fun _ => m) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q _ _ hp hq => rw [map_add]; exact hp.add hq
  | monomial d r hr =>
    have hX : ∀ v : Σ _ : Unit, ∀ k, ι k,
        IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
      intro v
      have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
        (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, v.2 k⟩)
        (fun k _ => isWeightedHomogeneous_X _ _ _)
      convert h using 1
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have hsum : ∑ v ∈ d.support, d v = m := by
      have h := congrFun hr ()
      rw [Finsupp.weight_apply, Finsupp.sum] at h
      simpa [blockWeight_unit, Finset.sum_apply] using h
    have hdeg : (∑ v ∈ d.support, d v • (fun _ : K => 1) : K → ℕ) = fun _ => m := by
      funext k
      simp [Finset.sum_apply, hsum]
    unfold segreMap
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ r
    rw [← hdeg]
    exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hX v).pow _
omit [DecidableEq K] in

theorem monomial_mem_map_segreMap (m : ℕ) :
    ∀ e : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = m) →
      monomial e (1 : F) ∈ (weightedHomogeneousSubmodule F
        (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map (segreMap F).toLinearMap := by
  classical
  induction m with
  | zero =>
    intro e he
    have he0 : e = 0 := by
      ext ⟨k, i⟩
      exact (Finset.sum_eq_zero_iff.mp (he k)) i (Finset.mem_univ _)
    subst he0
    refine ⟨1, ?_, ?_⟩
    · exact isWeightedHomogeneous_one _ _
    · simp
  | succ m ih =>
    intro e he
    have hne : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => e ⟨k, i⟩) (by rw [he k]; omega)
      exact ⟨i, hi⟩
    choose f hf using hne
    set s : (Σ k, ι k) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun v => if v.2 = f v.1 then 1 else 0) with hs_def
    have hs : ∀ k i, s ⟨k, i⟩ = if i = f k then 1 else 0 := fun k i => by simp [hs_def]
    have hse : s ≤ e := by
      rw [Finsupp.le_def]
      rintro ⟨k, i⟩
      rw [hs]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (hf k)
      · exact Nat.zero_le _
    have hadd : e - s + s = e := tsub_add_cancel_of_le hse
    have he' : ∀ k, ∑ i, (e - s) ⟨k, i⟩ = m := fun k => by
      have h1 : ∑ i, (e - s) ⟨k, i⟩ + ∑ i, s ⟨k, i⟩ = m + 1 := by
        rw [← Finset.sum_add_distrib, ← he k]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.add_apply, hadd]
      have h2 : ∑ i, s ⟨k, i⟩ = 1 := by simp [hs]
      omega
    obtain ⟨g, hg, hge⟩ := ih (e - s) he'
    have hsX : monomial s (1 : F) = ∏ k, (X ⟨k, f k⟩ : MRing ι F) := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [hs]
    refine ⟨g * X ⟨(), f⟩, ?_, ?_⟩
    · have h := (show IsWeightedHomogeneous _ g _ from hg).mul
        (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ∀ k, ι k)) ⟨(), f⟩)
      rw [blockWeight_unit] at h
      exact h
    · simp only [AlgHom.toLinearMap_apply, map_mul] at hge ⊢
      rw [hge, segreMap_X, ← hsX, monomial_mul, one_mul, hadd]
theorem map_segreMap_weightedHomogeneousSubmodule (m : ℕ) :
    (weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map
        (segreMap F).toLinearMap =
      weightedHomogeneousSubmodule F (blockWeight ι) (fun _ => m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact segreMap_isMultiHomog F hp
  · intro p hp
    have hp' : IsWeightedHomogeneous (blockWeight ι) p (fun _ => m) := hp
    clear hp
    induction hp' using IsWeightedHomogeneous.induction_on with
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | monomial d r hr =>
      have hd : ∀ k, ∑ i, d ⟨k, i⟩ = m := fun k => by
        rw [← weight_blockWeight_apply, hr]
      have h := Submodule.smul_mem _ r (monomial_mem_map_segreMap F m d hd)
      rwa [smul_monomial, smul_eq_mul, mul_one] at h
def segreQuotMap (q : Ideal (MRing ι F)) :
    MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q →ₐ[F] MRing ι F ⧸ q :=
  Ideal.quotientMapₐ (I := segrePrime F q) q (segreMap F) fun _ h => h
omit [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem segreQuotMap_injective (q : Ideal (MRing ι F)) : Function.Injective (segreQuotMap F q) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk q (segreMap F x) = 0 at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp ha))
def segreGradedPieceEquiv (q : Ideal (MRing ι F)) (m : ℕ) :
    gradedPiece (segrePrime F q) (fun _ : Unit => m) ≃ₗ[F] gradedPiece q (fun _ : K => m) :=
  have hinj : Function.Injective (segreQuotMap F q).toLinearMap := segreQuotMap_injective F q
  have hmap : (gradedPiece (segrePrime F q) (fun _ : Unit => m)).map (segreQuotMap F q).toLinearMap =
      gradedPiece q (fun _ : K => m) := by
    have hc : (segreQuotMap F q).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (segrePrime F q)).toLinearMap =
        (Ideal.Quotient.mkₐ F q).toLinearMap ∘ₗ (segreMap F).toLinearMap :=
      LinearMap.ext fun _ => rfl
    unfold gradedPiece
    rw [← Submodule.map_comp, hc, Submodule.map_comp, map_segreMap_weightedHomogeneousSubmodule]
  (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ hmap)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


