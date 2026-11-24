-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ArtinHenselCompletionNoetherian
-- name    : GroundTheory_ArithmeticGeometry_EtaleCompletion_ArtinHenselCompletionNoetherian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:23.633318+00:00
-- url     : https://prove2.me/theorems/987ee212-1070-4ca2-be19-74d7d382476d
-- title:
--   Artin Hensel Completion Noetherian
-- statement:
--   Definitions and structural lemmas for Artin Hensel Completion Noetherian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ArtinHenselCompletionNoetherian.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ArtinApproximationData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Etale
open IsLocalRing
theorem isNoetherianRing_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  classical
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).1 inferInstance I
  set k := s.card
  let a : Fin k → R := fun i ↦ (s.equivFin.symm i : R)
  have ha : Set.range a = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hr
      exact ⟨s.equivFin ⟨r, hr⟩, by simp [a]⟩
  let P := MvPolynomial (Fin k) R
  let σ : P →+* R := MvPolynomial.eval a
  let J := MvPolynomial.idealOfVars (Fin k) R
  have hσX : ∀ i, σ (MvPolynomial.X i) = a i := fun i ↦ MvPolynomial.eval_X i
  have hJ : J.map σ = I := by
    show Ideal.map σ (Ideal.span (Set.range MvPolynomial.X)) = I
    rw [Ideal.map_span, ← hs, ← ha, ← Set.range_comp]
    congr 1
    ext i
    simp [hσX]
  have hJn : ∀ n, (J ^ n).map σ = I ^ n := fun n ↦ by rw [Ideal.map_pow, hJ]
  have hσs : Function.Surjective σ := fun r ↦ ⟨MvPolynomial.C r, MvPolynomial.eval_C _⟩
  have hle : ∀ n, J ^ n ≤ (I ^ n).comap σ := fun n ↦ by
    rw [← Ideal.map_le_iff_le_comap, hJn]
  let g : (n : ℕ) → AdicCompletion J P →+* R ⧸ I ^ n := fun n ↦
    (Ideal.quotientMap (I ^ n) σ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n), (Ideal.Quotient.factorPow I hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    have hq' : AdicCompletion.evalₐ J m x = Ideal.Quotient.mk _ q := by
      obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective J P x
      rw [AdicCompletion.evalₐ_mk] at hq ⊢
      have h1 := f.property hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
      have h2 : f.val n - q ∈ J ^ m := Ideal.pow_le_pow_right hmn (Ideal.Quotient.eq.1 hq.symm)
      rw [Ideal.Quotient.eq]
      have := Ideal.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at this
    simp only [g, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, ← hq, hq', Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
  let ψ := AdicCompletion.liftRingHom I g hg
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I R x
    have hd : ∀ j, f.val (j + 1) - f.val j ∈ (J ^ j).map σ := by
      intro j
      have h1 := f.property (Nat.le_succ j)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
      rw [hJn, ← neg_mem_iff, neg_sub]
      exact h1
    choose Pj hPj hσP using fun j ↦ (Ideal.mem_map_iff_of_surjective σ hσs).1 (hd j)
    let Q : ℕ → P := fun n ↦ MvPolynomial.C (f.val 0) + ∑ j ∈ Finset.range n, Pj j
    have hQ : AdicCompletion.IsAdicCauchy J P Q := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      have : Q n - Q m = ∑ j ∈ Finset.Ico m n, Pj j := by
        simp only [Q, add_sub_add_left_eq_sub]
        rw [Finset.sum_Ico_eq_sub _ hmn]
      rw [this]
      exact Ideal.sum_mem _ fun j hj ↦
        Ideal.pow_le_pow_right (Finset.mem_Ico.1 hj).1 (hPj j)
    let Qc : AdicCompletion.AdicCauchySequence J P := ⟨Q, hQ⟩
    refine ⟨AdicCompletion.mk J P Qc, AdicCompletion.ext_evalₐ fun n ↦ ?_⟩
    rw [AdicCompletion.evalₐ_liftRingHom, AdicCompletion.evalₐ_mk]
    change Ideal.quotientMap (I ^ n) σ (hle n)
      (AdicCompletion.evalₐ J n (AdicCompletion.mk J P Qc)) = _
    rw [AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    refine congrArg _ ?_
    change σ (Q n) = f.val n
    simp only [Q, map_add, map_sum, hσP]
    rw [show σ (MvPolynomial.C (f.val 0)) = f.val 0 from MvPolynomial.eval_C _]
    rw [Finset.sum_range_sub (fun j ↦ f.val j) n]
    ring
  have : IsNoetherianRing (AdicCompletion J P) :=
    isNoetherianRing_of_ringEquiv _ (MvPowerSeries.toAdicCompletionAlgEquiv (Fin k) R).toRingEquiv
  exact isNoetherianRing_of_surjective _ _ ψ hψ
instance instIsNoetherianRingAdicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) :=
  isNoetherianRing_adicCompletion R I
end GroundTheory.Arith.Etale


