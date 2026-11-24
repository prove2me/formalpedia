-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCompletionEquiv
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCompletionEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:07.217701+00:00
-- url     : https://prove2.me/theorems/113fa5c5-049f-41a0-b204-9b484bcfca61
-- title:
--   PGerm Completion Equiv
-- statement:
--   Definitions and structural lemmas for PGerm Completion Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermCompletionEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermCompletionEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_holGermValue_polyGerm_02f2c54c1f02

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
namespace GermCompletionEquiv
theorem factorPow_evalₐ {R : Type} [CommRing R] (J : Ideal R) {k l : ℕ} (h : k ≤ l) (x : AdicCompletion J R) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J l x) = AdicCompletion.evalₐ J k x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk J h]
variable {σ : Type} [Fintype σ] (w : σ → ℂ)
theorem sub_polyGerm_C_mem (f : holGerms w) :
    f - polyGerm w (C (holGermValue w f)) ∈ holGermPointIdeal w := by
  rw [holGermPointIdeal, RingHom.mem_ker, map_sub, holGermValue_polyGerm, eval_C, sub_self]
theorem exists_sub_polyGerm_mem (hH : HolGermPointIdealSpan.Statement) (k : ℕ) (f : holGerms w) :
    ∃ q : MvPolynomial σ ℂ, f - polyGerm w q ∈ holGermPointIdeal w ^ k := by
  induction k generalizing f with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih f
    have hkey : holGermPointIdeal w ^ k =
        Ideal.span (polyGerm w '' ↑(Ideal.span (Set.range fun i : σ => (X i - C (w i) : MvPolynomial σ ℂ)) ^ k)) := by
      have e : Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i))) =
          (Ideal.span (Set.range fun i : σ => (X i - C (w i) : MvPolynomial σ ℂ))).map (polyGerm w) := by
        rw [Ideal.map_span, ← Set.range_comp]; rfl
      rw [hH σ w, e, ← Ideal.map_pow]; rfl
    have step : ∀ g ∈ holGermPointIdeal w ^ k,
        ∃ q' : MvPolynomial σ ℂ, g - polyGerm w q' ∈ holGermPointIdeal w ^ (k + 1) := by
      intro g hg
      rw [hkey] at hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨p, -, rfl⟩ := hx
        exact ⟨p, by simp⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ h1 h2 =>
        obtain ⟨q1, h1⟩ := h1
        obtain ⟨q2, h2⟩ := h2
        refine ⟨q1 + q2, ?_⟩
        rw [map_add]
        convert add_mem h1 h2 using 1
        ring
      | smul a x hx h =>
        obtain ⟨q1, h1⟩ := h
        have hx' : x ∈ holGermPointIdeal w ^ k := hkey ▸ hx
        refine ⟨C (holGermValue w a) * q1, ?_⟩
        have e : a • x - polyGerm w (C (holGermValue w a) * q1) =
            polyGerm w (C (holGermValue w a)) * (x - polyGerm w q1) +
              (a - polyGerm w (C (holGermValue w a))) * x := by
          rw [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ h1) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (sub_polyGerm_C_mem w a) hx'
    obtain ⟨q', hq'⟩ := step _ hq
    exact ⟨q + q', by rw [map_add, ← sub_sub]; exact hq'⟩
variable (I : Ideal (MvPolynomial σ ℂ))
theorem exists_sub_polyGerm_mem_of_mem_map (hH : HolGermPointIdealSpan.Statement) (k : ℕ) {x : holGerms w}
    (hx : x ∈ I.map (polyGerm w)) :
    ∃ i ∈ I, x - polyGerm w i ∈ holGermPointIdeal w ^ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, by simp⟩
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨i1, hi1, h1⟩ := h1
    obtain ⟨i2, hi2, h2⟩ := h2
    refine ⟨i1 + i2, I.add_mem hi1 hi2, ?_⟩
    rw [map_add]
    convert add_mem h1 h2 using 1
    ring
  | smul a x _ h =>
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨q0, hq0⟩ := exists_sub_polyGerm_mem w hH k a
    refine ⟨q0 * i, I.mul_mem_left _ hi, ?_⟩
    have e : a • x - polyGerm w (q0 * i) =
        (a - polyGerm w q0) * x + polyGerm w q0 * (x - polyGerm w i) := by
      rw [smul_eq_mul, map_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hq0) (Ideal.mul_mem_left _ _ h)
def phi : MvPolynomial σ ℂ ⧸ I →+* holGerms w ⧸ I.map (polyGerm w) :=
  Ideal.quotientMap _ (polyGerm w) Ideal.le_comap_map
theorem phi_mk (q : MvPolynomial σ ℂ) :
    phi w I (Ideal.Quotient.mk I q) = Ideal.Quotient.mk _ (polyGerm w q) :=
  Ideal.quotientMap_mk
theorem pow_le_comap (k : ℕ) :
    polyPointIdeal I w ^ k ≤ (germQuotPointIdeal I w ^ k).comap (phi w I) := by
  refine (Ideal.pow_right_mono ?_ k).trans (Ideal.le_comap_pow _ k)
  rw [polyPointIdeal, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro q hq
  rw [Ideal.mem_comap, RingHom.comp_apply, phi_mk, germQuotPointIdeal]
  exact Ideal.mem_map_of_mem _ (by rw [holGermPointIdeal, RingHom.mem_ker, holGermValue_polyGerm]; exact hq)
def psi (k : ℕ) : (MvPolynomial σ ℂ ⧸ I) ⧸ polyPointIdeal I w ^ k →+*
    (holGerms w ⧸ I.map (polyGerm w)) ⧸ germQuotPointIdeal I w ^ k :=
  Ideal.quotientMap _ (phi w I) (pow_le_comap w I k)
theorem psi_mk (k : ℕ) (q : MvPolynomial σ ℂ) :
    psi w I k (Ideal.Quotient.mk _ (Ideal.Quotient.mk I q)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (polyGerm w q)) := by
  rw [psi, Ideal.quotientMap_mk, phi_mk]
theorem psi_surjective (hH : HolGermPointIdealSpan.Statement) (k : ℕ) : Function.Surjective (psi w I k) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨q, hq⟩ := exists_sub_polyGerm_mem w hH k f
  refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk I q), ?_⟩
  rw [psi_mk, Ideal.Quotient.eq, germQuotPointIdeal, ← Ideal.map_pow, ← map_sub]
  exact Ideal.mem_map_of_mem _ (by rw [← neg_sub]; exact neg_mem hq)
theorem psi_injective (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) (k : ℕ) :
    Function.Injective (psi w I k) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [psi_mk, Ideal.Quotient.eq_zero_iff_mem, germQuotPointIdeal, ← Ideal.map_pow,
    Ideal.mem_quotient_iff_mem_sup, Submodule.mem_sup] at hy
  obtain ⟨μ, hμ, ι, hι, he⟩ := hy
  obtain ⟨i, hi, hi'⟩ := exists_sub_polyGerm_mem_of_mem_map w I hH k hι
  have hqi : polyGerm w (q - i) ∈ holGermPointIdeal w ^ k := by
    rw [map_sub, ← he]
    convert add_mem hμ hi' using 1
    ring
  have hq := hP σ w k (q - i) hqi
  have e : q = (q - i) + i := by ring
  rw [Ideal.Quotient.eq_zero_iff_mem, polyPointIdeal, ← Ideal.map_pow, e, map_add,
    Ideal.Quotient.eq_zero_iff_mem.2 hi, add_zero]
  exact Ideal.mem_map_of_mem _ hq
theorem psi_factorPow {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h).comp (psi w I l) =
      (psi w I k).comp (Ideal.Quotient.factorPow (polyPointIdeal I w) h) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [RingHom.comp_apply, psi_mk, Ideal.Quotient.factor_mk]
def psiEquiv (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement) (k : ℕ) :
    (MvPolynomial σ ℂ ⧸ I) ⧸ polyPointIdeal I w ^ k ≃+*
      (holGerms w ⧸ I.map (polyGerm w)) ⧸ germQuotPointIdeal I w ^ k :=
  RingEquiv.ofBijective (psi w I k) ⟨psi_injective w I hH hP k, psi_surjective w I hH k⟩
variable (hH : HolGermPointIdealSpan.Statement) (hP : PolyGermPointPow.Statement)
theorem toCompl_compat {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h).comp
        ((psi w I l).comp (AdicCompletion.evalₐ (polyPointIdeal I w) l).toRingHom) =
      (psi w I k).comp (AdicCompletion.evalₐ (polyPointIdeal I w) k).toRingHom := by
  refine RingHom.ext fun x => ?_
  change Ideal.Quotient.factorPow (germQuotPointIdeal I w) h
      (psi w I l (AdicCompletion.evalₐ (polyPointIdeal I w) l x)) =
    psi w I k (AdicCompletion.evalₐ (polyPointIdeal I w) k x)
  rw [← RingHom.comp_apply (Ideal.Quotient.factorPow (germQuotPointIdeal I w) h), psi_factorPow,
    RingHom.comp_apply, factorPow_evalₐ]
def toCompl : AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) →+*
    AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) :=
  AdicCompletion.liftRingHom (germQuotPointIdeal I w)
    (fun k => (psi w I k).comp (AdicCompletion.evalₐ (polyPointIdeal I w) k).toRingHom)
    (fun h => toCompl_compat w I h)
theorem fromCompl_compat {k l : ℕ} (h : k ≤ l)
    (x : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :
    Ideal.Quotient.factorPow (polyPointIdeal I w) h
        ((psiEquiv w I hH hP l).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) l x)) =
      (psiEquiv w I hH hP k).symm (AdicCompletion.evalₐ (germQuotPointIdeal I w) k x) := by
  apply (psiEquiv w I hH hP k).injective
  rw [RingEquiv.apply_symm_apply]
  change psi w I k _ = _
  rw [← RingHom.comp_apply (psi w I k), ← psi_factorPow w I h, RingHom.comp_apply]
  change Ideal.Quotient.factorPow (germQuotPointIdeal I w) h
    ((psiEquiv w I hH hP l) ((psiEquiv w I hH hP l).symm _)) = _
  rw [RingEquiv.apply_symm_apply, factorPow_evalₐ]
def fromCompl : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) →+*
    AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) :=
  AdicCompletion.liftRingHom (polyPointIdeal I w)
    (fun k => (psiEquiv w I hH hP k).symm.toRingHom.comp
      (AdicCompletion.evalₐ (germQuotPointIdeal I w) k).toRingHom)
    (fun h => RingHom.ext fun x => fromCompl_compat w I hH hP h x)
end GermCompletionEquiv
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


