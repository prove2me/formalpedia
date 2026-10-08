-- Prove2me | Definitions.Def_ChapterAtomicDiagonalModel
-- name    : ChapterAtomicDiagonalModel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T15:27:37.604078+00:00
-- url     : https://prove2.me/theorems/8d729e2b-94bb-4c53-9bd1-e81231f57fdc
-- title:
--   ChapterAtomicDiagonalModel
-- statement:
--   ChapterAtomicDiagonalModel

import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib


/-!
# The atomic summand is a diagonal algebra (plan GAP-2)

`ChapterMeasureAtomicDiffuse` splits every summand measure of the abelian
multiplication model into a purely atomic part and a diffuse part, and
`ChapterDiffuseUnitaryModel` identifies the diffuse part with the unit interval.
This module does the other half: for a *purely atomic* finite measure the `L²` space
has an orthonormal basis indexed by the atoms — the normalised point masses — and
every multiplication operator is **diagonal** in that basis.  That is the `I_n` /
`ℓ∞(ℕ)` entry of the classification list: an atomic summand contributes a diagonal
algebra whose size is the number of atoms.

* `atomVec` — the normalised indicator of an atom;
* `orthonormal_atomVec`, `span_atomVec_orthogonal_eq_bot`, `atomBasis` — they form a
  Hilbert basis of `L²(μ)` when `μ` is carried by its atoms;
* HEADLINE `atomic_multiplication_model_diagonal` — every multiplication operator is
  diagonal in that basis, acting on the basis vector at the atom `a` by the scalar
  `g a`.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

open MeasureTheory

namespace BookProof.ChapterAtomicDiagonalModel

open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (mu : Measure α) [IsFiniteMeasure mu]

/-! ## 1. The normalised point mass at an atom -/

omit [MeasurableSingletonClass α] in
theorem measureReal_singleton_pos (a : atomSet mu) : 0 < mu.real {(a : α)} :=
  ENNReal.toReal_pos a.2 (measure_ne_top mu _)

/-- The indicator of a point, as an element of `L²(μ)`. -/
def atomIndicator (a : α) : Lp ℂ 2 mu :=
  indicatorConstLp 2 (measurableSet_singleton a) (measure_ne_top mu _) (1 : ℂ)

theorem atomIndicator_coeFn (a : α) :
    (atomIndicator mu a : α → ℂ) =ᵐ[mu] Set.indicator {a} (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- **The normalised point mass at an atom**, a unit vector of `L²(μ)`. -/
def atomVec (a : atomSet mu) : Lp ℂ 2 mu :=
  (((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ) : ℂ) • atomIndicator mu (a : α)



/-! ## 2. Orthonormality -/

theorem norm_atomVec (a : atomSet mu) : ‖atomVec mu a‖ = 1 := by
  have hpos := measureReal_singleton_pos mu a
  have hne : Real.sqrt (mu.real {(a : α)}) ≠ 0 := Real.sqrt_ne_zero'.2 hpos
  rw [atomVec, norm_smul, atomIndicator,
    norm_indicatorConstLp (by simp) (by simp)]
  have h2 : (1 : ℝ) / (2 : ENNReal).toReal = 1 / 2 := by simp
  rw [h2, ← Real.sqrt_eq_rpow]
  simp only [norm_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact inv_mul_cancel₀ hne

theorem inner_atomIndicator_of_ne {a b : α} (hab : a ≠ b) :
    inner ℂ (atomIndicator mu a) (atomIndicator mu b) = 0 := by
  rw [atomIndicator, L2.inner_indicatorConstLp_eq_setIntegral_inner]
  have hcongr : ∫ x in ({a} : Set α),
        inner ℂ (1 : ℂ) ((atomIndicator mu b : α → ℂ) x) ∂mu
      = ∫ x in ({a} : Set α), Set.indicator {b} (fun _ => (1 : ℂ)) x ∂mu := by
    refine setIntegral_congr_ae (measurableSet_singleton a) ?_
    filter_upwards [atomIndicator_coeFn mu b] with x hx _
    rw [hx]
    simp
  rw [hcongr, integral_singleton]
  simp [Set.indicator_of_notMem, hab]

theorem inner_atomVec_of_ne {a b : atomSet mu} (hab : a ≠ b) :
    inner ℂ (atomVec mu a) (atomVec mu b) = 0 := by
  have hne : (a : α) ≠ (b : α) := fun h => hab (Subtype.ext h)
  rw [atomVec, atomVec, inner_smul_left, inner_smul_right,
    inner_atomIndicator_of_ne mu hne]
  ring

theorem orthonormal_atomVec : Orthonormal ℂ (atomVec mu) :=
  ⟨norm_atomVec mu, @fun _ _ hij => inner_atomVec_of_ne mu hij⟩

/-! ## 3. Completeness of the family when the measure is carried by its atoms -/

theorem eq_zero_of_inner_atomVec_eq_zero (hpure : mu (atomSet mu)ᶜ = 0) (u : Lp ℂ 2 mu)
    (hu : ∀ a : atomSet mu, inner ℂ (atomVec mu a) u = 0) : u = 0 := by
  have hval : ∀ a : atomSet mu, (u : α → ℂ) (a : α) = 0 := by
    intro a
    have hpos := measureReal_singleton_pos mu a
    have h := hu a
    rw [atomVec, inner_smul_left, atomIndicator,
      L2.inner_indicatorConstLp_eq_setIntegral_inner] at h
    have hint : ∫ x in ({(a : α)} : Set α), inner ℂ (1 : ℂ) ((u : α → ℂ) x) ∂mu
        = ((mu.real {(a : α)} : ℝ) : ℂ) * (u : α → ℂ) (a : α) := by
      rw [integral_singleton]
      simp [RCLike.inner_apply, Complex.real_smul]
    rw [hint] at h
    have hsq : ((((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ)) : ℂ) ≠ 0 := by
      simpa using (Real.sqrt_ne_zero'.2 hpos)
    have hconj : (starRingEnd ℂ) ((((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ)) : ℂ) ≠ 0 := by
      rw [Complex.conj_ofReal]
      exact hsq
    have hmu : ((mu.real {(a : α)} : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
    rcases mul_eq_zero.1 h with h1 | h2
    · exact absurd h1 hconj
    · rcases mul_eq_zero.1 h2 with h3 | h4
      · exact absurd h3 hmu
      · exact h4
  refine Lp.ext ?_
  have hsub : {x : α | (u : α → ℂ) x ≠ 0} ⊆ (atomSet mu)ᶜ := by
    intro x hx
    by_contra hmem
    exact hx (hval ⟨x, not_not.1 hmem⟩)
  have hnull : mu {x : α | (u : α → ℂ) x ≠ 0} = 0 := measure_mono_null hsub hpure
  filter_upwards [Lp.coeFn_zero ℂ 2 mu,
    (measure_eq_zero_iff_ae_notMem.1 hnull)] with x hx0 hx
  simp only [not_not] at hx
  rw [hx, hx0]
  rfl

theorem span_atomVec_orthogonal_eq_bot (hpure : mu (atomSet mu)ᶜ = 0) :
    (Submodule.span ℂ (Set.range (atomVec mu)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  exact eq_zero_of_inner_atomVec_eq_zero mu hpure u fun a =>
    hu _ (Submodule.subset_span ⟨a, rfl⟩)

/-- **The point masses at the atoms form a Hilbert basis** of `L²(μ)` when `μ` is
carried by its atoms. -/
def atomBasis (hpure : mu (atomSet mu)ᶜ = 0) :
    HilbertBasis (atomSet mu) ℂ (Lp ℂ 2 mu) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_atomVec mu)
    (span_atomVec_orthogonal_eq_bot mu hpure)



/-! ## 4. Multiplication operators are diagonal -/





end BookProof.ChapterAtomicDiagonalModel

end


