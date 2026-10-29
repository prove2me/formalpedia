-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:17.362089+00:00
-- url     : https://prove2.me/theorems/f5c15ed1-4df8-4e6b-a9fd-70f895a85f15
-- title:
--   LIDT definitions: LDT / Preliminaries / Polynomials
-- statement:
--   This bundle defines the low-individual-degree polynomial model and its agreement estimates. It introduces the polynomial class, individual and total degree bounds, uniform agreement probability, and the two Schwartz-Zippel consequences used throughout the LDT error analysis.
--
--   Principal definitions:
--   - `polyFunc`: the class of polynomials with individual degree at most `d` in `m` variables over the coded field.
--   - `degreeOf_le_of_mem_polyFunc`: bounds every individual degree of a member of `polyFunc`.
--   - `polynomialAgreementProbability`: the uniform probability that two polynomials agree on a point.
--   - `totalDegree_le_mul_of_degreeOf_le`: bounds total degree by `m` times the individual-degree bound.
--   - `schwartzZippel_totalDegree`: gives the agreement bound for two bounded-total-degree polynomials.
--   - `schwartzZippel_individualDegree`: gives the agreement bound for the low-individual-degree class.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/Polynomials.lean#L29-L123

-- Generated from MIPStarRE/LDT/Preliminaries/Polynomials.lean by skeleton subtraction.
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

/-!
# Polynomial preliminaries

Packages the paper's low-individual-degree polynomial class together
with Schwartz-Zippel bounds as thin wrappers around Mathlib's existing
multivariate polynomial theorems.

## References

* `references/ldt-paper/preliminaries.tex`, Section 3 (Preliminaries)
-/

@[expose] public section

open Finset Fintype

open scoped BigOperators

namespace MIPStarRE.LDT.Preliminaries

open MvPolynomial

/-- `\polyfunc{m}{q}{d}` from the paper's definition of low-individual-degree
polynomials. This is Mathlib's `MvPolynomial.restrictDegree` submodule. -/
noncomputable abbrev polyFunc (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.restrictDegree (Fin m) K d

/-- If `p ∈ polyFunc m K d`, then `p.degreeOf i ≤ d` for every variable `i`. -/
theorem degreeOf_le_of_mem_polyFunc {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (hp : p ∈ polyFunc m K d) (i : Fin m) :
    p.degreeOf i ≤ d :=
  MvPolynomial.degreeOf_le_iff.mpr fun s hs =>
    (MvPolynomial.mem_restrictDegree (σ := Fin m) (R := K) p d).mp hp s hs i



/-- The uniform agreement probability of two polynomials on `K^m`, written as a
finite cardinality ratio over `K^m`. -/
noncomputable def polynomialAgreementProbability (m : ℕ) (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] (g h : MvPolynomial (Fin m) K) : ℚ≥0 :=
  #{x ∈ (Finset.univ : Finset (Fin m → K)) |
      MvPolynomial.eval x g = MvPolynomial.eval x h} /
    (Fintype.card K ^ m : ℚ≥0)

/-- If every individual degree of `p` is at most `d`, then the total degree of
`p` is at most `m * d`. -/
theorem totalDegree_le_mul_of_degreeOf_le {m d : ℕ} {K : Type*} [CommSemiring K]
    {p : MvPolynomial (Fin m) K} (hdeg : ∀ i, p.degreeOf i ≤ d) :
    p.totalDegree ≤ m * d := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le ?_
  intro s hs
  calc
    s.sum (fun _ e => e) = ∑ i : Fin m, s i := by
      rw [Finsupp.sum_fintype]
      intro i
      rfl
    _ ≤ ∑ _i : Fin m, d := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact (MvPolynomial.degreeOf_le_iff.mp (hdeg i)) s hs
    _ = m * d := by
      simp [Fintype.card_fin]

/-- If two polynomials on `K^m` have total degree at most `d`, then the uniform
agreement probability is at most `d / |K|`. -/
theorem schwartzZippel_totalDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {g h : MvPolynomial (Fin m) K} (hneq : g ≠ h)
    (hg : g.totalDegree ≤ d) (hh : h.totalDegree ≤ d) :
    polynomialAgreementProbability m K g h ≤ d / Fintype.card K := by
  have hsub_ne : g - h ≠ 0 := sub_ne_zero.mpr hneq
  have hsub_deg : (g - h).totalDegree ≤ d :=
    (MvPolynomial.totalDegree_sub g h).trans (max_le hg hh)
  unfold polynomialAgreementProbability
  rw [show {x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x g = MvPolynomial.eval x h} =
      {x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x (g - h) = 0} by
        ext x
        simp [MvPolynomial.eval_sub, sub_eq_zero]]
  calc
    #{x ∈ (Finset.univ : Finset (Fin m → K)) |
        MvPolynomial.eval x (g - h) = 0} /
        (Fintype.card K ^ m : ℚ≥0)
      ≤ (g - h).totalDegree / Fintype.card K := by
          simpa using
            (MvPolynomial.schwartz_zippel_totalDegree
              (n := m) (p := g - h) hsub_ne (Finset.univ : Finset K))
    _ ≤ d / Fintype.card K := by
          gcongr

/-- Schwartz-Zippel for the paper's low-individual-degree class
`\polyfunc{m}{q}{d}`. -/
theorem schwartzZippel_individualDegree {m d : ℕ} {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (g h : polyFunc m K d) (hneq : g ≠ h) :
    polynomialAgreementProbability m K g.1 h.1 ≤ ((m * d : ℕ) : ℚ≥0) / Fintype.card K := by
  have hval_ne : g.1 ≠ h.1 := by
    intro hgh
    apply hneq
    exact Subtype.ext hgh
  have hg_degOf : ∀ i, g.1.degreeOf i ≤ d :=
    degreeOf_le_of_mem_polyFunc g.property
  have hh_degOf : ∀ i, h.1.degreeOf i ≤ d :=
    degreeOf_le_of_mem_polyFunc h.property
  exact schwartzZippel_totalDegree (g := g.1) (h := h.1) hval_ne
    (totalDegree_le_mul_of_degreeOf_le hg_degOf)
    (totalDegree_le_mul_of_degreeOf_le hh_degOf)

end MIPStarRE.LDT.Preliminaries

end

end LIDT


