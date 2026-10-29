-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
-- name    : LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:51:47.621981+00:00
-- url     : https://prove2.me/theorems/15b420dd-07aa-4470-b9ce-e7aac8605768
-- title:
--   LIDT definitions: LDT / Basic / ParametersFiniteAnswers
-- statement:
--   This bundle supplies finite-answer facts used when counting polynomial answers and regrouping polynomial-indexed sums. It gives coefficient uniqueness for bounded-degree univariate polynomials and a fiberwise reindexing principle for evaluation at a fixed point.
--
--   Principal definitions:
--   - `linePolynomial_coeff_fin_injective`: a univariate polynomial of degree at most `n` is determined by its first `n + 1` coefficients.
--   - `polynomial_sum_fiberwise`: reindexes a sum over polynomials by their value at a selected point.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean#L20-L100

-- Generated from MIPStarRE/LDT/Basic/ParametersFiniteAnswers.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Mathlib

namespace LIDT

/-!
# Finite answer spaces for the low individual degree test

Finite-type instances for the bounded polynomial answer spaces defined in
`MIPStarRE.LDT.Basic.LowDegreePolynomial`.
-/

@[expose] public section

namespace MIPStarRE.LDT

open scoped BigOperators

/-! ### Finite answer spaces -/

/-- The axis-line polynomial answer type uses classical equality on the bundled
polynomial witness. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    DecidableEq (AxisLinePolynomial params) :=
  Classical.decEq _

/-- The finite low-individual-degree polynomial answer type uses classical
equality on the bundled polynomial witness. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    DecidableEq (Polynomial params) :=
  Classical.decEq _

/-- A univariate polynomial of `natDegree ≤ n` is determined by its first
`n + 1` coefficients.  Shared injectivity fact behind the finite-answer-space
instances below. -/
theorem linePolynomial_coeff_fin_injective (params : Parameters) [FieldModel params.q]
    {n : ℕ} {p q : LinePolynomialModel params}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ i : Fin (n + 1), p.coeff i = q.coeff i) : p = q := by
  ext k
  by_cases hk : k < n + 1
  · exact h ⟨k, hk⟩
  · rw [p.coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega)),
      q.coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega))]

/-- Axis-line polynomial answers form a finite type via their bounded coefficient vectors. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (AxisLinePolynomial params) := by
  classical
  exact Fintype.ofInjective
    (fun f : AxisLinePolynomial params => fun i : Fin (params.d + 1) => f.poly.coeff i)
    fun f g h => AxisLinePolynomial.ext
      (linePolynomial_coeff_fin_injective params f.degreeBounded g.degreeBounded
        fun i => congrFun h i)

/-- Diagonal-line polynomial answers form a finite type via their bounded coefficient vectors. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (DiagonalLinePolynomial params) := by
  classical
  exact Fintype.ofInjective
    (fun f : DiagonalLinePolynomial params =>
      fun i : Fin (params.m * params.d + 1) => f.poly.coeff i)
    fun f g h => DiagonalLinePolynomial.ext
      (linePolynomial_coeff_fin_injective params f.degreeBounded g.degreeBounded
        fun i => congrFun h i)

/-- Global low-individual-degree polynomial answers form a finite type, by
injecting into the finite space of degree-restricted multivariate polynomials. -/
noncomputable instance (params : Parameters) [FieldModel params.q] :
    Fintype (Polynomial params) := by
  classical
  letI : Finite (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Module.finite_of_finite (Scalar params)
  letI : Fintype (MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d) :=
    Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun g : Polynomial params =>
      (⟨g.poly, by
          rw [MvPolynomial.mem_restrictDegree_iff_sup]
          simpa [MvPolynomial.degreeOf_def] using g.lowIndividualDegree⟩ :
        MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d))
    fun g g' h => by
      cases g; cases g'
      simpa using congrArg Subtype.val h

/-- Reindex a polynomial-indexed sum by the value of the polynomial at a fixed point.

The low individual degree test frequently groups global polynomial answers by
the fiber of the evaluation map `h ↦ h u`.  This lemma records that finite
reindexing in the notation used throughout the LDT formalization. -/
theorem polynomial_sum_fiberwise
    (params : Parameters)
    [FieldModel params.q]
    (u : Point params)
    {β : Type*} [AddCommMonoid β]
    (f : Polynomial params → β) :
    (∑ h : Polynomial params, f h) =
      ∑ a : Fq params,
        ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a), f h := by
  classical
  simpa using (Finset.sum_fiberwise Finset.univ (fun h : Polynomial params => h u) f).symm

end MIPStarRE.LDT

end

end LIDT


