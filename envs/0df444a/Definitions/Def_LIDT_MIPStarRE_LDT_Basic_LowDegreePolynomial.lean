-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
-- name    : LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:49:47.724211+00:00
-- url     : https://prove2.me/theorems/3e8c429f-adda-4fd7-9698-9d00cf6eb1de
-- title:
--   LIDT definitions: LDT / Basic / LowDegreePolynomial
-- statement:
--   This bundle defines the low-individual-degree polynomial model over the coded field and its basic restriction operations. It supports evaluation, constants, extension to a higher-dimensional slice, restriction to a fixed height, and restriction to an axis-parallel affine line.
--
--   Principal definitions:
--   - `Polynomial`: the multivariate polynomial type with the LDT individual-degree bound.
--   - `toFun`: evaluates a stored polynomial at a coded point.
--   - `const`: the constant polynomial with a chosen field value.
--   - `appendAtHeight`: extends a polynomial while ignoring a new coordinate.
--   - `restrictAtHeightCoordinateMap`: the coordinate map for height restriction.
--   - `restrictAtHeight`: restricts a polynomial to a fixed-height slice.
--   - `axisCoordinatePolynomial`: the coordinate polynomial for an axis-parallel line.
--   - `restrictToAxisParallelLine`: restricts a polynomial to an axis-parallel line.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/LowDegreePolynomial.lean#L21-L407

-- Generated from MIPStarRE/LDT/Basic/LowDegreePolynomial.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Mathlib

namespace LIDT

/-!
# Low-individual-degree polynomials for the low individual degree test

Multivariate low-degree polynomial objects and their restrictions.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

namespace MIPStarRE.LDT

/-- Global low-individual-degree polynomial outcomes. -/
structure Polynomial (params : Parameters) [FieldModel params.q] where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d

/-- Renaming a polynomial along the old-coordinate inclusion does not introduce
the appended last coordinate. -/
theorem degreeOf_rename_embedCoord_lastCoord (params : Parameters) [FieldModel params.q]
    (p : PolynomialModel params) :
    MvPolynomial.degreeOf (lastCoord params)
      (MvPolynomial.rename (embedCoord params) p : PolynomialModel params.next) = 0 := by
  change MvPolynomial.degreeOf (lastCoord params)
    (MvPolynomial.rename (embedCoord params) p :
      MvPolynomial (Fin params.next.m) (Scalar params)) = 0
  rw [MvPolynomial.degreeOf, MvPolynomial.degrees_rename_of_injective
    (R := Scalar params) (embedCoord_injective params)]
  simp only [Multiset.count_eq_zero, Multiset.mem_map]
  rintro ⟨b, _, hb⟩
  exact embedCoord_ne_lastCoord params b hb

namespace Polynomial

/-- Evaluation of the stored multivariate polynomial on a coded point. -/
noncomputable def toFun {params : Parameters} [FieldModel params.q] (g : Polynomial params) :
    Point params → Fq params :=
  evalPolynomialModel params g.poly

noncomputable instance {params : Parameters} [FieldModel params.q] :
    CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=
  ⟨Polynomial.toFun⟩



/-- The constant polynomial with value `a`. -/
noncomputable def const (params : Parameters) [FieldModel params.q] (a : Fq params) :
    Polynomial params where
  poly := MvPolynomial.C (decodeScalar a)
  lowIndividualDegree := fun i => (MvPolynomial.degreeOf_C _ i).trans_le (Nat.zero_le _)

noncomputable instance {params : Parameters} [FieldModel params.q] :
    Inhabited (Polynomial params) :=
  ⟨const params default⟩

/-- The constant polynomial evaluates to its prescribed value. -/
@[simp] theorem const_apply (params : Parameters) [FieldModel params.q]
    (a : Fq params) (u : Point params) :
    const params a u = a := by
  simp [const, Polynomial.toFun, evalPolynomialModel]







/-- Renaming a low-degree polynomial along the coordinate embedding preserves the
low-individual-degree bound in `m + 1` variables. -/
theorem degreeOf_rename_embedCoord_le (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (i : Fin params.next.m) :
    MvPolynomial.degreeOf i
      (MvPolynomial.rename (embedCoord params) g.poly : PolynomialModel params.next) ≤
      params.d := by
  change MvPolynomial.degreeOf i
    (MvPolynomial.rename (embedCoord params) g.poly :
      MvPolynomial (Fin params.next.m) (Scalar params)) ≤ params.d
  have hinj : Function.Injective (embedCoord params) := embedCoord_injective params
  by_cases h : i.val < params.m
  · -- i is in the range of embedCoord: transfer the degree bound
    have hi : embedCoord params ⟨i.val, h⟩ = i := by
      ext; simp [embedCoord]
    rw [← hi, MvPolynomial.degreeOf_rename_of_injective (R := Scalar params) hinj]
    exact g.lowIndividualDegree _
  · -- i is not in range: degreeOf = 0
    have hi_last : i = lastCoord params := by
      apply Fin.ext
      have hle : params.m ≤ i.val := Nat.le_of_not_gt h
      have hlt : i.val < params.m + 1 := by
        simpa [Parameters.next] using i.isLt
      exact le_antisymm (Nat.le_of_lt_succ hlt) hle
    rw [hi_last, degreeOf_rename_embedCoord_lastCoord]
    omega

/-- Extend a global polynomial to the slice at height `x` by ignoring the new variable. -/
noncomputable def appendAtHeight (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (_x : Fq params) : Polynomial params.next where
  poly := MvPolynomial.rename (embedCoord params) g.poly
  lowIndividualDegree := degreeOf_rename_embedCoord_le params g

/-- Evaluating an old polynomial after appending a new coordinate ignores the
appended coordinate. -/
@[simp] theorem appendAtHeight_apply_appendPoint
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (x : Fq params) (u : Point params) (y : Fq params) :
    appendAtHeight params g x (appendPoint params u y) = g u := by
  change encodeScalar (params := params)
      (MvPolynomial.eval (decodePoint (appendPoint params u y))
        (MvPolynomial.rename (embedCoord params) g.poly)) =
    encodeScalar (params := params) (MvPolynomial.eval (decodePoint u) g.poly)
  rw [MvPolynomial.eval_rename (R := Scalar params)]
  have hcoords :
      decodePoint (appendPoint params u y) ∘ embedCoord params = decodePoint u := by
    funext i
    simp [decodePoint, appendPoint, embedCoord]
    rfl
  rw [hcoords]

/-- Coordinate map for restricting a polynomial in `m+1` variables to the slice `X_m = x`. -/
noncomputable def restrictAtHeightCoordinateMap (params : Parameters) [FieldModel params.q]
    (x : Fq params) :
    Fin params.next.m → PolynomialModel params :=
  fun i =>
    if h : i.1 < params.m then
      MvPolynomial.X ⟨i.1, h⟩
    else
      MvPolynomial.C (decodeScalar x)

private theorem degreeOf_restrictAtHeightCoordinateMap_le
    (params : Parameters) [FieldModel params.q] (x : Fq params)
    (i : Fin params.m) (j : Fin params.next.m) :
    MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) ≤
      if j = embedCoord params i then 1 else 0 := by
  classical
  by_cases hji : j = embedCoord params i
  · subst hji
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · let := hsub
      have hX : (MvPolynomial.X i : PolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [restrictAtHeightCoordinateMap, embedCoord, hX]
    · let := hnontriv
      simp [restrictAtHeightCoordinateMap, embedCoord]
  · by_cases hj : j.1 < params.m
    · have hne : (⟨j.1, hj⟩ : Fin params.m) ≠ i := by
        intro h
        apply hji
        ext
        simpa [embedCoord] using congrArg Fin.val h
      rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
      · let := hsub
        have hX : (MvPolynomial.X ⟨j.1, hj⟩ : PolynomialModel params) = 0 := Subsingleton.elim _ _
        simp [restrictAtHeightCoordinateMap, hj, hji, hX]
      · let := hnontriv
        have hne' : i ≠ ⟨j.1, hj⟩ := by
          simpa [eq_comm] using hne
        rw [restrictAtHeightCoordinateMap, dif_pos hj, MvPolynomial.degreeOf_X]
        simp [hne', hji]
    · simp [restrictAtHeightCoordinateMap, hj, MvPolynomial.degreeOf_C, hji]

/-- Restricting a polynomial to a coordinate slice via `eval₂Hom` preserves the
low-individual-degree bound: each variable's degree stays at most `d`. -/
theorem degreeOf_eval₂Hom_restrictAtHeightCoordinateMap_le
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params.next) (x : Fq params) (i : Fin params.m) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly) ≤
      params.d := by
    classical
    let p : MvPolynomial (Fin params.next.m) (Scalar params) := g.poly
    change MvPolynomial.degreeOf i
      (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) p) ≤ params.d
    rw [p.as_sum]
    rw [map_sum
      (g := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x))
      (s := p.support)
      (f := fun n => (MvPolynomial.monomial n) (p.coeff n))]
    calc
      MvPolynomial.degreeOf i
          (∑ n ∈ p.support,
            MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
              (MvPolynomial.monomial n (p.coeff n))) ≤
          p.support.sup fun n =>
            MvPolynomial.degreeOf i
              (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
                (MvPolynomial.monomial n (p.coeff n))) :=
        MvPolynomial.degreeOf_sum_le i _ _
      _ ≤ params.d := by
        apply Finset.sup_le
        intro n hn
        rw [MvPolynomial.eval₂Hom_monomial]
        calc
          MvPolynomial.degreeOf i
              ((MvPolynomial.C (p.coeff n) : PolynomialModel params) *
                ∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) ≤
              MvPolynomial.degreeOf i (MvPolynomial.C (p.coeff n)) +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ 0 +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            gcongr
            exact (MvPolynomial.degreeOf_C (g.poly.coeff n) i).le
          _ =
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            simp
          _ ≤ ∑ j ∈ n.support,
                MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_prod_le i _ _
          _ ≤ ∑ j ∈ n.support, if j = embedCoord params i then n j else 0 := by
            apply Finset.sum_le_sum
            intro j hj
            calc
              MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) ≤
                  n j * MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) :=
                MvPolynomial.degreeOf_pow_le i _ _
              _ ≤ n j * (if j = embedCoord params i then 1 else 0) := by
                exact Nat.mul_le_mul_left _ (degreeOf_restrictAtHeightCoordinateMap_le params x i j)
              _ = if j = embedCoord params i then n j else 0 := by
                split_ifs <;> simp
          _ = n (embedCoord params i) := by
            by_cases hmem : embedCoord params i ∈ n.support
            · rw [Finset.sum_eq_single (embedCoord params i)]
              · simp
              · intro j hj hne
                simp [hne]
              · intro hnot
                contradiction
            · rw [Finset.sum_eq_zero]
              · rw [Finsupp.notMem_support_iff.mp hmem]
              · intro j hj
                by_cases h : j = embedCoord params i
                · exact (hmem (h ▸ hj)).elim
                · simp [h]
          _ ≤ params.d := by
            exact
              (MvPolynomial.degreeOf_le_iff.mp
                (g.lowIndividualDegree (embedCoord params i))) n hn

/-- Restrict a global polynomial in `m + 1` variables to the slice at height `x`. -/
noncomputable def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (g : Polynomial params.next) (x : Fq params) : Polynomial params where
  poly := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly
  lowIndividualDegree := degreeOf_eval₂Hom_restrictAtHeightCoordinateMap_le params g x

/-- Coordinate polynomial for restricting to an axis-parallel affine line. -/
noncomputable def axisCoordinatePolynomial (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    if i = ℓ.direction then
      _root_.Polynomial.C (decodeScalar (ℓ.base i)) + _root_.Polynomial.X
    else
      _root_.Polynomial.C (decodeScalar (ℓ.base i))

private theorem natDegree_axisCoordinatePolynomial_le (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) (i : Fin params.m) :
    (axisCoordinatePolynomial params ℓ i).natDegree ≤ if i = ℓ.direction then 1 else 0 := by
  classical
  by_cases hi : i = ℓ.direction
  · subst hi
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · let := hsub
      have hX : (_root_.Polynomial.X : LinePolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [axisCoordinatePolynomial, hX]
    · let := hnontriv
      simp [axisCoordinatePolynomial, add_comm]
  · simp [axisCoordinatePolynomial, hi, Polynomial.natDegree_C]

/-- Restricting a low-degree polynomial to an axis-parallel line via `eval₂Hom` yields a
univariate polynomial whose natural degree is at most `d`. -/
theorem natDegree_eval₂Hom_axisCoordinatePolynomial_le
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) :
    (MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
      g.poly).natDegree ≤ params.d := by
    classical
    rw [g.poly.as_sum, map_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := g.poly.support)
      (f := fun n =>
        MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
          (MvPolynomial.monomial n (g.poly.coeff n)))
      (n := params.d) ?_
    intro n hn
    rw [MvPolynomial.eval₂Hom_monomial]
    calc
      ((_root_.Polynomial.C (g.poly.coeff n) : LinePolynomialModel params) *
          ∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
          (∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ ∑ j ∈ n.support, (axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j ∈ n.support, if j = ℓ.direction then n j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
              n j * (axisCoordinatePolynomial params ℓ j).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ n j * (if j = ℓ.direction then 1 else 0) := by
            exact Nat.mul_le_mul_left _ (natDegree_axisCoordinatePolynomial_le params ℓ j)
          _ = if j = ℓ.direction then n j else 0 := by
            split_ifs <;> simp
      _ = n ℓ.direction := by
        by_cases hmem : ℓ.direction ∈ n.support
        · rw [Finset.sum_eq_single ℓ.direction]
          · simp
          · intro j hj hne
            simp [hne]
          · intro hnot
            contradiction
        · rw [Finset.sum_eq_zero]
          · rw [Finsupp.notMem_support_iff.mp hmem]
          · intro j hj
            by_cases h : j = ℓ.direction
            · exact (hmem (h ▸ hj)).elim
            · simp [h]
      _ ≤ params.d := by
        exact (MvPolynomial.degreeOf_le_iff.mp (g.lowIndividualDegree ℓ.direction)) n hn

/-- Restrict a global polynomial to an axis-parallel line. -/
noncomputable def restrictToAxisParallelLine (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) : AxisLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ) g.poly
  degreeBounded := natDegree_eval₂Hom_axisCoordinatePolynomial_le params g ℓ

/-- Evaluating an axis-parallel restriction agrees with evaluating the original
polynomial at the corresponding point on the line. -/
@[simp] theorem restrictToAxisParallelLine_apply
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) (t : Fq params) :
    restrictToAxisParallelLine params g ℓ t = g (ℓ.pointAt t) := by
  unfold restrictToAxisParallelLine Polynomial.toFun AxisLinePolynomial.toFun
    evalLinePolynomialModel evalPolynomialModel
  change encodeScalar
      (Polynomial.eval (decodeScalar t)
        (MvPolynomial.eval₂ Polynomial.C
          (axisCoordinatePolynomial params ℓ) g.poly)) = _
  rw [MvPolynomial.polynomial_eval_eval₂]
  change encodeScalar
      (MvPolynomial.eval₂
        ((Polynomial.evalRingHom (decodeScalar t)).comp Polynomial.C)
        (fun s => Polynomial.eval (decodeScalar t)
          (axisCoordinatePolynomial params ℓ s)) g.poly) =
    encodeScalar (MvPolynomial.eval₂ (RingHom.id _) (decodePoint (ℓ.pointAt t)) g.poly)
  have hcoeff :
      ((Polynomial.evalRingHom (decodeScalar t)).comp Polynomial.C) =
        RingHom.id _ := by
    ext a
    simp
  rw [hcoeff]
  have hvars :
      (fun s => Polynomial.eval (decodeScalar t)
        (axisCoordinatePolynomial params ℓ s)) =
        decodePoint (ℓ.pointAt t) := by
    funext i
    by_cases h : i = ℓ.direction
    · subst h
      simp [axisCoordinatePolynomial, AxisParallelLine.pointAt, decodePoint, addCoord]
    · simp [axisCoordinatePolynomial, AxisParallelLine.pointAt, decodePoint, h]
  rw [hvars]









end Polynomial


end MIPStarRE.LDT

end

end LIDT


