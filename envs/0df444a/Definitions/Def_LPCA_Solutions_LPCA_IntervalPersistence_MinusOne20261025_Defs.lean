-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
-- name    : LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T01:30:31.853679+00:00
-- url     : https://prove2.me/theorems/f75baf51-bd4a-457a-a967-7604557c9d96
-- title:
--   Interval Persistence — degree minus-one interval dependencies
-- statement:
--   Selected constructions and proved compatibility results for interval persistence, used in the explicit degree-minus-one interval presentations. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   Order convexity of a real interval, stated without endpoint conventions.
--
--   The actual reversed-arrow interval module. Its values are scalar spaces
--   on `J`, with identity scalar maps within `J` and zero elsewhere.
--
--   Empty support gives the zero module, including a half-open interval
--   `[b,b)`. A singleton support is allowed by the generic construction and
--   is not asserted to be zero.
--
--   The scalar identity when both supports are present, and zero otherwise.
--
--   A concrete scalar space which is `k` when `P` holds and zero otherwise.
--   The definition does not depend on any cohomology or barcode comparison.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Proposition3.12 and Corollary6.4, with their formalization dependencies. Certified Lean source: Solutions/LPCA_IntervalPersistence.lean, selected declarations in lines 13–96; source SHA-256 36a06e94ac83bd3f09b60732b4e34eeb7d31e0a44333d3c560a4ae00638dcc5d; exact-source certificate Sapelo2 job 49311470.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) [Field k]

/-- A concrete scalar space which is `k` when `P` holds and zero otherwise.
The definition does not depend on any cohomology or barcode comparison. -/
abbrev intervalScalarSpace (P : Prop) := PLift P → k

/-- The scalar identity when both supports are present, and zero otherwise. -/
noncomputable def intervalScalarMap (P Q : Prop) :
    intervalScalarSpace k P →ₗ[k] intervalScalarSpace k Q := by
  classical
  exact
    { toFun := fun x _ => if hp : P then x ⟨hp⟩ else 0
      map_add' := by
        intro x y
        funext z
        by_cases hp : P <;> simp [hp]
      map_smul' := by
        intro c x
        funext z
        by_cases hp : P <;> simp [hp] }

theorem intervalScalarMap_self (P : Prop) :
    intervalScalarMap k P P = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  funext z
  simp [intervalScalarMap, z.down]

theorem intervalScalarMap_comp (P Q R : Prop) (h : R → P → Q) :
    (intervalScalarMap k Q R).comp (intervalScalarMap k P Q) =
      intervalScalarMap k P R := by
  classical
  apply LinearMap.ext
  intro x
  funext z
  by_cases hp : P
  · have hq : Q := h z.down hp
    simp [intervalScalarMap, hp, hq]
  · by_cases hq : Q <;> simp [intervalScalarMap, hp, hq]

/-- Order convexity of a real interval, stated without endpoint conventions. -/
def IsTimeInterval (J : Set ℝ) : Prop :=
  ∀ ⦃s t u : ℝ⦄, s ≤ t → t ≤ u → s ∈ J → u ∈ J → t ∈ J

/-- The actual reversed-arrow interval module. Its values are scalar spaces
on `J`, with identity scalar maps within `J` and zero elsewhere. -/
noncomputable def intervalPersistence (J : Set ℝ) (hJ : IsTimeInterval J) :
    OrderDual ℝ ⥤ ModuleCat.{u} k where
  obj t := ModuleCat.of k (intervalScalarSpace k (OrderDual.ofDual t ∈ J))
  map {s t} _ := ModuleCat.ofHom
    (intervalScalarMap k (OrderDual.ofDual s ∈ J) (OrderDual.ofDual t ∈ J))
  map_id _ := ModuleCat.hom_ext (intervalScalarMap_self k _)
  map_comp {s t w} hst htw := by
    apply ModuleCat.hom_ext
    exact (intervalScalarMap_comp k _ _ _
      (fun hw hs => hJ (leOfHom htw) (leOfHom hst) hw hs)).symm

theorem intervalScalarSpace_isZero (P : Prop) (hP : ¬ P) :
    IsZero (ModuleCat.of k (intervalScalarSpace k P)) := by
  letI : IsEmpty (PLift P) := ⟨fun x => hP x.down⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

noncomputable def intervalScalarEquivOfTrue (P : Prop) (hP : P) :
    k ≃ₗ[k] intervalScalarSpace k P where
  toFun x _ := x
  invFun x := x ⟨hP⟩
  left_inv _ := rfl
  right_inv x := by funext z; cases z; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def intervalPersistenceCongr (J J' : Set ℝ)
    (hJ : IsTimeInterval J) (hJ' : IsTimeInterval J') (h : J = J') :
    intervalPersistence k J hJ ≅ intervalPersistence k J' hJ' := by
  subst J'
  exact Iso.refl _

/-- Empty support gives the zero module, including a half-open interval
`[b,b)`. A singleton support is allowed by the generic construction and
is not asserted to be zero. -/
theorem intervalPersistence_isZero_of_empty (J : Set ℝ) (hJ : IsTimeInterval J)
    (h : J = ∅) : IsZero (intervalPersistence k J hJ) := by
  apply Functor.isZero
  intro t
  exact intervalScalarSpace_isZero k _ (by simp [h])

end LPCA


