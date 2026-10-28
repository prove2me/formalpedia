-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_OrderedIntervalSplitting_IntervalExistence20261025_Defs
-- name    : LPCA_Solutions_LPCA_OrderedIntervalSplitting_IntervalExistence20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T02:45:35.705257+00:00
-- url     : https://prove2.me/theorems/e060ddb4-9a77-4b65-90fc-395b897bfcdb
-- title:
--   Ordered Interval Splitting — finite interval-decomposition dependencies
-- statement:
--   Selected constructions and proved compatibility results for ordered interval splitting, used in finite interval-decomposition existence for original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   The scalar interval diagram on a linearly ordered index, in the forward
--   direction. Applying it to an order dual covers reversed persistence.
--
--   Defines a natural map from the scalar interval when the chosen vector's images vanish beyond the terminal index. The normalized splitting is proved separately below.
--
--   At a supported index, send the interval's scalar to the chosen vector's
--   forward image; outside the interval use the zero map.
--
--   Vanishing before the first supported object defines a natural map to the interval. Paired with the normalized vector, it is the split retraction proved below.
--
--   Pull a functional at the terminal object back across the interval. The
--   proof of support supplies the map to that terminal object.
--
--   Inclusion followed by retraction is the identity on the interval.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, interval-decomposition existence part, with formalization dependencies. Certified Lean source: Solutions/LPCA_OrderedIntervalSplitting.lean, selected declarations in lines 15–134; source SHA-256 deef7445044a73ca7671d859abe3de593b3d5a185e23b94c7d054d4eb730cbdc; exact-source certificate Sapelo2 job 49312860.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v

variable (k : Type u) [Field k]
variable {ι : Type v} [LinearOrder ι]

/-- The scalar interval diagram on a linearly ordered index, in the forward
direction. Applying it to an order dual covers reversed persistence. -/
noncomputable def orderedInterval (i j : ι) : ι ⥤ ModuleCat.{u} k where
  obj t := ModuleCat.of k (intervalScalarSpace k (i ≤ t ∧ t ≤ j))
  map {s t} _ := ModuleCat.ofHom
    (intervalScalarMap k (i ≤ s ∧ s ≤ j) (i ≤ t ∧ t ≤ j))
  map_id _ := ModuleCat.hom_ext (intervalScalarMap_self k _)
  map_comp {s t w} hst htw := by
    apply ModuleCat.hom_ext
    exact (intervalScalarMap_comp k _ _ _ (fun hw hs =>
      ⟨hs.1.trans (leOfHom hst), (leOfHom htw).trans hw.2⟩)).symm

variable {k} (F : ι ⥤ ModuleCat.{u} k)

theorem orderedMap_comp_apply {s t w : ι} (hst : s ≤ t) (htw : t ≤ w)
    (x : F.obj s) :
    (F.map (homOfLE htw)) ((F.map (homOfLE hst)) x) =
      (F.map (homOfLE (hst.trans htw))) x := by
  have h := congrArg (fun g : F.obj s ⟶ F.obj w => g x)
    (F.map_comp (homOfLE hst) (homOfLE htw))
  exact h.symm

/-- At a supported index, send the interval's scalar to the chosen vector's
forward image; outside the interval use the zero map. -/
noncomputable def orderedIntervalInclusionLinear (i j : ι) (v : F.obj i) (t : ι) :
    intervalScalarSpace k (i ≤ t ∧ t ≤ j) →ₗ[k] F.obj t := by
  classical
  exact
    { toFun := fun x => if ht : i ≤ t ∧ t ≤ j then
        x ⟨ht⟩ • (F.map (homOfLE ht.1)) v else 0
      map_add' := by
        intro x y
        by_cases ht : i ≤ t ∧ t ≤ j <;> simp [ht, add_smul]
      map_smul' := by
        intro c x
        by_cases ht : i ≤ t ∧ t ≤ j <;> simp [ht, smul_smul] }

/-- The chosen vector generates an actual interval subdiagram if its images
vanish beyond the chosen terminal index. -/
noncomputable def orderedIntervalInclusion (i j : ι) (v : F.obj i)
    (hv : ∀ t, j < t → ∀ h : i ≤ t, (F.map (homOfLE h)) v = 0) :
    orderedInterval k i j ⟶ F where
  app t := ModuleCat.ofHom (orderedIntervalInclusionLinear F i j v t)
  naturality {s t} h := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change intervalScalarSpace k (i ≤ s ∧ s ≤ j) at x
    change orderedIntervalInclusionLinear F i j v t
        (intervalScalarMap k (i ≤ s ∧ s ≤ j) (i ≤ t ∧ t ≤ j) x) =
      (F.map h) (orderedIntervalInclusionLinear F i j v s x)
    have hst : s ≤ t := leOfHom h
    have hh : h = homOfLE hst := Subsingleton.elim _ _
    by_cases hs : i ≤ s ∧ s ≤ j
    · by_cases ht : i ≤ t ∧ t ≤ j
      · simp [orderedIntervalInclusionLinear, hs, ht, intervalScalarMap,
          hh, map_smul, orderedMap_comp_apply]
      · have hjt : j < t := lt_of_not_ge (fun htj => ht ⟨hs.1.trans hst, htj⟩)
        simp [orderedIntervalInclusionLinear, hs, ht, hh, map_smul,
          orderedMap_comp_apply, hv t hjt]
    · by_cases ht : i ≤ t ∧ t ≤ j
      · simp [orderedIntervalInclusionLinear, hs, ht, intervalScalarMap]
      · simp [orderedIntervalInclusionLinear, hs, ht]

/-- Pull a functional at the terminal object back across the interval. The
proof of support supplies the map to that terminal object. -/
noncomputable def orderedIntervalRetractionLinear (i j : ι)
    (φ : F.obj j →ₗ[k] k) (t : ι) :
    F.obj t →ₗ[k] intervalScalarSpace k (i ≤ t ∧ t ≤ j) where
  toFun x ht := φ ((F.map (homOfLE ht.down.2)) x)
  map_add' x y := by funext ht; simp
  map_smul' c x := by funext ht; simp

/-- Vanishing before the first supported object makes these pulled-back
functionals a natural retraction to the interval diagram. -/
noncomputable def orderedIntervalRetraction (i j : ι)
    (φ : F.obj j →ₗ[k] k)
    (hbefore : ∀ t, t < i → Subsingleton (F.obj t)) :
    F ⟶ orderedInterval k i j where
  app t := ModuleCat.ofHom (orderedIntervalRetractionLinear F i j φ t)
  naturality {s t} h := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext ht
    change φ ((F.map (homOfLE ht.down.2)) ((F.map h) x)) =
      intervalScalarMap k (i ≤ s ∧ s ≤ j) (i ≤ t ∧ t ≤ j)
        (orderedIntervalRetractionLinear F i j φ s x) ht
    have hst : s ≤ t := leOfHom h
    have hh : h = homOfLE hst := Subsingleton.elim _ _
    by_cases hs : i ≤ s ∧ s ≤ j
    · simp [intervalScalarMap, hs, orderedIntervalRetractionLinear,
        hh, orderedMap_comp_apply]
    · have hsi : s < i := lt_of_not_ge (fun his => hs ⟨his, hst.trans ht.down.2⟩)
      haveI := hbefore s hsi
      have hx : x = 0 := Subsingleton.elim _ _
      simp [intervalScalarMap, hs, hx]

/-- Inclusion followed by retraction is the identity on the interval. -/
theorem orderedInterval_inclusion_retraction (i j : ι) (hij : i ≤ j)
    (v : F.obj i) (φ : F.obj j →ₗ[k] k)
    (hφ : φ ((F.map (homOfLE hij)) v) = 1)
    (hv : ∀ t, j < t → ∀ h : i ≤ t, (F.map (homOfLE h)) v = 0)
    (hbefore : ∀ t, t < i → Subsingleton (F.obj t)) :
    orderedIntervalInclusion F i j v hv ≫ orderedIntervalRetraction F i j φ hbefore =
      𝟙 (orderedInterval k i j) := by
  classical
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change intervalScalarSpace k (i ≤ t ∧ t ≤ j) at x
  funext ht
  change φ ((F.map (homOfLE ht.down.2))
      (orderedIntervalInclusionLinear F i j v t x)) = x ht
  simp [orderedIntervalInclusionLinear, ht.down, map_smul,
    orderedMap_comp_apply, hφ]

end LPCA


