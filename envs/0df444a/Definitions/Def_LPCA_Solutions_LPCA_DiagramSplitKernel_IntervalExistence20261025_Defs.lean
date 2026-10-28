-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_DiagramSplitKernel_IntervalExistence20261025_Defs
-- name    : LPCA_Solutions_LPCA_DiagramSplitKernel_IntervalExistence20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T02:46:57.192986+00:00
-- url     : https://prove2.me/theorems/4609d964-d76e-4701-9b4f-a7eea27b6bba
-- title:
--   Diagram Split Kernel — finite interval-decomposition dependencies
-- statement:
--   Selected constructions and proved compatibility results for diagram split kernel, used in finite interval-decomposition existence for original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   The literal pointwise linear kernel, with the original maps restricted.
--
--   A concrete binary direct sum of diagrams.
--
--   A natural retraction gives an actual natural direct-sum decomposition,
--   with its actual kernel diagram as the complement.
--
--   The usual explicit decomposition x ↦ (r(x), x-i(r(x))).
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, interval-decomposition existence part, with formalization dependencies. Certified Lean source: Solutions/LPCA_DiagramSplitKernel.lean, selected declarations in lines 14–116; source SHA-256 16cacf9ad03c56281a951aa35f5b0715feb4063fa82f74353239ed9ebbb4fb11; exact-source certificate Sapelo2 job 49312860.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalSummand_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_OrderedIntervalSplitting_IntervalExistence20261025_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v

variable {k : Type u} [Field k]
variable {ι : Type v} [Category ι]

theorem diagramNaturality_apply {F G : ι ⥤ ModuleCat.{u} k}
    (α : F ⟶ G) {s t : ι} (h : s ⟶ t) (x : F.obj s) :
    (α.app t) ((F.map h) x) = (G.map h) ((α.app s) x) :=
  congrArg (fun g : F.obj s ⟶ G.obj t => g x) (α.naturality h)

/-- The literal pointwise linear kernel, with the original maps restricted. -/
noncomputable def diagramKernel {F G : ι ⥤ ModuleCat.{u} k} (r : F ⟶ G) :
    ι ⥤ ModuleCat.{u} k where
  obj t := ModuleCat.of k (LinearMap.ker (r.app t).hom)
  map {s t} h := ModuleCat.ofHom
    { toFun := fun x => ⟨(F.map h) x, by
        change (r.app t) ((F.map h) x) = 0
        rw [diagramNaturality_apply, x.property, map_zero]⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c x; apply Subtype.ext; exact map_smul _ _ _ }
  map_id t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (F.map (𝟙 t)) x = x
    simp
  map_comp h h' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (F.map (h ≫ h')) x = (F.map h') ((F.map h) x)
    simp [Functor.map_comp]

/-- A concrete binary direct sum of diagrams. -/
noncomputable def diagramProd (F G : ι ⥤ ModuleCat.{u} k) :
    ι ⥤ ModuleCat.{u} k where
  obj t := ModuleCat.of k (F.obj t × G.obj t)
  map h := ModuleCat.ofHom ((F.map h).hom.prodMap (G.map h).hom)
  map_id t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp
  map_comp h h' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp [Functor.map_comp]

theorem diagramRetract_apply {F G : ι ⥤ ModuleCat.{u} k}
    (inc : G ⟶ F) (ret : F ⟶ G) (h : inc ≫ ret = 𝟙 G)
    (t : ι) (x : G.obj t) : (ret.app t) ((inc.app t) x) = x := by
  exact congrArg (fun α : G ⟶ G => (α.app t) x) h

/-- The usual explicit decomposition x ↦ (r(x), x-i(r(x))). -/
noncomputable def diagramSplitLinearEquiv {F G : ι ⥤ ModuleCat.{u} k}
    (inc : G ⟶ F) (ret : F ⟶ G) (h : inc ≫ ret = 𝟙 G) (t : ι) :
    F.obj t ≃ₗ[k] (G.obj t × LinearMap.ker (ret.app t).hom) where
  toFun x := ⟨(ret.app t) x, ⟨x - (inc.app t) ((ret.app t) x), by
    change (ret.app t) (x - (inc.app t) ((ret.app t) x)) = 0
    rw [map_sub, diagramRetract_apply inc ret h, sub_self]⟩⟩
  invFun x := (inc.app t) x.1 + x.2
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · change (ret.app t) ((inc.app t) x.1 + x.2) = x.1
      rw [map_add, diagramRetract_apply inc ret h, x.2.property, add_zero]
    · apply Subtype.ext
      change (inc.app t) x.1 + x.2 -
        (inc.app t) ((ret.app t) ((inc.app t) x.1 + x.2)) = x.2
      rw [map_add, diagramRetract_apply inc ret h, x.2.property, add_zero]
      exact add_sub_cancel_left _ _
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      change x + y - (inc.app t) ((ret.app t) (x + y)) =
        (x - (inc.app t) ((ret.app t) x)) + (y - (inc.app t) ((ret.app t) y))
      simp only [map_add]
      exact (sub_add_sub_comm x ((inc.app t) ((ret.app t) x))
        y ((inc.app t) ((ret.app t) y))).symm
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Subtype.ext
      change c • x - (inc.app t) ((ret.app t) (c • x)) =
        c • (x - (inc.app t) ((ret.app t) x))
      simp [smul_sub]

/-- A natural retraction gives an actual natural direct-sum decomposition,
with its actual kernel diagram as the complement. -/
noncomputable def diagramSplitKernelIso {F G : ι ⥤ ModuleCat.{u} k}
    (inc : G ⟶ F) (ret : F ⟶ G) (h : inc ≫ ret = 𝟙 G) :
    F ≅ diagramProd G (diagramKernel ret) :=
  NatIso.ofComponents (fun t => (diagramSplitLinearEquiv inc ret h t).toModuleIso)
    (fun {s t} f => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · exact diagramNaturality_apply ret f x
      · apply Subtype.ext
        change (F.map f) x - (inc.app t) ((ret.app t) ((F.map f) x)) =
          (F.map f) (x - (inc.app s) ((ret.app s) x))
        rw [map_sub, diagramNaturality_apply ret f,
          diagramNaturality_apply inc f])

end LPCA


