-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalDecomposition_IntervalExistence20261025_Defs
-- name    : LPCA_Solutions_LPCA_FiniteIntervalDecomposition_IntervalExistence20261025_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-26T02:47:48.628198+00:00
-- url     : https://prove2.me/theorems/2ce4e232-b42e-40ed-af41-cb822dd0c96e
-- title:
--   Finite Interval Decomposition — finite interval-decomposition dependencies
-- statement:
--   Selected constructions and proved compatibility results for finite interval decomposition, used in finite interval-decomposition existence for original homogeneous Ext persistence. The formal declarations retain their exact objects, hypotheses and structure maps.
--
--   Concrete zero diagram, using the unique function on an empty type.
--
--   A finite binary direct sum of the indicated scalar interval diagrams.
--
--   Existence of a finite interval decomposition for every pointwise finite
--   dimensional diagram over a finite linear order. This statement asserts no
--   uniqueness and does not yet identify real endpoints after a pullback.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Theorem3.10, interval-decomposition existence part, with formalization dependencies. Certified Lean source: Solutions/LPCA_FiniteIntervalDecomposition.lean, selected declarations in lines 15–109; source SHA-256 e0a83c8776ccf8f52fc4d03a044e846e498ca646a08232fe6f066e48efe6afa3; exact-source certificate Sapelo2 job 49312860.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_DiagramSplitKernel_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiniteIntervalSummand_IntervalExistence20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_IntervalPersistence_MinusOne20261025_Defs
import Definitions.Def_LPCA_Solutions_LPCA_OrderedIntervalSplitting_IntervalExistence20261025_Defs

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u v

variable {k : Type u} [Field k]
variable {ι : Type v} [LinearOrder ι] [Fintype ι]

noncomputable def diagramProdIso {F F' G G' : ι ⥤ ModuleCat.{u} k}
    (e : F ≅ F') (e' : G ≅ G') : diagramProd F G ≅ diagramProd F' G' :=
  NatIso.ofComponents
    (fun t => ((e.app t).toLinearEquiv.prodCongr (e'.app t).toLinearEquiv).toModuleIso)
    (fun h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · exact diagramNaturality_apply e.hom h x.1
      · exact diagramNaturality_apply e'.hom h x.2)

/-- Concrete zero diagram, using the unique function on an empty type. -/
noncomputable def emptyIntervalSum : ι ⥤ ModuleCat.{u} k :=
  (Functor.const ι).obj (ModuleCat.of k (Fin 0 → k))

/-- A finite binary direct sum of the indicated scalar interval diagrams. -/
noncomputable def finiteIntervalSum : List (ι × ι) → (ι ⥤ ModuleCat.{u} k)
  | [] => emptyIntervalSum
  | p :: ps => diagramProd (orderedInterval k p.1 p.2) (finiteIntervalSum ps)

noncomputable def diagramIsoEmptyIntervalSum (F : ι ⥤ ModuleCat.{u} k)
    (h : ∀ t, Subsingleton (F.obj t)) : F ≅ emptyIntervalSum := by
  letI (t : ι) := h t
  exact NatIso.ofComponents
    (fun t => (LinearEquiv.ofSubsingleton (R := k) (F.obj t) (Fin 0 → k)).toModuleIso)
    (fun _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext e
      exact Fin.elim0 e)

noncomputable def diagramTotalDimension (F : ι ⥤ ModuleCat.{u} k) : ℕ :=
  ∑ t, Module.finrank k (F.obj t)

theorem diagramKernel_totalDimension_lt (F : ι ⥤ ModuleCat.{u} k)
    (hfd : ∀ t, FiniteDimensional k (F.obj t)) (i j : ι) (hij : i ≤ j)
    (inc : orderedInterval k i j ⟶ F) (ret : F ⟶ orderedInterval k i j)
    (h : inc ≫ ret = 𝟙 (orderedInterval k i j)) :
    diagramTotalDimension (diagramKernel ret) < diagramTotalDimension F := by
  classical
  letI (t : ι) := hfd t
  apply Finset.sum_lt_sum
  · intro t _
    exact (LinearMap.ker (ret.app t).hom).finrank_le
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Submodule.finrank_lt
    intro htop
    let one : (orderedInterval k i j).obj i :=
      (fun _ => 1 : intervalScalarSpace k (i ≤ i ∧ i ≤ j))
    have hmem : (inc.app i) one ∈ LinearMap.ker (ret.app i).hom := by rw [htop]; trivial
    have hz : (ret.app i) ((inc.app i) one) = 0 := hmem
    have hz' : one = 0 := (diagramRetract_apply inc ret h i one).symm.trans hz
    have hzscalar : (fun _ : PLift (i ≤ i ∧ i ≤ j) => (1 : k)) = 0 := hz'
    have h10 : (1 : k) = 0 := congrFun hzscalar ⟨le_refl i, hij⟩
    exact one_ne_zero h10

/-- Existence of a finite interval decomposition for every pointwise finite
dimensional diagram over a finite linear order. This statement asserts no
uniqueness and does not yet identify real endpoints after a pullback. -/
theorem finiteOrderedDiagram_interval_decomposition (F : ι ⥤ ModuleCat.{u} k)
    (hfd : ∀ t, FiniteDimensional k (F.obj t)) :
    ∃ ps : List (ι × ι), (∀ p ∈ ps, p.1 ≤ p.2) ∧ Nonempty (F ≅ finiteIntervalSum ps) := by
  classical
  suffices ∀ n : ℕ, ∀ F : ι ⥤ ModuleCat.{u} k,
      (∀ t, FiniteDimensional k (F.obj t)) → diagramTotalDimension F = n →
      ∃ ps : List (ι × ι), (∀ p ∈ ps, p.1 ≤ p.2) ∧ Nonempty (F ≅ finiteIntervalSum ps) by
    exact this (diagramTotalDimension F) F hfd rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hfd hdim
    by_cases hn : ∃ t, Nontrivial (F.obj t)
    · obtain ⟨i, j, hij, inc, ret, hret⟩ := finiteOrderedDiagram_has_interval_retract F hn
      have hlt : diagramTotalDimension (diagramKernel ret) < n := by
        rw [← hdim]
        exact diagramKernel_totalDimension_lt F hfd i j hij inc ret hret
      have hfdK : ∀ t, FiniteDimensional k ((diagramKernel ret).obj t) := by
        intro t
        letI := hfd t
        change FiniteDimensional k (LinearMap.ker (ret.app t).hom)
        exact inferInstance
      obtain ⟨ps, hps, ⟨e⟩⟩ := ih (diagramTotalDimension (diagramKernel ret)) hlt
        (diagramKernel ret) hfdK rfl
      refine ⟨(i, j) :: ps, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hij
        · exact hps p hp
      · exact ⟨diagramSplitKernelIso inc ret hret ≪≫ diagramProdIso (Iso.refl _) e⟩
    · have hzero : ∀ t, Subsingleton (F.obj t) := by
        intro t
        exact not_nontrivial_iff_subsingleton.mp (fun ht => hn ⟨t, ht⟩)
      exact ⟨[], by simp, ⟨diagramIsoEmptyIntervalSum F hzero⟩⟩

end LPCA


