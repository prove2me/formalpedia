-- Prove2me | Definitions.Def_Sensitivity213303_Selected10007
-- name    : Sensitivity213303_Selected10007
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:28:18.259383+00:00
-- url     : https://prove2.me/theorems/ca744e32-8c2d-4be6-81d6-f197abaf9758
-- title:
--   A fixed 10007-vertex tournament with a proved jointly avoiding labeling
-- statement:
--   An equivalence transports the Paley tournament to Fin 10007, preserving indegree and outdegree 5003 and common-neighbor counts 2501. The proved local-lemma result establishes existence of an edge labeling avoiding every required ordinary, marked, source and two-dominator event. selectedLabel chooses one such labeling by classical choice. No labeling-existence or tournament-geometry hypothesis is left for later callers to assume.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Selected10007; source SHA256 6e41259eb3d028c127dbdb8df743328e6345acfb656abc3bb5e4a0bf0105737b.

/- A concrete indexed Paley tournament and a labeling with all 23 exclusions. -/
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_Sensitivity213303_Paley10007
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
namespace Sensitivity10007Labeling.CompactDRT
end Sensitivity10007Labeling.CompactDRT
namespace Sensitivity10007Labeling.ZL
end Sensitivity10007Labeling.ZL


set_option autoImplicit false
open scoped Classical
noncomputable section

namespace Sensitivity10007Labeling
namespace Labeling10007
open CompactDRT ZL
attribute [local irreducible] core10007
set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

def selectedEquiv : Fin 10007 ≃ Vertex10007 :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin,vertex10007_card])

def Adj (i j : Fin 10007) : Prop :=
  Adj10007 (selectedEquiv i) (selectedEquiv j)

theorem irreflexive (i : Fin 10007) : ¬ Adj i i :=
  core10007.irreflexive (selectedEquiv i)

theorem edge_compl (i j : Fin 10007) (hij : i ≠ j) :
    Adj i j ↔ ¬ Adj j i :=
  ⟨core10007.asymmetric _ _,
    fun hn => (core10007.oriented _ _ (selectedEquiv.injective.ne hij)).resolve_right hn⟩

/-- Transport finite predicate cardinality through an equivalence. -/
theorem card_filter_of_equiv {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (P : V → Prop) (Q : W → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x ↔ Q (e x)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(h x).mp (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact e.injective he
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(h (e.symm y)).mpr ?_⟩
    simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hy).2

theorem outdegree (i : Fin 10007) :
    (Finset.univ.filter (Adj i)).card = 5003 :=
  (card_filter_of_equiv selectedEquiv (Adj i) (Adj10007 (selectedEquiv i))
    (fun _ => Iff.rfl)).trans (outdegree10007 (selectedEquiv i))

theorem indegree (i : Fin 10007) :
    (Finset.univ.filter fun z => Adj z i).card = 5003 :=
  (card_filter_of_equiv selectedEquiv (fun z => Adj z i) (fun z => Adj10007 z (selectedEquiv i))
    (fun _ => Iff.rfl)).trans (indegree10007 (selectedEquiv i))

theorem common_out (i j : Fin 10007) (hij : i ≠ j) :
    (Finset.univ.filter fun z => Adj i z ∧ Adj j z).card = 2501 :=
  (card_filter_of_equiv selectedEquiv (fun z => Adj i z ∧ Adj j z)
    (fun z => Adj10007 (selectedEquiv i) z ∧ Adj10007 (selectedEquiv j) z)
    (fun _ => Iff.rfl)).trans
      (common_out10007 _ _ (selectedEquiv.injective.ne hij))

theorem common_in (i j : Fin 10007) (hij : i ≠ j) :
    (Finset.univ.filter fun z => Adj z i ∧ Adj z j).card = 2501 :=
  (card_filter_of_equiv selectedEquiv (fun z => Adj z i ∧ Adj z j)
    (fun z => Adj10007 z (selectedEquiv i) ∧ Adj10007 z (selectedEquiv j))
    (fun _ => Iff.rfl)).trans
      (common_in10007 _ _ (selectedEquiv.injective.ne hij))

/-- No labeling, geometry, or local-lemma hypothesis remains in this theorem. -/
theorem exists_selected_labeling :
    ∃ ell : Fin 10007 × Fin 10007 → Fin 2,
      CompactLabeling10007.JointExclusions Adj ell := by
  apply Paley10007Verified.CompactLabeling10007.exists_joint_exclusions Adj
  · exact Fintype.card_fin 10007
  · exact irreflexive
  · exact edge_compl
  · intro x
    simpa only [ZL.outOn, CompactLabeling10007.degree] using outdegree x
  · intro x
    simpa only [ZL.inOn, CompactLabeling10007.degree] using indegree x
  · intro x y hxy
    simpa only [CompactLabeling10007.common] using common_in x y hxy
  · intro x y hxy
    simpa only [CompactLabeling10007.common] using common_out x y hxy

def selectedLabel : Fin 10007 × Fin 10007 → Fin 2 :=
  Classical.choose exists_selected_labeling



end Labeling10007
end Sensitivity10007Labeling
end


