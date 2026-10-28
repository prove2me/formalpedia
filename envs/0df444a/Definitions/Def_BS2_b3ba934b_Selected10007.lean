-- Prove2me | Definitions.Def_BS2_b3ba934b_Selected10007
-- name    : BS2_b3ba934b_Selected10007
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:03:12.030423+00:00
-- url     : https://prove2.me/theorems/261312f3-3a45-4f1f-a5c4-7df279bcb633
-- title:
--   Sensitivity separation: Selected10007 (complete source module)
-- statement:
--   Complete Lean source module `Selected10007` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Selected10007.lean; original SHA-256 6e41259eb3d028c127dbdb8df743328e6345acfb656abc3bb5e4a0bf0105737b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- A concrete indexed Paley tournament and a labeling with all 23 exclusions. -/
import Definitions.Def_BS2_b3ba934b_Paley10007

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

theorem selectedLabel_spec :
    CompactLabeling10007.JointExclusions Adj selectedLabel :=
  Classical.choose_spec exists_selected_labeling

end Labeling10007
end Sensitivity10007Labeling
end

#print axioms Sensitivity10007Labeling.Labeling10007.exists_selected_labeling
#print axioms Sensitivity10007Labeling.Labeling10007.selectedLabel_spec


