-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.exists_opens_iSup_eq_top_nodeLocus_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/713fa83b-fa2f-515d-a2c3-b86fd528e7a2

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot.AlgebraicGeometry.TwoGluedCurves"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme IsClosedImmersion IsReduced isClosedImmersion_of_comp_eq_id"
namespace TwoGluedCurves
p2m_export "AlgebraicGeometry.TwoGluedCurves" "nodeSectionFst nodeSectionSnd nodeLocus NodeCondition"
namespace CoverT
p2m_open "AlgebraicGeometry.TwoGluedCurves AlgebraicGeometry"

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} {x : X ⟶ Spec (.of κ)}
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1]
  {ι : Type v} [Finite ι]
  (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

def node (j : ι) : X := i₁.1.base ((p₁ j).1.base (IsLocalRing.closedPoint κ))

omit [IsClosedImmersion i₁.1] [Finite ι] in
theorem range_comp_base (j : ι) : Set.range ((p₁ j).1 ≫ i₁.1).base = {node i₁ p₁ j} := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    rw [Subsingleton.elim t (IsLocalRing.closedPoint κ)]
    rfl
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint κ, rfl⟩

omit [Finite ι] in
theorem isClosed_singleton_node (j : ι) : IsClosed ({node i₁ p₁ j} : Set X) := by
  haveI : IsClosedImmersion (p₁ j).1 := isClosedImmersion_of_comp_eq_id c₁ (p₁ j).1 (p₁ j).2
  rw [← range_comp_base]
  exact ((p₁ j).1 ≫ i₁.1).isClosedEmbedding.isClosed_range

include hinj in
omit [Finite ι] in
theorem node_injective : Function.Injective (node i₁ p₁) := fun _ _ e =>
  hinj (i₁.1.isClosedEmbedding.injective e)

theorem isClosed_image_node (S : Set ι) : IsClosed (node i₁ p₁ '' S) := by
  have : node i₁ p₁ '' S = ⋃ i ∈ S, {node i₁ p₁ i} := by
    ext q; simp [Set.mem_iUnion, eq_comm]
  rw [this]
  exact Set.Finite.isClosed_biUnion (Set.toFinite S) fun i _ => isClosed_singleton_node i₁ p₁ i

def W0 : X.Opens :=
  ⟨(node i₁ p₁ '' Set.univ)ᶜ, (isClosed_image_node i₁ p₁ _).isOpen_compl⟩

def W (i : ι) : X.Opens :=
  ⟨(node i₁ p₁ '' {j | j ≠ i})ᶜ, (isClosed_image_node i₁ p₁ _).isOpen_compl⟩

include hinj in
theorem node_mem_W_iff (i j : ι) : node i₁ p₁ j ∈ W i₁ p₁ i ↔ j = i := by
  show node i₁ p₁ j ∈ (node i₁ p₁ '' {l | l ≠ i})ᶜ ↔ j = i
  rw [Set.mem_compl_iff, (node_injective i₁ p₁ hinj).mem_set_image, Set.mem_setOf_eq, not_not]

theorem node_not_mem_W0 (i : ι) : node i₁ p₁ i ∉ W0 i₁ p₁ := fun hh => hh ⟨i, trivial, rfl⟩

include hinj in
theorem W0_sup_iSup_W_eq_top : W0 i₁ p₁ ⊔ ⨆ i, W i₁ p₁ i = ⊤ := by
  apply eq_top_iff.mpr
  intro q _
  by_cases hq : q ∈ node i₁ p₁ '' Set.univ
  · obtain ⟨i, -, rfl⟩ := hq
    apply TopologicalSpace.Opens.mem_sup.mpr
    exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, (node_mem_W_iff i₁ p₁ hinj i i).mpr rfl⟩)
  · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hq)

abbrev pr : pullback x h ⟶ X := pullback.fst x h

def U0 : (pullback x h).Opens := (pr (x := x) h) ⁻¹ᵁ (W0 i₁ p₁)
def U (i : ι) : (pullback x h).Opens := (pr (x := x) h) ⁻¹ᵁ (W i₁ p₁ i)

include hinj in

theorem cover_T : U0 i₁ p₁ h ⊔ ⨆ i, U i₁ p₁ h i = ⊤ := by
  apply eq_top_iff.mpr
  intro t _
  have ht : (pr (x := x) h).base t ∈ (W0 i₁ p₁ ⊔ ⨆ i, W i₁ p₁ i : X.Opens) := by
    rw [W0_sup_iSup_W_eq_top i₁ p₁ hinj]; trivial
  rcases TopologicalSpace.Opens.mem_sup.mp ht with h0 | h1
  · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl h0)
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
    exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩))

omit [IsClosedImmersion i₁.1] [Finite ι] in

theorem nodeSectionFst_curveChange_fst (j : ι) (t : T) :
    (pr (x := x) h).base ((curveChange i₁.1 i₁.2 h).base ((nodeSectionFst p₁ h j).base t)) = node i₁ p₁ j := by
  have hcomp : nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h ≫ pr (x := x) h = h ≫ (p₁ j).1 ≫ i₁.1 := by
    simp only [nodeSectionFst, rigSection, curveChange, pr, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.assoc]
  change (nodeSectionFst p₁ h j ≫ curveChange i₁.1 i₁.2 h ≫ pr (x := x) h).base t = node i₁ p₁ j
  rw [hcomp]
  show i₁.1.base ((p₁ j).1.base (h.base t)) = node i₁ p₁ j
  rw [Subsingleton.elim (h.base t) (IsLocalRing.closedPoint κ)]
  rfl

omit [IsClosedImmersion i₁.1] [Finite ι] in

theorem nodeSectionSnd_curveChange_fst (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (j : ι) (t : T) :
    (pr (x := x) h).base ((curveChange i₂.1 i₂.2 h).base ((nodeSectionSnd p₂ h j).base t)) = node i₁ p₁ j := by
  have hcomp : nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h ≫ pr (x := x) h = h ≫ (p₂ j).1 ≫ i₂.1 := by
    simp only [nodeSectionSnd, rigSection, curveChange, pr, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.assoc]
  change (nodeSectionSnd p₂ h j ≫ curveChange i₂.1 i₂.2 h ≫ pr (x := x) h).base t = node i₁ p₁ j
  rw [hcomp, ← hnode j]
  show i₁.1.base ((p₁ j).1.base (h.base t)) = node i₁ p₁ j
  rw [Subsingleton.elim (h.base t) (IsLocalRing.closedPoint κ)]
  rfl

include hinj in

theorem nodeLocus_eq_bot_of_le_U {i j : ι} (hij : j ≠ i) {Wt : (pullback x h).Opens}
    (hW : Wt ≤ U i₁ p₁ h i) : nodeLocus x i₁ i₂ p₁ p₂ h j Wt = ⊥ := by
  apply eq_bot_iff.mpr
  rintro t ⟨ht, -⟩
  apply hij
  apply (node_mem_W_iff i₁ p₁ hinj i j).mp
  rw [← nodeSectionFst_curveChange_fst i₁ p₁ h j t]
  exact hW ht

theorem nodeLocus_eq_bot_of_le_U0 (j : ι) {Wt : (pullback x h).Opens}
    (hW : Wt ≤ U0 i₁ p₁ h) : nodeLocus x i₁ i₂ p₁ p₂ h j Wt = ⊥ := by
  apply eq_bot_iff.mpr
  rintro t ⟨ht, -⟩
  apply node_not_mem_W0 i₁ p₁ j
  rw [← nodeSectionFst_curveChange_fst i₁ p₁ h j t]
  exact hW ht

omit [IsClosedImmersion i₁.1] [Finite ι] in

theorem nodeCondition_of_nodeLocus_eq_bot (u : ι → Γ(T, ⊤)ˣ) (Wt : (pullback x h).Opens) (j : ι)
    (hbot : nodeLocus x i₁ i₂ p₁ p₂ h j Wt = ⊥) (f) (g) :
    NodeCondition x i₁ i₂ p₁ p₂ h u Wt j f g := by
  unfold NodeCondition
  haveI : Subsingleton Γ(T, nodeLocus x i₁ i₂ p₁ p₂ h j Wt) :=
    CommRingCat.subsingleton_of_isTerminal (T.sheaf.isTerminalOfEqEmpty hbot)
  exact Subsingleton.elim _ _

include hinj in

theorem nodeLocus_U_self_eq_top (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) (i : ι) :
    nodeLocus x i₁ i₂ p₁ p₂ h i (U i₁ p₁ h i) = ⊤ := by
  apply eq_top_iff.mpr
  intro t _
  refine ⟨?_, ?_⟩
  · show (pr (x := x) h).base ((curveChange i₁.1 i₁.2 h).base ((nodeSectionFst p₁ h i).base t)) ∈ W i₁ p₁ i
    rw [nodeSectionFst_curveChange_fst]
    exact (node_mem_W_iff i₁ p₁ hinj i i).mpr rfl
  · show (pr (x := x) h).base ((curveChange i₂.1 i₂.2 h).base ((nodeSectionSnd p₂ h i).base t)) ∈ W i₁ p₁ i
    rw [nodeSectionSnd_curveChange_fst i₁ i₂ p₁ p₂ h hnode]
    exact (node_mem_W_iff i₁ p₁ hinj i i).mpr rfl

theorem U0_le_U (i : ι) : U0 i₁ p₁ h ≤ U i₁ p₁ h i := fun _ ht ht' =>
  ht (Set.image_mono (Set.subset_univ _) ht')

end AlgebraicGeometry.TwoGluedCurves.CoverT

open AlgebraicGeometry.TwoGluedCurves.CoverT in
theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    {ι : Type v} [Finite ι]
    (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
    (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1)
    (hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint κ))
    (hcr : IsReduced (pullback i₁.1 i₂.1))
    {T : Scheme.{u}} (h : T ⟶ Spec (.of κ)) :
    ∃ (U₀ : (pullback x h).Opens) (U : ι → (pullback x h).Opens),
      U₀ ⊔ ⨆ i, U i = ⊤ ∧ (∀ i, U₀ ≤ U i) ∧
      (∀ (j : ι) (W : (pullback x h).Opens), W ≤ U₀ →
        nodeLocus x i₁ i₂ p₁ p₂ h j W = ⊥) ∧
      (∀ (i j : ι), j ≠ i → ∀ W : (pullback x h).Opens, W ≤ U i →
        nodeLocus x i₁ i₂ p₁ p₂ h j W = ⊥) ∧
      (∀ i : ι, nodeLocus x i₁ i₂ p₁ p₂ h i (U i) = ⊤) ∧
      (∀ (u : ι → Γ(T, ⊤)ˣ) (j : ι) (W : (pullback x h).Opens), W ≤ U₀ →
        ∀ f g, NodeCondition x i₁ i₂ p₁ p₂ h u W j f g) ∧
      (∀ (u : ι → Γ(T, ⊤)ˣ) (i j : ι), j ≠ i → ∀ W : (pullback x h).Opens, W ≤ U i →
        ∀ f g, NodeCondition x i₁ i₂ p₁ p₂ h u W j f g) := by
  refine ⟨U0 i₁ p₁ h, U i₁ p₁ h, cover_T i₁ p₁ hinj h, U0_le_U i₁ p₁ h,
    fun j W hW => nodeLocus_eq_bot_of_le_U0 i₁ i₂ p₁ p₂ h j hW,
    fun i j hij W hW => nodeLocus_eq_bot_of_le_U i₁ i₂ p₁ p₂ hinj h hij hW,
    nodeLocus_U_self_eq_top i₁ i₂ p₁ p₂ hinj h hnode,
    fun u j W hW f g => nodeCondition_of_nodeLocus_eq_bot i₁ i₂ p₁ p₂ h u W j
      (nodeLocus_eq_bot_of_le_U0 i₁ i₂ p₁ p₂ h j hW) f g,
    fun u i j hij W hW f g => nodeCondition_of_nodeLocus_eq_bot i₁ i₂ p₁ p₂ h u W j
      (nodeLocus_eq_bot_of_le_U i₁ i₂ p₁ p₂ hinj h hij hW) f g⟩

end

end S_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_opens_iSup_eq_top_nodeLocus_eq_bot (solution)
