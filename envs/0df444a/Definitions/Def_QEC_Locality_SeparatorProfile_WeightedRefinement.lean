-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
-- name    : QEC_Locality_SeparatorProfile_WeightedRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:40:39.817908+00:00
-- url     : https://prove2.me/theorems/9eb8be0d-1dd1-4b76-9f81-caebf53983fb
-- title:
--   Weighted Refinement
-- statement:
--   Definitions and structural lemmas for Weighted Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_AssumedBGKLMeasuredProfilePowerUpperBound_edgeRestricted
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_disjoint_stopSides
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_marked_light
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_subset
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposed_stopSides_separatorUnion
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_separatorUnion_card_le_weightedSpineSeparatorBudget
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_disjoint
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_marked_light
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_subset_terminalCarrier
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_terminalCarrier_subset
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_threeSides_noEdge
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff
import Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def touches (side : Finset ι) (edge : ι × ι) : Prop :=
  edge.1 ∈ side ∨ edge.2 ∈ side
noncomputable def weightedSpineFirstEdges
    (edges : Finset (ι × ι)) (first : Finset ι) : Finset (ι × ι) :=
  by
    classical
    exact edges.filter (touches first)
noncomputable def weightedSpineSecondEdges
    (edges : Finset (ι × ι)) (first second : Finset ι) : Finset (ι × ι) :=
  by
    classical
    exact edges.filter fun edge => ¬ touches first edge ∧ touches second edge
noncomputable def weightedSpineThirdEdges
    (edges : Finset (ι × ι)) (first second : Finset ι) : Finset (ι × ι) :=
  by
    classical
    exact edges.filter fun edge => ¬ touches first edge ∧ ¬ touches second edge
theorem weightedSpineFirstEdges_reverse
    (edges : Finset (ι × ι)) (first : Finset ι)
    (hsymmetric : ReverseSymmetricEdgeSet edges) (x y : ι) :
    (x, y) ∈ weightedSpineFirstEdges edges first ↔
      (y, x) ∈ weightedSpineFirstEdges edges first := by
  simp only [weightedSpineFirstEdges, Finset.mem_filter, touches]
  rw [hsymmetric]
  tauto
theorem weightedSpineSecondEdges_reverse
    (edges : Finset (ι × ι)) (first second : Finset ι)
    (hsymmetric : ReverseSymmetricEdgeSet edges) (x y : ι) :
    (x, y) ∈ weightedSpineSecondEdges edges first second ↔
      (y, x) ∈ weightedSpineSecondEdges edges first second := by
  classical
  unfold weightedSpineSecondEdges
  erw [Finset.mem_filter, Finset.mem_filter]
  simp only [touches]
  rw [hsymmetric]
  tauto
theorem weightedSpineThirdEdges_reverse
    (edges : Finset (ι × ι)) (first second : Finset ι)
    (hsymmetric : ReverseSymmetricEdgeSet edges) (x y : ι) :
    (x, y) ∈ weightedSpineThirdEdges edges first second ↔
      (y, x) ∈ weightedSpineThirdEdges edges first second := by
  classical
  unfold weightedSpineThirdEdges
  erw [Finset.mem_filter, Finset.mem_filter]
  simp only [touches]
  rw [hsymmetric]
  tauto
theorem edgeRestricted_adjacent_of_mem
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)}
    (hsubset : edges ⊆ directedEdgeFinset G) {x y : ι}
    (hxy : (x, y) ∈ edges) : (edgeRestrictedGraph G edges).adjacent x y := by
  exact ⟨(mem_directedEdgeFinset_iff G x y).1 (hsubset hxy), Or.inl hxy⟩
theorem endpoint_in_threeSide_or_separator
    {H : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine H marked vertices) {x : ι} (hx : x ∈ vertices) :
    x ∈ spine.exposedSide ∨ x ∈ spine.stopSides.1 ∨
      x ∈ spine.stopSides.2 ∨ x ∈ markedSpineSeparatorUnion spine := by
  have hx' : x ∈ spine.exposedSide ∪ spine.stopSides.1 ∪ spine.stopSides.2 ∪
      markedSpineSeparatorUnion spine := by
    rw [spine.exposed_stopSides_separatorUnion]
    exact hx
  rcases Finset.mem_union.mp hx' with hxthree | hxseparator
  · rcases Finset.mem_union.mp hxthree with hxtwo | hxthird
    · rcases Finset.mem_union.mp hxtwo with hxfirst | hxsecond
      · exact Or.inl hxfirst
      · exact Or.inr (Or.inl hxsecond)
    · exact Or.inr (Or.inr (Or.inl hxthird))
  · exact Or.inr (Or.inr (Or.inr hxseparator))
theorem weightedSpineFirstEdges_incident_subset
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices) :
    edgeIncidentVertices (weightedSpineFirstEdges edges spine.exposedSide) ⊆
      spine.exposedSide ∪ markedSpineSeparatorUnion spine := by
  classical
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hxendpoint⟩
  have hedgeParent := (Finset.mem_filter.mp hedge).1
  have htouch := (Finset.mem_filter.mp hedge).2
  have hadj := edgeRestricted_adjacent_of_mem G hsubset hedgeParent
  have hxvertices : x ∈ vertices := by
    exact hincident ((mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hedgeParent, hxendpoint⟩)
  rcases endpoint_in_threeSide_or_separator spine hxvertices with
    hxfirst | hxsecond | hxthird | hxseparator
  · exact Finset.mem_union_left _ hxfirst
  · rcases hxendpoint with rfl | rfl
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.1) hxfirst hxsecond)
      · exact False.elim ((spine.threeSides_noEdge.1 hyfirst hxsecond)
            ((edgeRestrictedGraph G edges).symmetric hadj))
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((spine.threeSides_noEdge.1 hxfirst hxsecond) hadj)
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.1) hyfirst hxsecond)
  · rcases hxendpoint with rfl | rfl
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.2) hxfirst hxthird)
      · exact False.elim ((spine.threeSides_noEdge.2.1 hyfirst hxthird)
            ((edgeRestrictedGraph G edges).symmetric hadj))
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((spine.threeSides_noEdge.2.1 hxfirst hxthird) hadj)
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.2) hyfirst hxthird)
  · exact Finset.mem_union_right _ hxseparator
theorem weightedSpineSecondEdges_incident_subset
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices) :
    edgeIncidentVertices
        (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1) ⊆
      spine.stopSides.1 ∪ markedSpineSeparatorUnion spine := by
  classical
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hxendpoint⟩
  have hedgeData := (Finset.mem_filter.mp hedge).2
  have hedgeParent := (Finset.mem_filter.mp hedge).1
  have hadj := edgeRestricted_adjacent_of_mem G hsubset hedgeParent
  have hxvertices : x ∈ vertices := by
    exact hincident ((mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hedgeParent, hxendpoint⟩)
  rcases endpoint_in_threeSide_or_separator spine hxvertices with
    hxfirst | hxsecond | hxthird | hxseparator
  · rcases hxendpoint with rfl | rfl
    · exact False.elim (hedgeData.1 (Or.inl hxfirst))
    · exact False.elim (hedgeData.1 (Or.inr hxfirst))
  · exact Finset.mem_union_left _ hxsecond
  · rcases hxendpoint with rfl | rfl
    · rcases hedgeData.2 with hxsecond | hysecond
      · exact False.elim ((Finset.disjoint_left.mp spine.stopSides_disjoint)
            hxsecond hxthird)
      · exact False.elim ((spine.threeSides_noEdge.2.2 hysecond hxthird)
            ((edgeRestrictedGraph G edges).symmetric hadj))
    · rcases hedgeData.2 with hxsecond | hysecond
      · exact False.elim ((spine.threeSides_noEdge.2.2 hxsecond hxthird) hadj)
      · exact False.elim ((Finset.disjoint_left.mp spine.stopSides_disjoint)
            hysecond hxthird)
  · exact Finset.mem_union_right _ hxseparator
theorem weightedSpineThirdEdges_incident_subset
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices) :
    edgeIncidentVertices
        (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1) ⊆
      spine.stopSides.2 ∪ markedSpineSeparatorUnion spine := by
  classical
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hxendpoint⟩
  have hedgeData := (Finset.mem_filter.mp hedge).2
  have hedgeParent := (Finset.mem_filter.mp hedge).1
  have hxvertices : x ∈ vertices := by
    exact hincident ((mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hedgeParent, hxendpoint⟩)
  rcases endpoint_in_threeSide_or_separator spine hxvertices with
    hxfirst | hxsecond | hxthird | hxseparator
  · rcases hxendpoint with rfl | rfl
    · exact False.elim (hedgeData.1 (Or.inl hxfirst))
    · exact False.elim (hedgeData.1 (Or.inr hxfirst))
  · rcases hxendpoint with rfl | rfl
    · exact False.elim (hedgeData.2 (Or.inl hxsecond))
    · exact False.elim (hedgeData.2 (Or.inr hxsecond))
  · exact Finset.mem_union_left _ hxthird
  · exact Finset.mem_union_right _ hxseparator
noncomputable def weightedSpineChildCarrier
    (side separatorUnion : Finset ι) : Finset ι :=
  side ∪ separatorUnion
noncomputable def weightedSpineChildBoundary
    (boundary side separatorUnion : Finset ι) : Finset ι :=
  separatorUnion ∪ (boundary ∩ weightedSpineChildCarrier side separatorUnion)
theorem weightedSpineChildBoundary_subset_carrier
    (boundary side separatorUnion : Finset ι) :
    weightedSpineChildBoundary boundary side separatorUnion ⊆
      weightedSpineChildCarrier side separatorUnion := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxseparator | hxboundary
  · exact Finset.mem_union_right _ hxseparator
  · exact (Finset.mem_inter.mp hxboundary).2
theorem weightedSpineChildBoundary_card_le
    (boundary side separatorUnion : Finset ι) :
    (weightedSpineChildBoundary boundary side separatorUnion).card ≤
      separatorUnion.card + (boundary ∩ side).card := by
  have hsubset : weightedSpineChildBoundary boundary side separatorUnion ⊆
      separatorUnion ∪ (boundary ∩ side) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxseparator | hxboundary
    · exact Finset.mem_union_left _ hxseparator
    · rcases Finset.mem_inter.mp hxboundary with ⟨hxmarked, hxcarrier⟩
      rcases Finset.mem_union.mp hxcarrier with hxside | hxseparator
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxmarked, hxside⟩)
      · exact Finset.mem_union_left _ hxseparator
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
theorem weightedSpineChildBoundary_card_lt
    (boundary side separatorUnion : Finset ι) {spineBudget : Nat}
    (hside : 3 * (boundary ∩ side).card ≤ 2 * boundary.card)
    (hseparator : separatorUnion.card ≤ spineBudget)
    (hlarge : 6 * spineBudget < boundary.card) :
    (weightedSpineChildBoundary boundary side separatorUnion).card < boundary.card := by
  have hcard := weightedSpineChildBoundary_card_le boundary side separatorUnion
  omega
theorem MarkedSeparatorSpine.separatorUnion_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    markedSpineSeparatorUnion spine ⊆ vertices := by
  intro x hx
  rw [← spine.exposed_stopSides_separatorUnion]
  exact Finset.mem_union_right _ hx
theorem MarkedSeparatorSpine.stopSides_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.stopSides.1 ⊆ vertices ∧ spine.stopSides.2 ⊆ vertices := by
  have hsides := spine.stopSides_subset_terminalCarrier
  exact ⟨hsides.1.trans spine.terminalCarrier_subset,
    hsides.2.trans spine.terminalCarrier_subset⟩
theorem MarkedSeparatorSpine.childCarriers_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine) ⊆ vertices ∧
      weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine) ⊆ vertices ∧
      weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine) ⊆ vertices := by
  exact ⟨Finset.union_subset spine.exposedSide_subset spine.separatorUnion_subset,
    Finset.union_subset spine.stopSides_subset.1 spine.separatorUnion_subset,
    Finset.union_subset spine.stopSides_subset.2 spine.separatorUnion_subset⟩
inductive WeightedBoundaryEdgeRecursion
    (G : ConnectivityGraph ι) (r spineBudget : Nat) :
    Finset (ι × ι) → Finset ι → Finset ι → Type u
  | leaf {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hboundary : boundary ⊆ vertices)
      (hcard : vertices.card ≤ r)
      (hboundaryCard : boundary.card ≤ 6 * spineBudget) :
      WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary
  | split {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hboundary : boundary ⊆ vertices)
      (hcard : vertices.card ≤ r)
      (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
      (hseparatorCard : (markedSpineSeparatorUnion spine).card ≤ spineBudget)
      (hboundaryLarge : 6 * spineBudget < boundary.card)
      (firstTree : WeightedBoundaryEdgeRecursion G r spineBudget
        (weightedSpineFirstEdges edges spine.exposedSide)
        (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
        (weightedSpineChildBoundary boundary spine.exposedSide
          (markedSpineSeparatorUnion spine)))
      (secondTree : WeightedBoundaryEdgeRecursion G r spineBudget
        (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
        (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
        (weightedSpineChildBoundary boundary spine.stopSides.1
          (markedSpineSeparatorUnion spine)))
      (thirdTree : WeightedBoundaryEdgeRecursion G r spineBudget
        (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
        (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
        (weightedSpineChildBoundary boundary spine.stopSides.2
          (markedSpineSeparatorUnion spine))) :
      WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary
noncomputable def buildWeightedBoundaryEdgeRecursion
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (r : Nat) (edges : Finset (ι × ι)) (vertices boundary : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hboundary : boundary ⊆ vertices)
    (hcard : vertices.card ≤ r) :
    WeightedBoundaryEdgeRecursion G r (weightedSpineSeparatorBudget beta exponent r)
      edges vertices boundary := by
  classical
  let spineBudget := weightedSpineSeparatorBudget beta exponent r
  by_cases hleaf : boundary.card ≤ 6 * spineBudget
  · exact .leaf hsubset hsymmetric hincident hboundary hcard hleaf
  · let H := edgeRestrictedGraph G edges
    let spine := buildMarkedSeparatorSpine H boundary vertices
    let separatorUnion := markedSpineSeparatorUnion spine
    let first := spine.exposedSide
    let second := spine.stopSides.1
    let third := spine.stopSides.2
    have hboundaryLarge : 6 * spineBudget < boundary.card := Nat.lt_of_not_ge hleaf
    have hvertices : 1 ≤ vertices.card := by
      have hboundaryPositive : 0 < boundary.card := by omega
      exact hboundaryPositive.trans_le (Finset.card_le_card hboundary)
    have hprofileH : AssumedBGKLMeasuredProfilePowerUpperBound H beta exponent :=
      hProfile.edgeRestricted G beta exponent edges
    have hseparator : separatorUnion.card ≤ spineBudget := by
      exact spine.separatorUnion_card_le_weightedSpineSeparatorBudget
        hprofileH hvertices hcard
    have hfirstLight : 3 * (boundary ∩ first).card ≤ 2 * boundary.card :=
      spine.exposedSide_marked_light
    have hstopLight := spine.stopSides_marked_light
    have hsecondLight : 3 * (boundary ∩ second).card ≤ 2 * boundary.card :=
      hstopLight.1
    have hthirdLight : 3 * (boundary ∩ third).card ≤ 2 * boundary.card :=
      hstopLight.2
    have hfirstStrict :
        (weightedSpineChildBoundary boundary first separatorUnion).card < boundary.card :=
      weightedSpineChildBoundary_card_lt boundary first separatorUnion
        hfirstLight hseparator hboundaryLarge
    have hsecondStrict :
        (weightedSpineChildBoundary boundary second separatorUnion).card < boundary.card :=
      weightedSpineChildBoundary_card_lt boundary second separatorUnion
        hsecondLight hseparator hboundaryLarge
    have hthirdStrict :
        (weightedSpineChildBoundary boundary third separatorUnion).card < boundary.card :=
      weightedSpineChildBoundary_card_lt boundary third separatorUnion
        hthirdLight hseparator hboundaryLarge
    have hcarriers := spine.childCarriers_subset
    refine .split hsubset hsymmetric hincident hboundary hcard spine hseparator hboundaryLarge
      ?_ ?_ ?_
    · exact buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
        (weightedSpineFirstEdges edges first)
        (weightedSpineChildCarrier first separatorUnion)
        (weightedSpineChildBoundary boundary first separatorUnion)
        ((Finset.filter_subset _ _).trans hsubset)
        (weightedSpineFirstEdges_reverse edges first hsymmetric)
        (weightedSpineFirstEdges_incident_subset G hsubset hincident spine)
        (weightedSpineChildBoundary_subset_carrier boundary first separatorUnion)
        ((Finset.card_le_card hcarriers.1).trans hcard)
    · exact buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
        (weightedSpineSecondEdges edges first second)
        (weightedSpineChildCarrier second separatorUnion)
        (weightedSpineChildBoundary boundary second separatorUnion)
        ((Finset.filter_subset _ _).trans hsubset)
        (weightedSpineSecondEdges_reverse edges first second hsymmetric)
        (weightedSpineSecondEdges_incident_subset G hsubset hincident spine)
        (weightedSpineChildBoundary_subset_carrier boundary second separatorUnion)
        ((Finset.card_le_card hcarriers.2.1).trans hcard)
    · exact buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
        (weightedSpineThirdEdges edges first second)
        (weightedSpineChildCarrier third separatorUnion)
        (weightedSpineChildBoundary boundary third separatorUnion)
        ((Finset.filter_subset _ _).trans hsubset)
        (weightedSpineThirdEdges_reverse edges first second hsymmetric)
        (weightedSpineThirdEdges_incident_subset G hincident spine)
        (weightedSpineChildBoundary_subset_carrier boundary third separatorUnion)
        ((Finset.card_le_card hcarriers.2.2).trans hcard)
termination_by boundary.card
decreasing_by
  · exact hfirstStrict
  · exact hsecondStrict
  · exact hthirdStrict
def WeightedBoundaryEdgeRecursion.edgeOwnerType
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary → Type
  | .leaf _ _ _ _ _ _ => Unit
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree =>
      Sum firstTree.edgeOwnerType (Sum secondTree.edgeOwnerType thirdTree.edgeOwnerType)
noncomputable instance WeightedBoundaryEdgeRecursion.edgeOwnerFintype
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    Fintype tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ _ _ =>
      change Fintype Unit
      infer_instance
  | split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      change Fintype
        (Sum firstTree.edgeOwnerType (Sum secondTree.edgeOwnerType thirdTree.edgeOwnerType))
      letI := ihFirst
      letI := ihSecond
      letI := ihThird
      infer_instance
noncomputable instance WeightedBoundaryEdgeRecursion.edgeOwnerDecidableEq
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    DecidableEq tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ _ _ =>
      change DecidableEq Unit
      infer_instance
  | split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      change DecidableEq
        (Sum firstTree.edgeOwnerType (Sum secondTree.edgeOwnerType thirdTree.edgeOwnerType))
      letI := ihFirst
      letI := ihSecond
      letI := ihThird
      infer_instance
noncomputable def WeightedBoundaryEdgeRecursion.edgeRegion
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) →
      tree.edgeOwnerType → Finset (ι × ι)
  | .leaf (edges := edges) _ _ _ _ _ _, _ => edges
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree, owner =>
      match owner with
      | Sum.inl owner => firstTree.edgeRegion owner
      | Sum.inr (Sum.inl owner) => secondTree.edgeRegion owner
      | Sum.inr (Sum.inr owner) => thirdTree.edgeRegion owner
noncomputable def WeightedBoundaryEdgeRecursion.edgeActive
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    Finset tree.edgeOwnerType := by
  classical
  exact Finset.univ.filter fun owner => (tree.edgeRegion owner).Nonempty
noncomputable def WeightedBoundaryEdgeRecursion.ownerBoundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) →
      tree.edgeOwnerType → Finset ι
  | .leaf (boundary := boundary) _ _ _ _ _ _, _ => boundary
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree, owner =>
      match owner with
      | Sum.inl owner => firstTree.ownerBoundary owner
      | Sum.inr (Sum.inl owner) => secondTree.ownerBoundary owner
      | Sum.inr (Sum.inr owner) => thirdTree.ownerBoundary owner
noncomputable def WeightedBoundaryEdgeRecursion.terminalOwnerCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary → Nat
  | .leaf _ _ _ _ _ _ => 1
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree =>
      firstTree.terminalOwnerCount + secondTree.terminalOwnerCount +
        thirdTree.terminalOwnerCount
noncomputable def WeightedBoundaryEdgeRecursion.splitCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary → Nat
  | .leaf _ _ _ _ _ _ => 0
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree =>
      1 + firstTree.splitCount + secondTree.splitCount + thirdTree.splitCount
end QEC.Locality


