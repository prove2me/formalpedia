-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
-- name    : QEC_Coding_CodeReduction_Classical_Collapse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:51:13.246215+00:00
-- url     : https://prove2.me/theorems/8b09dc46-809f-41ff-95e1-5423809b4d08
-- title:
--   Collapse
-- statement:
--   Definitions and structural lemmas for Collapse, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Collapse.lean

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Homotopy
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F] [Fintype Check] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit] in
theorem word_add_self_eq_zero_of_char_two [CharP F 2]
    {Index : Type*} (x : Word F Index) : x + x = 0 := by
  ext i
  exact add_self_eq_zero_of_char_two (F := F) (x i)
noncomputable def pathEdgePrefix {n : Nat} (i : Fin n) :
    Word F (Fin (n - 1)) :=
  fun j => if j.1 < i.1 then 1 else 0
noncomputable def pathEdgePrefixAtOption {n : Nat} (i : Fin n)
    (o : Option (Fin (n - 1))) : F :=
  match o with
  | none => 0
  | some j => pathEdgePrefix (F := F) i j
omit [Fintype F] [DecidableEq F] in
/-- The boundary of the path from vertex zero to `i` is supported exactly
at its two endpoints. -/
theorem pathEdgePrefix_adjacent [CharP F 2]
    {n : Nat} (hn : 0 < n) (i k : Fin n) :
    pathEdgePrefixAtOption (F := F) i (pathPrevious k) +
        pathEdgePrefixAtOption (F := F) i (pathNext k) =
      (if k.1 = 0 then 1 else 0) + (if k = i then 1 else 0) := by
  classical
  by_cases hi : i.1 = 0
  · have hpref (o : Option (Fin (n - 1))) :
        pathEdgePrefixAtOption (F := F) i o = 0 := by
      cases o <;> simp [pathEdgePrefixAtOption, pathEdgePrefix, hi]
    rw [hpref, hpref, zero_add]
    by_cases hk : k.1 = 0
    · have hki : k = i := Fin.ext (by omega)
      rw [if_pos hk, if_pos hki]
      exact (add_self_eq_zero_of_char_two (F := F) 1).symm
    · have hki : k ≠ i := by
        intro h
        apply hk
        simpa [h] using hi
      simp [hk, hki]
  · have hipos : 0 < i.1 := by omega
    by_cases hk : k.1 = 0
    · have hnext : k.1 + 1 < n := by omega
      have hnnext : 1 < n := by omega
      have hki : k ≠ i := by omega
      simp [pathEdgePrefixAtOption, pathEdgePrefix, pathPrevious,
        pathNext, hk, hnnext, hipos, hki]
    · have hkpos : 0 < k.1 := by omega
      by_cases hnext : k.1 + 1 < n
      · by_cases hki : k = i
        · subst k
          have hprev : i.1 - 1 < i.1 := by omega
          simp [pathEdgePrefixAtOption, pathEdgePrefix, pathPrevious,
            pathNext, hi, hipos, hnext, hprev]
        · by_cases hlt : k.1 < i.1
          · have hprev : k.1 - 1 < i.1 := by omega
            simp [pathEdgePrefixAtOption, pathEdgePrefix, pathPrevious,
              pathNext, hk, hkpos, hnext, hki, hlt, hprev,
              add_self_eq_zero_of_char_two (F := F)]
          · have hprev : ¬k.1 - 1 < i.1 := by omega
            have hklt : ¬k < i := by omega
            simp [pathEdgePrefixAtOption, pathEdgePrefix, pathPrevious,
              pathNext, hk, hkpos, hnext, hki, hprev, hklt]
      · by_cases hki : k = i
        · subst k
          have hprev : i.1 - 1 < i.1 := by omega
          simp [pathEdgePrefixAtOption, pathEdgePrefix, pathPrevious,
            pathNext, hi, hipos, hnext, hprev]
        · have hprev : ¬k.1 - 1 < i.1 := by omega
          simp [pathEdgePrefixAtOption, pathEdgePrefix, pathPrevious,
            pathNext, hk, hkpos, hnext, hki, hprev]
omit [Fintype F] [DecidableEq F] in
/-- The two rooted paths ending at adjacent vertices differ by their unique
connecting edge. -/
theorem pathEdgePrefix_left_add_right [CharP F 2]
    {n : Nat} (j : Fin (n - 1)) :
    pathEdgePrefix (F := F) (pathLeft j) +
        pathEdgePrefix (F := F) (pathRight j) =
      Pi.single j 1 := by
  classical
  ext k
  by_cases hkj : k = j
  · subst k
    simp [pathEdgePrefix, pathLeft, pathRight]
  · by_cases hlt : k.1 < j.1
    · have hlt' : k.1 < j.1 + 1 := by omega
      simp [pathEdgePrefix, pathLeft, pathRight, hkj, hlt, hlt',
        add_self_eq_zero_of_char_two (F := F)]
    · have hge : j.1 + 1 ≤ k.1 := by
        have hne : k.1 ≠ j.1 := by
          intro hval
          apply hkj
          exact Fin.ext hval
        omega
      have hjk : j < k := by omega
      simp [pathEdgePrefix, pathLeft, pathRight, hkj, hlt, hjk]
noncomputable def embedAuxiliaryBits (x : Word F (AuxiliaryBit R)) :
    Word F (BitSplitBit R) :=
  fun b =>
    match b with
    | Sum.inl _ => 0
    | Sum.inr a => x a
noncomputable def auxiliaryBitAtOption (x : Word F (AuxiliaryBit R))
    (c : Check) (o : Option (Fin (Fintype.card (CheckNeighbor R c) - 1))) : F :=
  match o with
  | none => 0
  | some j => x ⟨c, j⟩
noncomputable def embedAuxiliaryBitsWeightReduced
    (x : Word F (AuxiliaryBit R)) : Word F (WeightReducedBit R) :=
  fun b =>
    match b with
    | Sum.inl _ => 0
    | Sum.inr a => x a
omit [Fintype F] [DecidableEq F] in
theorem bitSplitBoundary_embedAuxiliaryBits_eq_boundary_apply
    (x : Word F (AuxiliaryBit R)) (e : Incidence R) :
    bitSplitBoundary (F := F) R (embedAuxiliaryBits (F := F) R x) e =
      boundary (F := F) R
        (embedAuxiliaryBitsWeightReduced (F := F) R x) (Sum.inl e) := by
  classical
  unfold bitSplitBoundary boundary linearMapOfBasisImages
  change (∑ b : BitSplitBit R,
      embedAuxiliaryBits (F := F) R x b •
        bitSplitBasisBoundary (F := F) R b) e =
    (∑ b : WeightReducedBit R,
      embedAuxiliaryBitsWeightReduced (F := F) R x b •
        basisBoundary (F := F) R b) (Sum.inl e)
  rw [Finset.sum_apply, Finset.sum_apply]
  simp [embedAuxiliaryBits, embedAuxiliaryBitsWeightReduced,
    bitSplitBasisBoundary, basisBoundary, bitSplitAuxiliaryBoundary,
    auxiliaryBitBoundary]
  apply Finset.sum_congr rfl
  intro a _
  simp [Pi.single_apply]
omit [DecidableEq F] in
theorem bitSplitBoundary_embedAuxiliaryBits_apply [CharP F 2]
    (x : Word F (AuxiliaryBit R)) (e : Incidence R) :
    bitSplitBoundary (F := F) R (embedAuxiliaryBits (F := F) R x) e =
      auxiliaryBitAtOption (F := F) R x e.1.1
          (pathPrevious (checkPosition R e)) +
        auxiliaryBitAtOption (F := F) R x e.1.1
          (pathNext (checkPosition R e)) := by
  rw [bitSplitBoundary_embedAuxiliaryBits_eq_boundary_apply]
  rw [boundary_apply_eq_dot_basisCoboundary]
  cases hp : pathPrevious (checkPosition R e) <;>
    cases hn : pathNext (checkPosition R e) <;>
    simp [basisCoboundary, primaryCheckCoboundary,
      embedAuxiliaryBitsWeightReduced, auxiliaryBitAtOption,
      optionalSingle, auxiliaryBitIndex, hp, hn, add_dotProduct,
      single_dotProduct]
noncomputable def checkPathPrefixWord (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) :
    Word F (AuxiliaryBit R) :=
  fun a =>
    if a.1 = c ∧ a.2.1 < i.1 then 1 else 0
noncomputable def checkPathAuxiliaryPrefix (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) :
    Word F (BitSplitBit R) :=
  fun b =>
    match b with
    | Sum.inl _ => 0
    | Sum.inr a => if a.1 = c ∧ a.2.1 < i.1 then 1 else 0
omit [Fintype F] [DecidableEq F] [Fintype Check] [DecidableEq Bit] in
theorem checkPathAuxiliaryPrefix_eq_embed (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) :
    checkPathAuxiliaryPrefix (F := F) R c i =
      embedAuxiliaryBits (F := F) R (checkPathPrefixWord (F := F) R c i) := by
  rfl
omit [DecidableEq F] in
theorem bitSplitBoundary_checkPathAuxiliaryPrefix_apply [CharP F 2]
    (h : HasNoIsolatedVertices R) (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) (e : Incidence R) :
    bitSplitBoundary (F := F) R
        (checkPathAuxiliaryPrefix (F := F) R c i) e =
      if e.1.1 = c then
        (if (checkPosition R e).1 = 0 then 1 else 0) +
          (if (checkPosition R e).1 = i.1 then 1 else 0)
      else 0 := by
  rw [checkPathAuxiliaryPrefix_eq_embed,
    bitSplitBoundary_embedAuxiliaryBits_apply]
  by_cases hec : e.1.1 = c
  · subst c
    have hp := pathEdgePrefix_adjacent (F := F)
      (h.check_card_pos R e.1.1) i (checkPosition R e)
    have hleft :
        auxiliaryBitAtOption (F := F) R
              (checkPathPrefixWord (F := F) R e.1.1 i) e.1.1
              (pathPrevious (checkPosition R e)) +
            auxiliaryBitAtOption (F := F) R
              (checkPathPrefixWord (F := F) R e.1.1 i) e.1.1
              (pathNext (checkPosition R e)) =
          pathEdgePrefixAtOption (F := F) i
              (pathPrevious (checkPosition R e)) +
            pathEdgePrefixAtOption (F := F) i
              (pathNext (checkPosition R e)) := by
      cases pathPrevious (checkPosition R e) <;>
        cases pathNext (checkPosition R e) <;>
        simp [auxiliaryBitAtOption, checkPathPrefixWord,
          pathEdgePrefixAtOption, pathEdgePrefix]
    rw [hleft, hp]
    by_cases h0 : (checkPosition R e).1 = 0 <;>
      by_cases hi : (checkPosition R e).1 = i.1 <;>
      simp [h0, hi, Fin.ext_iff]
  · cases hp : pathPrevious (checkPosition R e) <;>
      cases hn : pathNext (checkPosition R e) <;>
      simp [auxiliaryBitAtOption, checkPathPrefixWord, hec]
omit [Fintype F] [DecidableEq F] [Fintype Check] in
theorem incidenceSingle_apply_same_check (e : Incidence R)
    (k : Fin (Fintype.card (CheckNeighbor R e.1.1))) :
    (Pi.single (checkIncidenceAt R e.1.1 k) 1 : Word F (Incidence R)) e =
      if (checkPosition R e).1 = k.1 then 1 else 0 := by
  classical
  by_cases hk : k = checkPosition R e
  · subst k
    rw [checkIncidenceAt_checkPosition R e]
    simp
  · have hne : checkIncidenceAt R e.1.1 k ≠ e := by
      intro hke
      apply hk
      have hn : checkNeighborOrder R e.1.1 k = ⟨e.1.2, e.2⟩ := by
        apply Subtype.ext
        exact congrArg (fun x : Incidence R => x.1.2) hke
      have hp := congrArg (checkNeighborOrder R e.1.1).symm hn
      simpa [checkPosition] using hp
    have hval : (checkPosition R e).1 ≠ k.1 := by
      intro hval
      apply hk
      exact Fin.ext hval.symm
    simp [hne, hval]
omit [Fintype F] [DecidableEq F] [Fintype Check] in
theorem incidenceSingle_apply_of_check_ne {c : Check} (e : Incidence R)
    (hc : e.1.1 ≠ c) (k : Fin (Fintype.card (CheckNeighbor R c))) :
    (Pi.single (checkIncidenceAt R c k) 1 : Word F (Incidence R)) e = 0 := by
  classical
  have hne : checkIncidenceAt R c k ≠ e := by
    intro hke
    apply hc
    have hcheck := congrArg (fun x : Incidence R => x.1.1) hke
    simpa [checkIncidenceAt] using hcheck.symm
  simp [hne]
omit [DecidableEq F] in
/-- Vector form of the rooted check-path boundary equation. -/
theorem bitSplitBoundary_checkPathAuxiliaryPrefix [CharP F 2]
    (h : HasNoIsolatedVertices R) (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) :
    bitSplitBoundary (F := F) R
        (checkPathAuxiliaryPrefix (F := F) R c i) =
      Pi.single (checkIncidenceAt R c (checkRootPosition R h c)) 1 +
        Pi.single (checkIncidenceAt R c i) 1 := by
  classical
  ext e
  rw [bitSplitBoundary_checkPathAuxiliaryPrefix_apply (F := F) R h c i e]
  simp only [Pi.add_apply]
  by_cases hec : e.1.1 = c
  · subst c
    rw [incidenceSingle_apply_same_check (F := F) R e,
      incidenceSingle_apply_same_check (F := F) R e]
    simp [checkRootPosition]
    rfl
  · rw [incidenceSingle_apply_of_check_ne (F := F) R e hec,
      incidenceSingle_apply_of_check_ne (F := F) R e hec]
    simp [hec]
omit [Fintype F] [DecidableEq F] [Fintype Check] in
/-- Adjacent rooted check paths cancel except for the auxiliary edge between
their endpoints. -/
theorem checkPathAuxiliaryPrefix_left_add_right [CharP F 2]
    (c : Check)
    (j : Fin (Fintype.card (CheckNeighbor R c) - 1)) :
    checkPathAuxiliaryPrefix (F := F) R c (pathLeft j) +
        checkPathAuxiliaryPrefix (F := F) R c (pathRight j) =
      Pi.single (Sum.inr (⟨c, j⟩ : AuxiliaryBit R)) 1 := by
  classical
  ext b
  cases b with
  | inl b =>
      simp [checkPathAuxiliaryPrefix]
  | inr a =>
      rcases a with ⟨c', k⟩
      by_cases hc : c' = c
      · subst c'
        have hp := congrFun
          (pathEdgePrefix_left_add_right (F := F) j) k
        simpa [checkPathAuxiliaryPrefix, pathEdgePrefix,
          Pi.single_apply] using hp
      · have hne : (⟨c', k⟩ : AuxiliaryBit R) ≠ ⟨c, j⟩ := by
          intro h
          apply hc
          exact congrArg Sigma.fst h
        simp [checkPathAuxiliaryPrefix, hc, hne]
noncomputable def collapseForwardMap0Basis (e : BitSplitCheck R) :
    Word F Check :=
  Pi.single e.1.1 1
noncomputable def collapseForwardMap1Basis :
    BitSplitBit R → Word F Bit
  | Sum.inl b => Pi.single b 1
  | Sum.inr _ => 0
noncomputable def collapseForwardMap0 :
    Word F (BitSplitCheck R) →ₗ[F] Word F Check :=
  linearMapOfBasisImages (F := F) (collapseForwardMap0Basis (F := F) R)
noncomputable def collapseForwardMap1 :
    Word F (BitSplitBit R) →ₗ[F] Word F Bit :=
  linearMapOfBasisImages (F := F) (collapseForwardMap1Basis (F := F) R)
noncomputable def collapseInverseMap0Basis
    (h : HasNoIsolatedVertices R) (c : Check) :
    Word F (BitSplitCheck R) :=
  Pi.single (checkIncidenceAt R c (checkRootPosition R h c)) 1
noncomputable def collapseHomotopy0Basis (e : BitSplitCheck R) :
    Word F (BitSplitBit R) :=
  checkPathAuxiliaryPrefix (F := F) R e.1.1 (checkPosition R e)
noncomputable def collapseHomotopy0 :
    Word F (BitSplitCheck R) →ₗ[F] Word F (BitSplitBit R) :=
  linearMapOfBasisImages (F := F) (collapseHomotopy0Basis (F := F) R)
noncomputable def collapseInverseMap1Basis (b : Bit) :
    Word F (BitSplitBit R) :=
  Pi.single (Sum.inl b) 1 +
    collapseHomotopy0 (F := F) R (bitSplitPrimaryBoundary (F := F) R b)
noncomputable def collapseInverseMap0 (h : HasNoIsolatedVertices R) :
    Word F Check →ₗ[F] Word F (BitSplitCheck R) :=
  linearMapOfBasisImages (F := F) (collapseInverseMap0Basis (F := F) R h)
noncomputable def collapseInverseMap1 :
    Word F Bit →ₗ[F] Word F (BitSplitBit R) :=
  linearMapOfBasisImages (F := F) (collapseInverseMap1Basis (F := F) R)
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem collapseForwardMap0_single (e : BitSplitCheck R) :
    collapseForwardMap0 (F := F) R (Pi.single e 1) =
      collapseForwardMap0Basis (F := F) R e := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem collapseForwardMap1_single (b : BitSplitBit R) :
    collapseForwardMap1 (F := F) R (Pi.single b 1) =
      collapseForwardMap1Basis (F := F) R b := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem collapseInverseMap0_single (h : HasNoIsolatedVertices R) (c : Check) :
    collapseInverseMap0 (F := F) R h (Pi.single c 1) =
      collapseInverseMap0Basis (F := F) R h c := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem collapseInverseMap1_single (b : Bit) :
    collapseInverseMap1 (F := F) R (Pi.single b 1) =
      collapseInverseMap1Basis (F := F) R b := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem collapseHomotopy0_single (e : BitSplitCheck R) :
    collapseHomotopy0 (F := F) R (Pi.single e 1) =
      collapseHomotopy0Basis (F := F) R e := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [DecidableEq F] in
/-- Degree-zero homotopy equation for check-path collapsing. -/
theorem collapseInverseForward_homotopy_degree0 [CharP F 2]
    (h : HasNoIsolatedVertices R) :
    (collapseInverseMap0 (F := F) R h).comp
          (collapseForwardMap0 (F := F) R) - LinearMap.id =
      (bitSplitBoundary (F := F) R).comp
        (collapseHomotopy0 (F := F) R) := by
  refine linearMap_eq_of_single_one_eq (F := F)
    ((collapseInverseMap0 (F := F) R h).comp
      (collapseForwardMap0 (F := F) R) - LinearMap.id)
    ((bitSplitBoundary (F := F) R).comp
      (collapseHomotopy0 (F := F) R)) ?_
  intro e
  change collapseInverseMap0 (F := F) R h
        (collapseForwardMap0 (F := F) R (Pi.single e 1)) -
      Pi.single e 1 =
    bitSplitBoundary (F := F) R
      (collapseHomotopy0 (F := F) R (Pi.single e 1))
  rw [collapseForwardMap0_single (F := F) R e,
    collapseHomotopy0_single (F := F) R e]
  change collapseInverseMap0 (F := F) R h (Pi.single e.1.1 1) -
      Pi.single e 1 =
    bitSplitBoundary (F := F) R
      (checkPathAuxiliaryPrefix (F := F) R e.1.1 (checkPosition R e))
  rw [collapseInverseMap0_single, word_sub_eq_add_of_char_two,
    bitSplitBoundary_checkPathAuxiliaryPrefix]
  simp [collapseInverseMap0Basis]
  all_goals assumption
omit [Fintype F] [DecidableEq F] in
/-- The check-path homotopy contracts the boundary of one auxiliary bit back
to that bit. -/
theorem collapseHomotopy0_bitSplitAuxiliaryBoundary [CharP F 2]
    (a : AuxiliaryBit R) :
    collapseHomotopy0 (F := F) R
        (bitSplitAuxiliaryBoundary (F := F) R a) =
      Pi.single (Sum.inr a) 1 := by
  rcases a with ⟨c, j⟩
  unfold bitSplitAuxiliaryBoundary
  rw [map_add, collapseHomotopy0_single, collapseHomotopy0_single]
  change checkPathAuxiliaryPrefix (F := F) R c
          (checkPosition R (checkIncidenceAt R c (pathLeft j))) +
        checkPathAuxiliaryPrefix (F := F) R c
          (checkPosition R (checkIncidenceAt R c (pathRight j))) =
      Pi.single (Sum.inr (⟨c, j⟩ : AuxiliaryBit R)) 1
  rw [checkPosition_checkIncidenceAt, checkPosition_checkIncidenceAt]
  exact checkPathAuxiliaryPrefix_left_add_right (F := F) R c j
omit [Fintype F] [DecidableEq F] in
/-- Degree-one homotopy equation for check-path collapsing. -/
theorem collapseInverseForward_homotopy_degree1 [CharP F 2] :
    (collapseInverseMap1 (F := F) R).comp
          (collapseForwardMap1 (F := F) R) - LinearMap.id =
      (collapseHomotopy0 (F := F) R).comp
        (bitSplitBoundary (F := F) R) := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro b
  cases b with
  | inl b =>
      rw [LinearMap.sub_apply, LinearMap.comp_apply,
        collapseForwardMap1_single, LinearMap.id_apply,
        LinearMap.comp_apply]
      change collapseInverseMap1 (F := F) R (Pi.single b 1) -
          Pi.single (Sum.inl b) 1 =
        collapseHomotopy0 (F := F) R
          (bitSplitBoundary (F := F) R (Pi.single (Sum.inl b) 1))
      rw [collapseInverseMap1_single, bitSplitBoundary_single]
      change (Pi.single (Sum.inl b) 1 +
          collapseHomotopy0 (F := F) R
            (bitSplitPrimaryBoundary (F := F) R b)) -
          Pi.single (Sum.inl b) 1 =
        collapseHomotopy0 (F := F) R
          (bitSplitPrimaryBoundary (F := F) R b)
      rw [word_sub_eq_add_of_char_two]
      have hdouble :
          (Pi.single (Sum.inl b) 1 : Word F (BitSplitBit R)) +
              Pi.single (Sum.inl b) 1 = 0 := by
        ext x
        exact add_self_eq_zero_of_char_two (F := F) _
      calc
        Pi.single (Sum.inl b) 1 +
              collapseHomotopy0 (F := F) R
                  (bitSplitPrimaryBoundary (F := F) R b) +
            Pi.single (Sum.inl b) 1 =
          collapseHomotopy0 (F := F) R
              (bitSplitPrimaryBoundary (F := F) R b) +
            (Pi.single (Sum.inl b) 1 + Pi.single (Sum.inl b) 1) := by abel
        _ = collapseHomotopy0 (F := F) R
              (bitSplitPrimaryBoundary (F := F) R b) := by
          rw [hdouble]
          simp
  | inr a =>
      rw [LinearMap.sub_apply, LinearMap.comp_apply,
        collapseForwardMap1_single, LinearMap.id_apply,
        LinearMap.comp_apply]
      change collapseInverseMap1 (F := F) R 0 -
          Pi.single (Sum.inr a) 1 =
        collapseHomotopy0 (F := F) R
          (bitSplitBoundary (F := F) R (Pi.single (Sum.inr a) 1))
      rw [map_zero, bitSplitBoundary_single,
        word_sub_eq_add_of_char_two, zero_add]
      change Pi.single (Sum.inr a) 1 =
        collapseHomotopy0 (F := F) R
          (bitSplitAuxiliaryBoundary (F := F) R a)
      exact (collapseHomotopy0_bitSplitAuxiliaryBoundary (F := F) R a).symm
omit [Fintype F] [DecidableEq F] in
theorem collapseForwardMap1_checkPathAuxiliaryPrefix
    (c : Check) (i : Fin (Fintype.card (CheckNeighbor R c))) :
    collapseForwardMap1 (F := F) R
        (checkPathAuxiliaryPrefix (F := F) R c i) = 0 := by
  classical
  unfold collapseForwardMap1 linearMapOfBasisImages
  apply Finset.sum_eq_zero
  intro b _
  cases b <;> simp [checkPathAuxiliaryPrefix, collapseForwardMap1Basis]
omit [Fintype F] [DecidableEq F] in
theorem collapseForwardMap1_comp_collapseHomotopy0 :
    (collapseForwardMap1 (F := F) R).comp
        (collapseHomotopy0 (F := F) R) = 0 := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro e
  rw [LinearMap.comp_apply, collapseHomotopy0_single]
  exact collapseForwardMap1_checkPathAuxiliaryPrefix (F := F) R
    e.1.1 (checkPosition R e)
omit [Fintype F] [DecidableEq F] in
theorem collapseForwardMap0_comp_collapseInverseMap0
    (h : HasNoIsolatedVertices R) :
    (collapseForwardMap0 (F := F) R).comp
        (collapseInverseMap0 (F := F) R h) = LinearMap.id := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro c
  simp [collapseInverseMap0Basis, collapseForwardMap0Basis,
    checkIncidenceAt]
omit [Fintype F] [DecidableEq F] in
theorem collapseForwardMap1_comp_collapseInverseMap1 :
    (collapseForwardMap1 (F := F) R).comp
        (collapseInverseMap1 (F := F) R) = LinearMap.id := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro b
  rw [LinearMap.comp_apply, collapseInverseMap1_single,
    LinearMap.id_apply]
  unfold collapseInverseMap1Basis
  rw [map_add, collapseForwardMap1_single]
  change Pi.single b 1 + collapseForwardMap1 (F := F) R
      (collapseHomotopy0 (F := F) R
        (bitSplitPrimaryBoundary (F := F) R b)) = Pi.single b 1
  rw [← LinearMap.comp_apply,
    collapseForwardMap1_comp_collapseHomotopy0]
  simp
omit [Fintype F] [DecidableEq F] in
theorem collapseForwardMap0_bitSplitPrimaryBoundary (b : Bit) :
    collapseForwardMap0 (F := F) R
        (bitSplitPrimaryBoundary (F := F) R b) =
      originalBasisBoundary (F := F) R b := by
  classical
  ext c
  unfold collapseForwardMap0 linearMapOfBasisImages
  change (∑ e : Incidence R,
    bitSplitPrimaryBoundary (F := F) R b e •
      collapseForwardMap0Basis (F := F) R e) c = _
  rw [Finset.sum_apply]
  by_cases hcb : R c b
  · let e₀ : Incidence R := ⟨(c, b), hcb⟩
    rw [Finset.sum_eq_single e₀]
    · simp [bitSplitPrimaryBoundary, collapseForwardMap0Basis,
        originalBasisBoundary, e₀, hcb]
    · intro e _ hne
      by_cases heb : e.1.2 = b
      · have hec : e.1.1 ≠ c := by
          intro hec
          apply hne
          apply Subtype.ext
          exact Prod.ext hec heb
        simp [bitSplitPrimaryBoundary, collapseForwardMap0Basis,
          heb, hec]
      · simp [bitSplitPrimaryBoundary, heb]
    · simp
  · have hec (e : Incidence R) (heb : e.1.2 = b) : e.1.1 ≠ c := by
      intro hcheck
      apply hcb
      simpa [hcheck, heb] using e.2
    rw [show originalBasisBoundary (F := F) R b c = 0 by
      simp [originalBasisBoundary, hcb]]
    apply Finset.sum_eq_zero
    intro e _
    by_cases heb : e.1.2 = b
    · simp [bitSplitPrimaryBoundary, collapseForwardMap0Basis,
        heb, hec e heb]
    · simp [bitSplitPrimaryBoundary, heb]
omit [DecidableEq F] in
/-- The chosen inverse sends each original bit boundary to the boundary of
its rooted lift. -/
theorem collapseInverse_commutes_basis [CharP F 2]
    (h : HasNoIsolatedVertices R) (b : Bit) :
    bitSplitBoundary (F := F) R
        (collapseInverseMap1Basis (F := F) R b) =
      collapseInverseMap0 (F := F) R h
        (originalBasisBoundary (F := F) R b) := by
  have hd := LinearMap.congr_fun
    (collapseInverseForward_homotopy_degree0 (F := F) R h)
    (bitSplitPrimaryBoundary (F := F) R b)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hd
  rw [collapseForwardMap0_bitSplitPrimaryBoundary] at hd
  unfold collapseInverseMap1Basis
  rw [map_add, bitSplitBoundary_single]
  change bitSplitPrimaryBoundary (F := F) R b +
      bitSplitBoundary (F := F) R
        (collapseHomotopy0 (F := F) R
          (bitSplitPrimaryBoundary (F := F) R b)) =
    collapseInverseMap0 (F := F) R h
      (originalBasisBoundary (F := F) R b)
  rw [← hd, word_sub_eq_add_of_char_two]
  calc
    bitSplitPrimaryBoundary (F := F) R b +
          (collapseInverseMap0 (F := F) R h
              (originalBasisBoundary (F := F) R b) +
            bitSplitPrimaryBoundary (F := F) R b) =
        collapseInverseMap0 (F := F) R h
            (originalBasisBoundary (F := F) R b) +
          (bitSplitPrimaryBoundary (F := F) R b +
            bitSplitPrimaryBoundary (F := F) R b) := by abel
    _ = collapseInverseMap0 (F := F) R h
          (originalBasisBoundary (F := F) R b) := by
      have hdouble : bitSplitPrimaryBoundary (F := F) R b +
          bitSplitPrimaryBoundary (F := F) R b = 0 := by
        ext e
        exact add_self_eq_zero_of_char_two (F := F) _
      rw [hdouble]
      simp
omit [DecidableEq F] in
/-- The rooted lift is a chain map from the original Tanner complex to the
bit-combined complex. -/
theorem collapseInverse_commutes_boundary [CharP F 2]
    (h : HasNoIsolatedVertices R) :
    (bitSplitBoundary (F := F) R).comp
        (collapseInverseMap1 (F := F) R) =
      (collapseInverseMap0 (F := F) R h).comp
        (originalBoundary (F := F) R) := by
  refine linearMap_eq_of_single_one_eq (F := F)
    ((bitSplitBoundary (F := F) R).comp
      (collapseInverseMap1 (F := F) R))
    ((collapseInverseMap0 (F := F) R h).comp
      (originalBoundary (F := F) R)) ?_
  intro b
  rw [LinearMap.comp_apply, collapseInverseMap1_single,
    LinearMap.comp_apply, originalBoundary_single]
  exact collapseInverse_commutes_basis (F := F) R h b
omit [Fintype F] [DecidableEq F] in
theorem collapseForward_commutes_primaryBit (b : Bit) :
    originalBoundary (F := F) R
        (collapseForwardMap1Basis (F := F) R (Sum.inl b)) =
      collapseForwardMap0 (F := F) R
        (bitSplitBasisBoundary (F := F) R (Sum.inl b)) := by
  simp [collapseForwardMap1Basis, originalBoundary_single,
    bitSplitBasisBoundary, collapseForwardMap0_bitSplitPrimaryBoundary]
omit [Fintype F] [DecidableEq F] in
theorem collapseForward_commutes_auxiliaryBit [CharP F 2]
    (a : AuxiliaryBit R) :
    originalBoundary (F := F) R
        (collapseForwardMap1Basis (F := F) R (Sum.inr a)) =
      collapseForwardMap0 (F := F) R
        (bitSplitBasisBoundary (F := F) R (Sum.inr a)) := by
  classical
  simp only [collapseForwardMap1Basis, map_zero,
    bitSplitBasisBoundary, bitSplitAuxiliaryBoundary, map_add,
    collapseForwardMap0_single, collapseForwardMap0Basis]
  ext c
  change 0 = (Pi.single a.1 1 : Word F Check) c +
    (Pi.single a.1 1 : Word F Check) c
  exact (add_self_eq_zero_of_char_two (F := F) _).symm
omit [Fintype F] [DecidableEq F] in
theorem collapseForward_commutes_boundary [CharP F 2] :
    (originalBoundary (F := F) R).comp (collapseForwardMap1 (F := F) R) =
      (collapseForwardMap0 (F := F) R).comp (bitSplitBoundary (F := F) R) := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro i
  cases i with
  | inl b =>
      rw [LinearMap.comp_apply, collapseForwardMap1_single,
        LinearMap.comp_apply, bitSplitBoundary_single]
      exact collapseForward_commutes_primaryBit (F := F) R b
  | inr a =>
      rw [LinearMap.comp_apply, collapseForwardMap1_single,
        LinearMap.comp_apply, bitSplitBoundary_single]
      exact collapseForward_commutes_auxiliaryBit (F := F) R a
section SameUniverseCollapse
universe x
variable {F₀ Check₀ Bit₀ : Type x}
variable [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable [Fintype Check₀] [DecidableEq Check₀]
variable [Fintype Bit₀] [DecidableEq Bit₀]
variable (R₀ : Check₀ → Bit₀ → Prop) [DecidableRel R₀]
noncomputable def collapseForwardChainMap [CharP F₀ 2] :
    ThreeTermChainMap (bitSplitComplex (F₀ := F₀) R₀)
      (originalComplex (F₀ := F₀) R₀) where
  map0 := collapseForwardMap0 (F := F₀) R₀
  map1 := collapseForwardMap1 (F := F₀) R₀
  map2 := LinearMap.id
  commutes_boundary1 := collapseForward_commutes_boundary (F := F₀) R₀
  commutes_boundary2 := by
    simp [bitSplitComplex, originalComplex]
noncomputable def collapseInverseChainMap [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainMap (originalComplex (F₀ := F₀) R₀)
      (bitSplitComplex (F₀ := F₀) R₀) where
  map0 := collapseInverseMap0 (F := F₀) R₀ h
  map1 := collapseInverseMap1 (F := F₀) R₀
  map2 := LinearMap.id
  commutes_boundary1 := collapseInverse_commutes_boundary (F := F₀) R₀ h
  commutes_boundary2 := by
    simp [bitSplitComplex, originalComplex]
noncomputable def collapseInverseForwardHomotopy [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopy
      ((collapseInverseChainMap (F₀ := F₀) R₀ h).comp
        (collapseForwardChainMap (F₀ := F₀) R₀))
      (ThreeTermChainMap.id (bitSplitComplex (F₀ := F₀) R₀)) where
  homotopy0 := collapseHomotopy0 (F := F₀) R₀
  homotopy1 := 0
  degree0 := by
    simpa [collapseInverseChainMap, collapseForwardChainMap,
      bitSplitComplex] using
      collapseInverseForward_homotopy_degree0 (F := F₀) R₀ h
  degree1 := by
    simpa [collapseInverseChainMap, collapseForwardChainMap,
      bitSplitComplex] using
      collapseInverseForward_homotopy_degree1 (F := F₀) R₀
  degree2 := by
    simp [collapseInverseChainMap, collapseForwardChainMap,
      bitSplitComplex]
noncomputable def collapseForwardInverseHomotopy [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopy
      ((collapseForwardChainMap (F₀ := F₀) R₀).comp
        (collapseInverseChainMap (F₀ := F₀) R₀ h))
      (ThreeTermChainMap.id (originalComplex (F₀ := F₀) R₀)) where
  homotopy0 := 0
  homotopy1 := 0
  degree0 := by
    simp only [ThreeTermChainMap.comp_map0, ThreeTermChainMap.id_map0]
    change (collapseForwardMap0 (F := F₀) R₀).comp
        (collapseInverseMap0 (F := F₀) R₀ h) - LinearMap.id = _
    rw [collapseForwardMap0_comp_collapseInverseMap0]
    simp
  degree1 := by
    simp only [ThreeTermChainMap.comp_map1, ThreeTermChainMap.id_map1]
    change (collapseForwardMap1 (F := F₀) R₀).comp
        (collapseInverseMap1 (F := F₀) R₀) - LinearMap.id = _
    rw [collapseForwardMap1_comp_collapseInverseMap1]
    simp
  degree2 := by
    simp [collapseForwardChainMap, collapseInverseChainMap,
      originalComplex]
noncomputable def collapseHomotopyEquiv [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopyEquiv
      (bitSplitComplex (F₀ := F₀) R₀)
      (originalComplex (F₀ := F₀) R₀) where
  forward := collapseForwardChainMap (F₀ := F₀) R₀
  inverse := collapseInverseChainMap (F₀ := F₀) R₀ h
  inverse_forward := collapseInverseForwardHomotopy (F₀ := F₀) R₀ h
  forward_inverse := collapseForwardInverseHomotopy (F₀ := F₀) R₀ h
noncomputable def classicalWeightReductionHomotopy0 :
    Word F₀ (WeightReducedCheck R₀) →ₗ[F₀]
      Word F₀ (WeightReducedBit R₀) :=
  (combineInverseMap1 (F := F₀) R₀).comp
      ((collapseHomotopy0 (F := F₀) R₀).comp
        (combineForwardMap0 (F := F₀) R₀)) +
    combineHomotopy0 (F := F₀) R₀
omit [DecidableEq F₀] in
/-- Degree-zero equation for the composite classical weight-reduction
homotopy. -/
theorem classicalWeightReduction_homotopy_degree0 [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ((combineInverseMap0 (F := F₀) R₀).comp
        (collapseInverseMap0 (F := F₀) R₀ h)).comp
          ((collapseForwardMap0 (F := F₀) R₀).comp
            (combineForwardMap0 (F := F₀) R₀)) - LinearMap.id =
      (boundary (F := F₀) R₀).comp
        (classicalWeightReductionHomotopy0 (F₀ := F₀) R₀) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply]
  rw [word_sub_eq_add_of_char_two]
  let y := combineForwardMap0 (F := F₀) R₀ x
  let u := combineInverseMap0 (F := F₀) R₀ y
  let z := collapseHomotopy0 (F := F₀) R₀ y
  have hc := LinearMap.congr_fun
    (collapseInverseForward_homotopy_degree0 (F := F₀) R₀ h) y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hc
  rw [word_sub_eq_add_of_char_two] at hc
  have hcmap := congrArg (combineInverseMap0 (F := F₀) R₀) hc
  simp only [map_add] at hcmap
  have hb := LinearMap.congr_fun
    (combineInverseForward_homotopy_degree0 (F := F₀) R₀) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hb
  rw [word_sub_eq_add_of_char_two] at hb
  have hchain := LinearMap.congr_fun
    (combineInverse_commutes_boundary (F := F₀) R₀) z
  simp only [LinearMap.comp_apply] at hchain
  have hdouble : u + u = 0 :=
    word_add_self_eq_zero_of_char_two (F := F₀) u
  change combineInverseMap0 (F := F₀) R₀
          (collapseInverseMap0 (F := F₀) R₀ h
            (collapseForwardMap0 (F := F₀) R₀ y)) + x =
    boundary (F := F₀) R₀
      (combineInverseMap1 (F := F₀) R₀ z +
        combineHomotopy0 (F := F₀) R₀ x)
  calc
    combineInverseMap0 (F := F₀) R₀
            (collapseInverseMap0 (F := F₀) R₀ h
              (collapseForwardMap0 (F := F₀) R₀ y)) + x =
        (combineInverseMap0 (F := F₀) R₀
              (collapseInverseMap0 (F := F₀) R₀ h
                (collapseForwardMap0 (F := F₀) R₀ y)) + x) + 0 := by simp
    _ = (combineInverseMap0 (F := F₀) R₀
            (collapseInverseMap0 (F := F₀) R₀ h
              (collapseForwardMap0 (F := F₀) R₀ y)) + x) +
          (u + u) := by rw [hdouble]
    _ = (combineInverseMap0 (F := F₀) R₀
            (collapseInverseMap0 (F := F₀) R₀ h
              (collapseForwardMap0 (F := F₀) R₀ y)) + u) +
          (u + x) := by abel
    _ = combineInverseMap0 (F := F₀) R₀
            (bitSplitBoundary (F := F₀) R₀ z) +
          boundary (F := F₀) R₀
            (combineHomotopy0 (F := F₀) R₀ x) := by
      rw [← hcmap, ← hb]
    _ = boundary (F := F₀) R₀
            (combineInverseMap1 (F := F₀) R₀ z) +
          boundary (F := F₀) R₀
            (combineHomotopy0 (F := F₀) R₀ x) := by rw [hchain]
    _ = boundary (F := F₀) R₀
          (combineInverseMap1 (F := F₀) R₀ z +
            combineHomotopy0 (F := F₀) R₀ x) := by rw [map_add]
omit [Fintype F₀] [DecidableEq F₀] in
/-- Degree-one equation for the composite classical weight-reduction
homotopy. -/
theorem classicalWeightReduction_homotopy_degree1 [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ((combineInverseMap1 (F := F₀) R₀).comp
        (collapseInverseMap1 (F := F₀) R₀)).comp
          ((collapseForwardMap1 (F := F₀) R₀).comp
            (combineForwardMap1 (F := F₀) R₀ h)) - LinearMap.id =
      (classicalWeightReductionHomotopy0 (F₀ := F₀) R₀).comp
        (boundary (F := F₀) R₀) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply]
  rw [word_sub_eq_add_of_char_two]
  let y := combineForwardMap1 (F := F₀) R₀ h x
  let u := combineInverseMap1 (F := F₀) R₀ y
  let z := collapseHomotopy0 (F := F₀) R₀
    (bitSplitBoundary (F := F₀) R₀ y)
  have hc := LinearMap.congr_fun
    (collapseInverseForward_homotopy_degree1 (F := F₀) R₀) y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hc
  rw [word_sub_eq_add_of_char_two] at hc
  have hcmap := congrArg (combineInverseMap1 (F := F₀) R₀) hc
  simp only [map_add] at hcmap
  have hb := LinearMap.congr_fun
    (combineInverseForward_homotopy_degree1 (F := F₀) R₀ h) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hb
  rw [word_sub_eq_add_of_char_two] at hb
  have hforward := LinearMap.congr_fun
    (combineForward_commutes_boundary (F := F₀) R₀ h) x
  simp only [LinearMap.comp_apply] at hforward
  have hdouble : u + u = 0 :=
    word_add_self_eq_zero_of_char_two (F := F₀) u
  change combineInverseMap1 (F := F₀) R₀
          (collapseInverseMap1 (F := F₀) R₀
            (collapseForwardMap1 (F := F₀) R₀ y)) + x =
    combineInverseMap1 (F := F₀) R₀
        (collapseHomotopy0 (F := F₀) R₀
          (combineForwardMap0 (F := F₀) R₀
            (boundary (F := F₀) R₀ x))) +
      combineHomotopy0 (F := F₀) R₀
        (boundary (F := F₀) R₀ x)
  calc
    combineInverseMap1 (F := F₀) R₀
            (collapseInverseMap1 (F := F₀) R₀
              (collapseForwardMap1 (F := F₀) R₀ y)) + x =
        (combineInverseMap1 (F := F₀) R₀
              (collapseInverseMap1 (F := F₀) R₀
                (collapseForwardMap1 (F := F₀) R₀ y)) + x) + 0 := by simp
    _ = (combineInverseMap1 (F := F₀) R₀
            (collapseInverseMap1 (F := F₀) R₀
              (collapseForwardMap1 (F := F₀) R₀ y)) + x) +
          (u + u) := by rw [hdouble]
    _ = (combineInverseMap1 (F := F₀) R₀
            (collapseInverseMap1 (F := F₀) R₀
              (collapseForwardMap1 (F := F₀) R₀ y)) + u) +
          (u + x) := by abel
    _ = combineInverseMap1 (F := F₀) R₀ z +
          combineHomotopy0 (F := F₀) R₀
            (boundary (F := F₀) R₀ x) := by
      rw [← hcmap, ← hb]
    _ = combineInverseMap1 (F := F₀) R₀
            (collapseHomotopy0 (F := F₀) R₀
              (combineForwardMap0 (F := F₀) R₀
                (boundary (F := F₀) R₀ x))) +
          combineHomotopy0 (F := F₀) R₀
            (boundary (F := F₀) R₀ x) := by rw [← hforward]
noncomputable def classicalWeightReductionForwardChainMap [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainMap (weightReducedComplex (F₀ := F₀) R₀)
      (originalComplex (F₀ := F₀) R₀) :=
  (collapseForwardChainMap (F₀ := F₀) R₀).comp
    (combineForwardChainMap (F₀ := F₀) R₀ h)
noncomputable def classicalWeightReductionInverseChainMap [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainMap (originalComplex (F₀ := F₀) R₀)
      (weightReducedComplex (F₀ := F₀) R₀) :=
  (combineInverseChainMap (F₀ := F₀) R₀).comp
    (collapseInverseChainMap (F₀ := F₀) R₀ h)
noncomputable def classicalWeightReductionInverseForwardHomotopy
    [CharP F₀ 2] (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopy
      ((classicalWeightReductionInverseChainMap (F₀ := F₀) R₀ h).comp
        (classicalWeightReductionForwardChainMap (F₀ := F₀) R₀ h))
      (ThreeTermChainMap.id (weightReducedComplex (F₀ := F₀) R₀)) where
  homotopy0 := classicalWeightReductionHomotopy0 (F₀ := F₀) R₀
  homotopy1 := 0
  degree0 := by
    simpa [classicalWeightReductionInverseChainMap,
      classicalWeightReductionForwardChainMap,
      ThreeTermChainMap.comp, combineInverseChainMap, collapseInverseChainMap,
      collapseForwardChainMap, combineForwardChainMap, weightReducedComplex] using
      classicalWeightReduction_homotopy_degree0 (F₀ := F₀) R₀ h
  degree1 := by
    simpa [classicalWeightReductionInverseChainMap,
      classicalWeightReductionForwardChainMap,
      ThreeTermChainMap.comp, combineInverseChainMap, collapseInverseChainMap,
      collapseForwardChainMap, combineForwardChainMap, weightReducedComplex] using
      classicalWeightReduction_homotopy_degree1 (F₀ := F₀) R₀ h
  degree2 := by
    apply LinearMap.ext
    intro x
    ext i
    exact Fin.elim0 i
noncomputable def classicalWeightReductionForwardInverseHomotopy
    [CharP F₀ 2] (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopy
      ((classicalWeightReductionForwardChainMap (F₀ := F₀) R₀ h).comp
        (classicalWeightReductionInverseChainMap (F₀ := F₀) R₀ h))
      (ThreeTermChainMap.id (originalComplex (F₀ := F₀) R₀)) where
  homotopy0 := 0
  homotopy1 := 0
  degree0 := by
    apply LinearMap.ext
    intro x
    simp only [classicalWeightReductionForwardChainMap,
      classicalWeightReductionInverseChainMap,
      ThreeTermChainMap.comp_map0, ThreeTermChainMap.id_map0,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply, map_zero, originalComplex]
    change collapseForwardMap0 (F := F₀) R₀
          (combineForwardMap0 (F := F₀) R₀
            (combineInverseMap0 (F := F₀) R₀
              (collapseInverseMap0 (F := F₀) R₀ h x))) - x = 0
    have hcombine := LinearMap.congr_fun
      (combineForwardMap0_comp_combineInverseMap0 (F := F₀) R₀)
      (collapseInverseMap0 (F := F₀) R₀ h x)
    have hcollapse := LinearMap.congr_fun
      (collapseForwardMap0_comp_collapseInverseMap0 (F := F₀) R₀ h) x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcombine hcollapse
    rw [hcombine, hcollapse]
    simp
  degree1 := by
    apply LinearMap.ext
    intro x
    simp only [classicalWeightReductionForwardChainMap,
      classicalWeightReductionInverseChainMap,
      ThreeTermChainMap.comp_map1, ThreeTermChainMap.id_map1,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.add_apply, LinearMap.zero_apply, map_zero, zero_add,
      originalComplex]
    change collapseForwardMap1 (F := F₀) R₀
          (combineForwardMap1 (F := F₀) R₀ h
            (combineInverseMap1 (F := F₀) R₀
              (collapseInverseMap1 (F := F₀) R₀ x))) - x = 0
    have hcombine := LinearMap.congr_fun
      (combineForwardMap1_comp_combineInverseMap1 (F := F₀) R₀ h)
      (collapseInverseMap1 (F := F₀) R₀ x)
    have hcollapse := LinearMap.congr_fun
      (collapseForwardMap1_comp_collapseInverseMap1 (F := F₀) R₀) x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcombine hcollapse
    rw [hcombine, hcollapse]
    simp
  degree2 := by
    apply LinearMap.ext
    intro x
    ext i
    exact Fin.elim0 i
noncomputable def classicalWeightReductionHomotopyEquiv [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopyEquiv
      (weightReducedComplex (F₀ := F₀) R₀)
      (originalComplex (F₀ := F₀) R₀) where
  forward := classicalWeightReductionForwardChainMap (F₀ := F₀) R₀ h
  inverse := classicalWeightReductionInverseChainMap (F₀ := F₀) R₀ h
  inverse_forward :=
    classicalWeightReductionInverseForwardHomotopy (F₀ := F₀) R₀ h
  forward_inverse :=
    classicalWeightReductionForwardInverseHomotopy (F₀ := F₀) R₀ h
end SameUniverseCollapse
end QEC.Coding.ClassicalWeightReduction


