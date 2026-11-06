-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_Classical_Homotopy
-- name    : QEC_Coding_CodeReduction_Classical_Homotopy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:49:52.422625+00:00
-- url     : https://prove2.me/theorems/a136cff9-2fea-4320-b888-d2a2f6819d26
-- title:
--   Homotopy
-- statement:
--   Definitions and structural lemmas for Homotopy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Homotopy.lean

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_boundary_single
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
structure HasNoIsolatedVertices : Prop where
  bit_nonempty : ∀ b : Bit, Nonempty (BitNeighbor R b)
  check_nonempty : ∀ c : Check, Nonempty (CheckNeighbor R c)
omit [Fintype F] [DecidableEq F] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit] in
theorem HasNoIsolatedVertices.bit_card_pos
    (h : HasNoIsolatedVertices R) (b : Bit) :
    0 < Fintype.card (BitNeighbor R b) := by
  exact Fintype.card_pos_iff.mpr (h.bit_nonempty b)
omit [Fintype F] [DecidableEq F] [Fintype Check]
    [DecidableEq Check] [DecidableEq Bit] in
theorem HasNoIsolatedVertices.check_card_pos
    (h : HasNoIsolatedVertices R) (c : Check) :
    0 < Fintype.card (CheckNeighbor R c) := by
  exact Fintype.card_pos_iff.mpr (h.check_nonempty c)
def bitRootPosition (h : HasNoIsolatedVertices R) (b : Bit) :
    Fin (Fintype.card (BitNeighbor R b)) :=
  ⟨0, h.bit_card_pos R b⟩
def checkRootPosition (h : HasNoIsolatedVertices R) (c : Check) :
    Fin (Fintype.card (CheckNeighbor R c)) :=
  ⟨0, h.check_card_pos R c⟩
abbrev BitSplitBit := Bit ⊕ AuxiliaryBit R
abbrev BitSplitCheck := Incidence R
noncomputable def bitSplitPrimaryBoundary (b : Bit) :
    Word F (BitSplitCheck R) :=
  fun e => if e.1.2 = b then 1 else 0
noncomputable def bitSplitAuxiliaryBoundary (a : AuxiliaryBit R) :
    Word F (BitSplitCheck R) :=
  Pi.single (checkIncidenceAt R a.1 (pathLeft a.2)) 1 +
    Pi.single (checkIncidenceAt R a.1 (pathRight a.2)) 1
noncomputable def bitSplitBasisBoundary : BitSplitBit R →
    Word F (BitSplitCheck R)
  | Sum.inl b => bitSplitPrimaryBoundary (F := F) R b
  | Sum.inr a => bitSplitAuxiliaryBoundary (F := F) R a
noncomputable def bitSplitBoundary :
    Word F (BitSplitBit R) →ₗ[F] Word F (BitSplitCheck R) :=
  linearMapOfBasisImages (F := F) (bitSplitBasisBoundary (F := F) R)
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem bitSplitBoundary_single (i : BitSplitBit R) :
    bitSplitBoundary (F := F) R (Pi.single i 1) =
      bitSplitBasisBoundary (F := F) R i := by
  exact linearMapOfBasisImages_single (F := F) _ _
noncomputable def bitCheckSuffix (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    Word F (BitSplitCheck R) :=
  fun e => if e.1.2 = b ∧ j.1 < (bitPosition R e).1 then 1 else 0
noncomputable def combineForwardMap1Basis (h : HasNoIsolatedVertices R) :
    WeightReducedBit R → Word F (BitSplitBit R)
  | Sum.inl e =>
      if bitPosition R e = bitRootPosition R h e.1.2 then
        Pi.single (Sum.inl e.1.2) 1
      else 0
  | Sum.inr a => Pi.single (Sum.inr a) 1
noncomputable def combineForwardMap0Basis :
    WeightReducedCheck R → Word F (BitSplitCheck R)
  | Sum.inl e => Pi.single e 1
  | Sum.inr a => bitCheckSuffix (F := F) R a.1 a.2
noncomputable def allPrimaryBitCopies (b : Bit) :
    Word F (WeightReducedBit R) :=
  fun i =>
    match i with
    | Sum.inl e => if e.1.2 = b then 1 else 0
    | Sum.inr _ => 0
noncomputable def combineInverseMap1Basis :
    BitSplitBit R → Word F (WeightReducedBit R)
  | Sum.inl b => allPrimaryBitCopies (F := F) R b
  | Sum.inr a => Pi.single (Sum.inr a) 1
noncomputable def combineInverseMap0Basis (e : BitSplitCheck R) :
    Word F (WeightReducedCheck R) :=
  Pi.single (Sum.inl e) 1
noncomputable def combineForwardMap1 (h : HasNoIsolatedVertices R) :
    Word F (WeightReducedBit R) →ₗ[F] Word F (BitSplitBit R) :=
  linearMapOfBasisImages (F := F) (combineForwardMap1Basis (F := F) R h)
noncomputable def combineForwardMap0 :
    Word F (WeightReducedCheck R) →ₗ[F] Word F (BitSplitCheck R) :=
  linearMapOfBasisImages (F := F) (combineForwardMap0Basis (F := F) R)
noncomputable def combineInverseMap1 :
    Word F (BitSplitBit R) →ₗ[F] Word F (WeightReducedBit R) :=
  linearMapOfBasisImages (F := F) (combineInverseMap1Basis (F := F) R)
noncomputable def combineInverseMap0 :
    Word F (BitSplitCheck R) →ₗ[F] Word F (WeightReducedCheck R) :=
  linearMapOfBasisImages (F := F) (combineInverseMap0Basis (F := F) R)
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineForwardMap1_single (h : HasNoIsolatedVertices R)
    (i : WeightReducedBit R) :
    combineForwardMap1 (F := F) R h (Pi.single i 1) =
      combineForwardMap1Basis (F := F) R h i := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineForwardMap0_single (q : WeightReducedCheck R) :
    combineForwardMap0 (F := F) R (Pi.single q 1) =
      combineForwardMap0Basis (F := F) R q := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineInverseMap1_single (i : BitSplitBit R) :
    combineInverseMap1 (F := F) R (Pi.single i 1) =
      combineInverseMap1Basis (F := F) R i := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineInverseMap0_single (q : BitSplitCheck R) :
    combineInverseMap0 (F := F) R (Pi.single q 1) =
      combineInverseMap0Basis (F := F) R q := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
theorem combineForwardMap1_allPrimaryBitCopies
    (h : HasNoIsolatedVertices R) (b : Bit) :
    combineForwardMap1 (F := F) R h (allPrimaryBitCopies (F := F) R b) =
      Pi.single (Sum.inl b) 1 := by
  classical
  unfold combineForwardMap1 linearMapOfBasisImages
  change (∑ i : WeightReducedBit R,
    allPrimaryBitCopies (F := F) R b i • combineForwardMap1Basis (F := F) R h i) = _
  rw [Finset.sum_eq_single
    (Sum.inl (bitIncidenceAt R b (bitRootPosition R h b)))]
  · simp only [allPrimaryBitCopies, combineForwardMap1Basis]
    rw [bitPosition_bitIncidenceAt R b (bitRootPosition R h b)]
    simp only [bitIncidenceAt, ite_true, one_smul]
    exact if_pos rfl
  · intro i _ hne
    cases i with
    | inr a => simp [allPrimaryBitCopies]
    | inl e =>
        by_cases heb : e.1.2 = b
        · have hpos : bitPosition R e ≠ bitRootPosition R h e.1.2 := by
            intro hp
            apply hne
            apply congrArg Sum.inl
            calc
              e = bitIncidenceAt R e.1.2 (bitPosition R e) :=
                  (bitIncidenceAt_bitPosition R e).symm
              _ = bitIncidenceAt R e.1.2 (bitRootPosition R h e.1.2) := by
                  rw [hp]
              _ = bitIncidenceAt R b (bitRootPosition R h b) := by
                  cases heb
                  rfl
          simp [allPrimaryBitCopies, combineForwardMap1Basis, heb, hpos]
        · simp [allPrimaryBitCopies, heb]
  · simp
omit [Fintype F] [DecidableEq F] in
theorem linearMap_eq_of_single_one_eq
    {Source Target : Type*} [Fintype Source] [DecidableEq Source]
    [AddCommGroup Target] [Module F Target]
    (f g : Word F Source →ₗ[F] Target)
    (h : ∀ i : Source, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearMap.ext
  intro x
  calc
    f x = f (∑ i : Source, Pi.single i (x i)) := by
      rw [word_eq_sum_single (F := F) x]
    _ = ∑ i : Source, f (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i : Source, g (Pi.single i (x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hs : (Pi.single i (x i) : Word F Source) =
          x i • Pi.single i (1 : F) := by
        ext j
        simp [Pi.single_apply]
      rw [hs, f.map_smul, g.map_smul, h i]
    _ = g (∑ i : Source, Pi.single i (x i)) := by rw [map_sum]
    _ = g x := by rw [word_eq_sum_single (F := F) x]
omit [Fintype F] [DecidableEq F] in
/-- On degree one, combining after splitting is strictly the identity on the
bit-combined intermediate complex. -/
theorem combineForwardMap1_comp_combineInverseMap1
    (h : HasNoIsolatedVertices R) :
    (combineForwardMap1 (F := F) R h).comp
        (combineInverseMap1 (F := F) R) = LinearMap.id := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro i
  cases i with
  | inl b =>
      rw [LinearMap.comp_apply, combineInverseMap1_single, LinearMap.id_apply]
      change combineForwardMap1 (F := F) R h
        (allPrimaryBitCopies (F := F) R b) = Pi.single (Sum.inl b) 1
      exact combineForwardMap1_allPrimaryBitCopies (F := F) R h b
  | inr a =>
      simp [combineInverseMap1Basis, combineForwardMap1Basis]
omit [Fintype F] [DecidableEq F] in
/-- On degree zero, combining after splitting is strictly the identity. -/
theorem combineForwardMap0_comp_combineInverseMap0 :
    (combineForwardMap0 (F := F) R).comp
        (combineInverseMap0 (F := F) R) = LinearMap.id := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro e
  simp [combineInverseMap0Basis, combineForwardMap0Basis]
omit [Fintype F] [DecidableEq F] in
theorem add_self_eq_zero_of_char_two [CharP F 2] (a : F) : a + a = 0 := by
  have htwo : (2 : F) = 0 :=
    (CharP.cast_eq_zero_iff F 2 2).mpr (dvd_refl 2)
  rw [← two_mul, htwo, zero_mul]
omit [Fintype F] [DecidableEq F] in
theorem neg_eq_self_of_char_two [CharP F 2] (a : F) : -a = a := by
  exact (eq_neg_of_add_eq_zero_left (add_self_eq_zero_of_char_two (F := F) a)).symm
omit [Fintype F] [DecidableEq F] in
theorem word_sub_eq_add_of_char_two [CharP F 2]
    {Index : Type*} (x y : Word F Index) : x - y = x + y := by
  ext i
  simp [sub_eq_add_neg, neg_eq_self_of_char_two (F := F)]
noncomputable def pathVertexSuffix {n : Nat} (j : Fin (n - 1)) :
    Word F (Fin n) :=
  fun i => if j.1 < i.1 then 1 else 0
noncomputable def optionalPathVertexSuffix {n : Nat}
    (j : Option (Fin (n - 1))) : Word F (Fin n) :=
  match j with
  | none => 0
  | some edge => pathVertexSuffix (F := F) edge
omit [Fintype F] [DecidableEq F] in
/-- The rooted cell-combining identity on a finite path over characteristic
two: a vertex, the suffix after its preceding edge, and the suffix after its
following edge sum to the all-ones word only at the root and to zero elsewhere. -/
theorem path_vertex_add_adjacent_suffixes [CharP F 2]
    {n : Nat} (i : Fin n) :
    Pi.single i 1 + optionalPathVertexSuffix (F := F) (pathPrevious i) +
        optionalPathVertexSuffix (F := F) (pathNext i) =
      if i.1 = 0 then (fun _ => 1) else (0 : Word F (Fin n)) := by
  classical
  ext k
  unfold optionalPathVertexSuffix pathVertexSuffix pathPrevious pathNext
  by_cases hi : i.1 = 0
  · have hiprev : ¬0 < i.1 := by omega
    by_cases hinext : i.1 + 1 < n
    · have hn : 1 < n := by omega
      by_cases hki : k = i
      · subst k
        simp [hi, hn]
      · have hik : i.1 < k.1 := by omega
        have hkzero : k.1 ≠ 0 := by omega
        simp [hi, hn, hki, hkzero]
    · have hki : k = i := by
        apply Fin.ext
        omega
      have hn : ¬1 < n := by omega
      subst k
      simp [hi, hn]
  · have hipos : 0 < i.1 := by omega
    by_cases hinext : i.1 + 1 < n
    · by_cases hki : k = i
      · subst k
        have hprev : i.1 - 1 < i.1 := by omega
        simp [hi, hipos, hinext, hprev,
          add_self_eq_zero_of_char_two (F := F)]
      · by_cases hlt : k.1 < i.1
        · have hprev : ¬i.1 - 1 < k.1 := by omega
          have hnext : ¬i.1 < k.1 := by omega
          have hleFin : k ≤ i := by omega
          simp [hi, hipos, hinext, hki, hprev, hleFin]
        · have hik : i.1 < k.1 := by omega
          have hprev : i.1 - 1 < k.1 := by omega
          have hikFin : i < k := by omega
          simp [hi, hipos, hinext, hki, hprev, hikFin,
            add_self_eq_zero_of_char_two (F := F)]
    · have hilast : i.1 + 1 = n := by omega
      by_cases hki : k = i
      · subst k
        have hprev : i.1 - 1 < i.1 := by omega
        simp [hi, hipos, hinext, hprev,
          add_self_eq_zero_of_char_two (F := F)]
      · have hlt : k.1 < i.1 := by omega
        have hprev : ¬i.1 - 1 < k.1 := by omega
        simp [hi, hipos, hinext, hki, hprev]
omit [Fintype F] [DecidableEq F] in
/-- The boundary of a suffix of path vertices is the single edge at which
the suffix starts. -/
theorem pathVertexSuffix_left_add_right [CharP F 2]
    {n : Nat} (j k : Fin (n - 1)) :
    pathVertexSuffix (F := F) j (pathLeft k) +
        pathVertexSuffix (F := F) j (pathRight k) =
      (Pi.single j 1 : Word F (Fin (n - 1))) k := by
  classical
  by_cases hkj : k = j
  · subst k
    simp [pathVertexSuffix, pathLeft, pathRight]
  · have hjk : j ≠ k := fun h => hkj h.symm
    have hval : k.1 < j.1 ∨ j.1 < k.1 := by
      omega
    rcases hval with hlt | hgt
    · have hright : ¬j.1 < k.1 + 1 := by omega
      have hle : k ≤ j := by omega
      simp [pathVertexSuffix, pathLeft, pathRight, hkj, hright, hle]
    · have hle : j.1 ≤ k.1 := Nat.le_of_lt hgt
      simp [pathVertexSuffix, pathLeft, pathRight, hkj, hgt, hle,
        add_self_eq_zero_of_char_two (F := F)]
omit [Fintype F] [DecidableEq F] [DecidableEq Check] [Fintype Bit] in
@[simp]
theorem bitCheckSuffix_bitIncidenceAt (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1))
    (i : Fin (Fintype.card (BitNeighbor R b))) :
    bitCheckSuffix (F := F) R b j (bitIncidenceAt R b i) =
      pathVertexSuffix (F := F) j i := by
  unfold bitCheckSuffix pathVertexSuffix
  rw [bitPosition_bitIncidenceAt R b i]
  simp [bitIncidenceAt]
abbrev BitPositionSigma :=
  Σ b : Bit, Fin (Fintype.card (BitNeighbor R b))
noncomputable def incidenceBitPosition (e : Incidence R) : BitPositionSigma R :=
  ⟨e.1.2, bitPosition R e⟩
noncomputable def incidenceAtBitPosition : BitPositionSigma R → Incidence R
  | ⟨b, i⟩ => bitIncidenceAt R b i
omit [Fintype F] [DecidableEq F] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit] in
@[simp]
theorem incidenceAtBitPosition_incidenceBitPosition (e : Incidence R) :
    incidenceAtBitPosition R (incidenceBitPosition R e) = e := by
  exact bitIncidenceAt_bitPosition R e
omit [Fintype F] [DecidableEq F] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit] in
theorem incidenceBitPosition_injective :
    Function.Injective (incidenceBitPosition R) := by
  intro e e' h
  calc
    e = incidenceAtBitPosition R (incidenceBitPosition R e) :=
      (incidenceAtBitPosition_incidenceBitPosition R e).symm
    _ = incidenceAtBitPosition R (incidenceBitPosition R e') := by rw [h]
    _ = e' := incidenceAtBitPosition_incidenceBitPosition R e'
omit [Fintype F] [DecidableEq F] [Fintype Bit] in
theorem single_incidence_apply_eq_single_bitPosition
    (e e' : Incidence R) :
    (Pi.single e 1 : Word F (Incidence R)) e' =
      (Pi.single (incidenceBitPosition R e) 1 : Word F (BitPositionSigma R))
        (incidenceBitPosition R e') := by
  classical
  by_cases heq : e = e'
  · subst e'
    simp
  · have hpos : incidenceBitPosition R e ≠ incidenceBitPosition R e' := by
      exact fun h => heq (incidenceBitPosition_injective R h)
    simp [heq, hpos]
noncomputable def bitFiberIndicator (b : Bit) : Word F (BitPositionSigma R) :=
  fun s => if s.1 = b then 1 else 0
noncomputable def bitFiberSuffix (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    Word F (BitPositionSigma R) :=
  fun s => if s.1 = b ∧ j.1 < s.2.1 then 1 else 0
noncomputable def optionalBitFiberSuffix (b : Bit)
    (j : Option (Fin (Fintype.card (BitNeighbor R b) - 1))) :
    Word F (BitPositionSigma R) :=
  match j with
  | none => 0
  | some edge => bitFiberSuffix (F := F) R b edge
omit [Fintype F] [DecidableEq F] [DecidableEq Check] [Fintype Bit] in
@[simp]
theorem optionalBitFiberSuffix_apply_same (b : Bit)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (k : Fin (Fintype.card (BitNeighbor R b))) :
    optionalBitFiberSuffix (F := F) R b o ⟨b, k⟩ =
      optionalPathVertexSuffix (F := F) o k := by
  cases o <;> simp [optionalBitFiberSuffix, optionalPathVertexSuffix,
    bitFiberSuffix, pathVertexSuffix]
omit [Fintype F] [DecidableEq F] [DecidableEq Check] [Fintype Bit] in
theorem optionalBitFiberSuffix_apply_of_ne {b b' : Bit} (hb : b' ≠ b)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (k : Fin (Fintype.card (BitNeighbor R b'))) :
    optionalBitFiberSuffix (F := F) R b o ⟨b', k⟩ = 0 := by
  cases o <;> simp [optionalBitFiberSuffix, bitFiberSuffix, hb]
omit [Fintype F] [DecidableEq F] [DecidableEq Check] [Fintype Bit] in
theorem bitFiber_vertex_add_adjacent_suffixes [CharP F 2]
    (b : Bit) (i : Fin (Fintype.card (BitNeighbor R b))) :
    Pi.single (⟨b, i⟩ : BitPositionSigma R) 1 +
        optionalBitFiberSuffix (F := F) R b (pathPrevious i) +
        optionalBitFiberSuffix (F := F) R b (pathNext i) =
      if i.1 = 0 then bitFiberIndicator (F := F) R b
      else (0 : Word F (BitPositionSigma R)) := by
  classical
  ext s
  rcases s with ⟨b', k⟩
  by_cases hb : b' = b
  · subst b'
    by_cases hi : i.1 = 0
    · simpa [hi, optionalBitFiberSuffix_apply_same, bitFiberIndicator,
        Pi.single_apply] using
        congrFun (path_vertex_add_adjacent_suffixes (F := F) i) k
    · simpa [hi, optionalBitFiberSuffix_apply_same, bitFiberIndicator,
        Pi.single_apply] using
        congrFun (path_vertex_add_adjacent_suffixes (F := F) i) k
  · simp only [Pi.add_apply]
    rw [optionalBitFiberSuffix_apply_of_ne (F := F) R hb,
      optionalBitFiberSuffix_apply_of_ne (F := F) R hb]
    by_cases hi : i.1 = 0 <;>
      simp [hi, bitFiberIndicator, hb]
omit [Fintype F] [DecidableEq F] [DecidableEq Check] [Fintype Bit] in
@[simp]
theorem bitFiberSuffix_incidenceBitPosition (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) (e : Incidence R) :
    bitFiberSuffix (F := F) R b j (incidenceBitPosition R e) =
      bitCheckSuffix (F := F) R b j e := by
  rfl
omit [Fintype F] [DecidableEq F] [DecidableEq Check] [Fintype Bit] in
@[simp]
theorem bitFiberIndicator_incidenceBitPosition (b : Bit) (e : Incidence R) :
    bitFiberIndicator (F := F) R b (incidenceBitPosition R e) =
      bitSplitPrimaryBoundary (F := F) R b e := by
  rfl
noncomputable def optionalBitCheckSuffix (b : Bit)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1))) :
    Word F (BitSplitCheck R) :=
  match o with
  | none => 0
  | some edge => bitCheckSuffix (F := F) R b edge
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineForwardMap0_optionalAuxiliaryCheck (b : Bit)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1))) :
    combineForwardMap0 (F := F) R
        (optionalSingle (F := F) (o.map (auxiliaryCheckIndex R b))) =
      optionalBitCheckSuffix (F := F) R b o := by
  cases o <;> simp [optionalSingle, optionalBitCheckSuffix,
    combineForwardMap0Basis, auxiliaryCheckIndex]
omit [Fintype F] [DecidableEq F] [DecidableEq Check] [Fintype Bit] in
@[simp]
theorem optionalBitFiberSuffix_incidenceBitPosition (b : Bit)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (e : Incidence R) :
    optionalBitFiberSuffix (F := F) R b o (incidenceBitPosition R e) =
      optionalBitCheckSuffix (F := F) R b o e := by
  cases o <;> rfl
omit [Fintype F] [DecidableEq F] in
theorem combineForward_commutes_primaryBit [CharP F 2]
    (h : HasNoIsolatedVertices R) (e : Incidence R) :
    combineForwardMap0 (F := F) R (primaryBitBoundary (F := F) R e) =
      bitSplitBoundary (F := F) R
        (combineForwardMap1Basis (F := F) R h (Sum.inl e)) := by
  classical
  ext e'
  have hpath := congrFun
    (bitFiber_vertex_add_adjacent_suffixes (F := F) R e.1.2 (bitPosition R e))
    (incidenceBitPosition R e')
  simp only [Pi.add_apply] at hpath
  change ((Pi.single (incidenceBitPosition R e) (1 : F) :
      Word F (BitPositionSigma R)) (incidenceBitPosition R e') +
    optionalBitFiberSuffix (F := F) R e.1.2 (pathPrevious (bitPosition R e))
      (incidenceBitPosition R e') +
    optionalBitFiberSuffix (F := F) R e.1.2 (pathNext (bitPosition R e))
      (incidenceBitPosition R e')) = _ at hpath
  rw [← single_incidence_apply_eq_single_bitPosition (F := F) R e e'] at hpath
  simp only [optionalBitFiberSuffix_incidenceBitPosition] at hpath
  unfold primaryBitBoundary
  simp only [map_add, Pi.add_apply, combineForwardMap0_single,
    combineForwardMap0_optionalAuxiliaryCheck, combineForwardMap0Basis]
  by_cases hroot : bitPosition R e = bitRootPosition R h e.1.2
  · have hi : (bitPosition R e).1 = 0 := by
      rw [hroot]
      rfl
    simp [hi, bitFiberIndicator_incidenceBitPosition] at hpath
    rw [hpath]
    simp [combineForwardMap1Basis, hroot, bitSplitBoundary_single,
      bitSplitBasisBoundary]
  · have hi : (bitPosition R e).1 ≠ 0 := by
      intro hzero
      apply hroot
      apply Fin.ext
      exact hzero
    simp [hi] at hpath
    rw [hpath]
    simp [combineForwardMap1Basis, hroot]
omit [Fintype F] [DecidableEq F] in
theorem combineForward_commutes_auxiliaryBit
    (h : HasNoIsolatedVertices R) (a : AuxiliaryBit R) :
    combineForwardMap0 (F := F) R (auxiliaryBitBoundary (F := F) R a) =
      bitSplitBoundary (F := F) R
        (combineForwardMap1Basis (F := F) R h (Sum.inr a)) := by
  classical
  unfold auxiliaryBitBoundary
  simp [combineForwardMap0Basis, combineForwardMap1Basis,
    bitSplitBoundary_single, bitSplitBasisBoundary,
    bitSplitAuxiliaryBoundary]
omit [Fintype F] [DecidableEq F] in
/-- The complete degree-one chain-map equation for the cell-combining
forward map. -/
theorem combineForward_commutes_boundary [CharP F 2]
    (h : HasNoIsolatedVertices R) :
    (bitSplitBoundary (F := F) R).comp (combineForwardMap1 (F := F) R h) =
      (combineForwardMap0 (F := F) R).comp (boundary (F := F) R) := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro i
  cases i with
  | inl e =>
      rw [LinearMap.comp_apply, combineForwardMap1_single,
        LinearMap.comp_apply, boundary_single]
      exact (combineForward_commutes_primaryBit (F := F) R h e).symm
  | inr a =>
      rw [LinearMap.comp_apply, combineForwardMap1_single,
        LinearMap.comp_apply, boundary_single]
      exact (combineForward_commutes_auxiliaryBit (F := F) R h a).symm
noncomputable def primaryBitSuffix (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    Word F (WeightReducedBit R) :=
  fun i =>
    match i with
    | Sum.inl e => bitFiberSuffix (F := F) R b j (incidenceBitPosition R e)
    | Sum.inr _ => 0
noncomputable def optionalPrimaryBitSuffix (b : Bit)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1))) :
    Word F (WeightReducedBit R) :=
  match o with
  | none => 0
  | some j => primaryBitSuffix (F := F) R b j
omit [Fintype F] [DecidableEq F] [DecidableEq Check] in
@[simp]
theorem primaryBitSuffix_primary (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) (e : Incidence R) :
    primaryBitSuffix (F := F) R b j (Sum.inl e) =
      bitCheckSuffix (F := F) R b j e := by
  rfl
omit [Fintype F] [DecidableEq F] [DecidableEq Check] in
@[simp]
theorem primaryBitSuffix_auxiliary (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) (a : AuxiliaryBit R) :
    primaryBitSuffix (F := F) R b j (Sum.inr a) = 0 := by
  rfl
omit [Fintype F] [DecidableEq F] [DecidableEq Check] in
@[simp]
theorem optionalPrimaryBitSuffix_primary (b : Bit)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (e : Incidence R) :
    optionalPrimaryBitSuffix (F := F) R b o (Sum.inl e) =
      optionalBitCheckSuffix (F := F) R b o e := by
  cases o <;> rfl
noncomputable def combineHomotopy0Basis :
    WeightReducedCheck R → Word F (WeightReducedBit R)
  | Sum.inl _ => 0
  | Sum.inr a => primaryBitSuffix (F := F) R a.1 a.2
noncomputable def combineHomotopy0 :
    Word F (WeightReducedCheck R) →ₗ[F] Word F (WeightReducedBit R) :=
  linearMapOfBasisImages (F := F) (combineHomotopy0Basis (F := F) R)
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineHomotopy0_single (q : WeightReducedCheck R) :
    combineHomotopy0 (F := F) R (Pi.single q 1) =
      combineHomotopy0Basis (F := F) R q := by
  exact linearMapOfBasisImages_single (F := F) _ _
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineHomotopy0_optionalAuxiliaryCheck (b : Bit)
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1))) :
    combineHomotopy0 (F := F) R
        (optionalSingle (F := F) (o.map (auxiliaryCheckIndex R b))) =
      optionalPrimaryBitSuffix (F := F) R b o := by
  cases o <;> simp [optionalSingle, optionalPrimaryBitSuffix,
    combineHomotopy0Basis, auxiliaryCheckIndex]
omit [Fintype F] [DecidableEq F] in
/-- The finite-path contraction identity lifted from sigma coordinates to
the primary-bit coordinates of the weight-reduced Tanner complex. -/
theorem primaryBit_vertex_add_adjacent_suffixes [CharP F 2]
    (e : Incidence R) :
    Pi.single (Sum.inl e) 1 +
        optionalPrimaryBitSuffix (F := F) R e.1.2
          (pathPrevious (bitPosition R e)) +
        optionalPrimaryBitSuffix (F := F) R e.1.2
          (pathNext (bitPosition R e)) =
      if (bitPosition R e).1 = 0 then
        allPrimaryBitCopies (F := F) R e.1.2
      else 0 := by
  classical
  ext i
  cases i with
  | inl e' =>
      have hpath := congrFun
        (bitFiber_vertex_add_adjacent_suffixes (F := F) R e.1.2
          (bitPosition R e)) (incidenceBitPosition R e')
      simp only [Pi.add_apply] at hpath ⊢
      change (Pi.single (incidenceBitPosition R e) 1 :
          Word F (BitPositionSigma R)) (incidenceBitPosition R e') +
          _ + _ = _ at hpath
      rw [← single_incidence_apply_eq_single_bitPosition (F := F) R e e'] at hpath
      have hsingle :
          (Pi.single (Sum.inl e) 1 : Word F (WeightReducedBit R))
              (Sum.inl e') =
            (Pi.single e 1 : Word F (Incidence R)) e' := by
        simp [Pi.single_apply]
      rw [hsingle]
      rw [optionalPrimaryBitSuffix_primary,
        optionalPrimaryBitSuffix_primary]
      rw [optionalBitFiberSuffix_incidenceBitPosition,
        optionalBitFiberSuffix_incidenceBitPosition] at hpath
      by_cases hroot : (bitPosition R e).1 = 0
      · simp only [hroot, allPrimaryBitCopies, bitFiberIndicator,
          incidenceBitPosition, if_pos] at hpath ⊢
        exact hpath
      · simpa [hroot] using hpath
  | inr a =>
      cases hp : pathPrevious (bitPosition R e) <;>
        cases hn : pathNext (bitPosition R e) <;>
        by_cases hroot : (bitPosition R e).1 = 0 <;>
        simp [optionalPrimaryBitSuffix, hroot,
          allPrimaryBitCopies, primaryBitSuffix_auxiliary]
omit [Fintype F] [DecidableEq F] in
/-- Applying the homotopy to a primary-bit boundary gives the discrepancy
between the rooted surviving fiber and that primary bit. -/
theorem combineHomotopy0_primaryBitBoundary [CharP F 2]
    (e : Incidence R) :
    combineHomotopy0 (F := F) R (primaryBitBoundary (F := F) R e) =
      (if (bitPosition R e).1 = 0 then
          allPrimaryBitCopies (F := F) R e.1.2
        else 0) - Pi.single (Sum.inl e) 1 := by
  have hcontract := primaryBit_vertex_add_adjacent_suffixes (F := F) R e
  have hcontract' :
      Pi.single (Sum.inl e) 1 +
          (optionalPrimaryBitSuffix (F := F) R e.1.2
              (pathPrevious (bitPosition R e)) +
            optionalPrimaryBitSuffix (F := F) R e.1.2
              (pathNext (bitPosition R e))) =
        if (bitPosition R e).1 = 0 then
          allPrimaryBitCopies (F := F) R e.1.2
        else 0 := by
    simpa [add_assoc] using hcontract
  unfold primaryBitBoundary
  simp only [map_add, combineHomotopy0_single,
    combineHomotopy0_optionalAuxiliaryCheck, combineHomotopy0Basis,
    zero_add]
  exact eq_sub_of_add_eq' hcontract'
omit [Fintype F] [DecidableEq F] in
theorem combineInverseMap1_combineForwardMap1Basis_primary
    (h : HasNoIsolatedVertices R) (e : Incidence R) :
    combineInverseMap1 (F := F) R
        (combineForwardMap1Basis (F := F) R h (Sum.inl e)) =
      if (bitPosition R e).1 = 0 then
        allPrimaryBitCopies (F := F) R e.1.2
      else 0 := by
  classical
  by_cases hzero : (bitPosition R e).1 = 0
  · have hroot : bitPosition R e = bitRootPosition R h e.1.2 := by
      apply Fin.ext
      exact hzero
    have hrootzero : (bitRootPosition R h e.1.2).1 = 0 := rfl
    simp [combineForwardMap1Basis, hroot, hrootzero,
      combineInverseMap1Basis]
  · have hroot : bitPosition R e ≠ bitRootPosition R h e.1.2 := by
      intro heq
      apply hzero
      exact congrArg Fin.val heq
    simp [combineForwardMap1Basis, hroot, hzero]
omit [Fintype F] [DecidableEq F] in
theorem combineHomotopy0_auxiliaryBitBoundary (a : AuxiliaryBit R) :
    combineHomotopy0 (F := F) R (auxiliaryBitBoundary (F := F) R a) = 0 := by
  classical
  unfold auxiliaryBitBoundary
  simp [combineHomotopy0Basis]
noncomputable def allPrimaryCheckCopies (b : Bit) :
    Word F (WeightReducedCheck R) :=
  fun q =>
    match q with
    | Sum.inl e => if e.1.2 = b then 1 else 0
    | Sum.inr _ => 0
omit [DecidableEq F] in
/-- A boundary coordinate is the dot product against its proved transposed
row. -/
theorem boundary_apply_eq_dot_basisCoboundary
    (x : Word F (WeightReducedBit R)) (q : WeightReducedCheck R) :
    boundary (F := F) R x q =
      dotProduct (basisCoboundary (F := F) R q) x := by
  have h := wordPairing_wordLinearMapTranspose
    (boundary (F := F) R) (Pi.single q 1) x
  rw [transpose_boundary_single] at h
  simpa [wordPairing_apply, dotProduct_comm] using h.symm
omit [Fintype F] [DecidableEq F] in
theorem combineInverseMap0_bitSplitPrimaryBoundary (b : Bit) :
    combineInverseMap0 (F := F) R (bitSplitPrimaryBoundary (F := F) R b) =
      allPrimaryCheckCopies (F := F) R b := by
  classical
  ext q
  cases q with
  | inl e =>
      unfold combineInverseMap0 linearMapOfBasisImages
      change (∑ e' : Incidence R,
        bitSplitPrimaryBoundary (F := F) R b e' •
          combineInverseMap0Basis (F := F) R e') (Sum.inl e) = _
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single e]
      · simp [bitSplitPrimaryBoundary, combineInverseMap0Basis,
          allPrimaryCheckCopies]
      · intro e' _ hne
        have hs : (Sum.inl e' : WeightReducedCheck R) ≠ Sum.inl e := by
          intro heq
          exact hne (Sum.inl.inj heq)
        simp [combineInverseMap0Basis, hs]
      · simp
  | inr a =>
      unfold combineInverseMap0 linearMapOfBasisImages
      simp [combineInverseMap0Basis, allPrimaryCheckCopies]
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineInverseMap0_apply_primary
    (x : Word F (BitSplitCheck R)) (e : Incidence R) :
    combineInverseMap0 (F := F) R x (Sum.inl e) = x e := by
  classical
  unfold combineInverseMap0 linearMapOfBasisImages
  change (∑ e' : Incidence R,
    x e' • combineInverseMap0Basis (F := F) R e') (Sum.inl e) = _
  rw [Finset.sum_apply, Finset.sum_eq_single e]
  · simp [combineInverseMap0Basis]
  · intro e' _ hne
    have hs : (Sum.inl e' : WeightReducedCheck R) ≠ Sum.inl e := by
      intro heq
      exact hne (Sum.inl.inj heq)
    simp [combineInverseMap0Basis, hs]
  · simp
omit [Fintype F] [DecidableEq F] in
@[simp]
theorem combineInverseMap0_apply_auxiliary
    (x : Word F (BitSplitCheck R)) (a : AuxiliaryCheck R) :
    combineInverseMap0 (F := F) R x (Sum.inr a) = 0 := by
  classical
  unfold combineInverseMap0 linearMapOfBasisImages
  simp [combineInverseMap0Basis]
omit [DecidableEq F] in
/-- The boundary of a homotopy suffix consists of the corresponding suffix
of primary checks together with the auxiliary check at the cut edge. -/
theorem boundary_primaryBitSuffix [CharP F 2]
    (b : Bit) (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    boundary (F := F) R (primaryBitSuffix (F := F) R b j) =
      combineInverseMap0 (F := F) R (bitCheckSuffix (F := F) R b j) +
        Pi.single (Sum.inr ⟨b, j⟩) 1 := by
  classical
  ext q
  rw [boundary_apply_eq_dot_basisCoboundary]
  cases q with
  | inl e =>
      cases hp : pathPrevious (checkPosition R e) <;>
        cases hn : pathNext (checkPosition R e) <;>
        simp [basisCoboundary, primaryCheckCoboundary, primaryBitSuffix,
          optionalSingle, hp, hn, auxiliaryBitIndex, add_dotProduct,
          single_dotProduct]
  | inr a =>
      rcases a with ⟨b', k⟩
      by_cases hb : b' = b
      · subst b'
        simp only [basisCoboundary, auxiliaryCheckCoboundary,
          add_dotProduct, single_dotProduct, one_mul,
          primaryBitSuffix_primary]
        rw [bitCheckSuffix_bitIncidenceAt, bitCheckSuffix_bitIncidenceAt]
        rw [Pi.add_apply, combineInverseMap0_apply_auxiliary, zero_add]
        simpa [Pi.single_apply] using
          pathVertexSuffix_left_add_right (F := F) j k
      · simp [basisCoboundary, auxiliaryCheckCoboundary,
          primaryBitSuffix, bitFiberSuffix, incidenceBitPosition,
          bitIncidenceAt, hb, add_dotProduct, single_dotProduct]
omit [DecidableEq F] in
/-- Degree-zero part of the cell-combining homotopy equation. -/
theorem combineInverseForward_homotopy_degree0 [CharP F 2] :
    (combineInverseMap0 (F := F) R).comp (combineForwardMap0 (F := F) R) -
        LinearMap.id =
      (boundary (F := F) R).comp (combineHomotopy0 (F := F) R) := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro q
  cases q with
  | inl e =>
      simp [combineForwardMap0Basis, combineInverseMap0Basis,
        combineHomotopy0Basis]
  | inr a =>
      rw [LinearMap.sub_apply, LinearMap.comp_apply,
        combineForwardMap0_single, LinearMap.id_apply,
        LinearMap.comp_apply, combineHomotopy0_single]
      change combineInverseMap0 (F := F) R
          (bitCheckSuffix (F := F) R a.1 a.2) -
          Pi.single (Sum.inr a) 1 =
        boundary (F := F) R (primaryBitSuffix (F := F) R a.1 a.2)
      rw [word_sub_eq_add_of_char_two,
        boundary_primaryBitSuffix]
omit [Fintype F] [DecidableEq F] in
/-- Degree-one part of the cell-combining homotopy equation. -/
theorem combineInverseForward_homotopy_degree1 [CharP F 2]
    (h : HasNoIsolatedVertices R) :
    (combineInverseMap1 (F := F) R).comp
          (combineForwardMap1 (F := F) R h) - LinearMap.id =
      (combineHomotopy0 (F := F) R).comp (boundary (F := F) R) := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro i
  cases i with
  | inl e =>
      rw [LinearMap.sub_apply, LinearMap.comp_apply,
        combineForwardMap1_single, LinearMap.id_apply,
        combineInverseMap1_combineForwardMap1Basis_primary,
        LinearMap.comp_apply, boundary_single]
      change (if (bitPosition R e).1 = 0 then
          allPrimaryBitCopies (F := F) R e.1.2 else 0) -
          Pi.single (Sum.inl e) 1 =
        combineHomotopy0 (F := F) R (primaryBitBoundary (F := F) R e)
      exact (combineHomotopy0_primaryBitBoundary (F := F) R e).symm
  | inr a =>
      rw [LinearMap.sub_apply, LinearMap.comp_apply,
        combineForwardMap1_single, LinearMap.id_apply,
        LinearMap.comp_apply, boundary_single]
      change combineInverseMap1 (F := F) R
          (Pi.single (Sum.inr a) 1) - Pi.single (Sum.inr a) 1 =
        combineHomotopy0 (F := F) R (auxiliaryBitBoundary (F := F) R a)
      rw [combineInverseMap1_single]
      simp [combineInverseMap1Basis,
        combineHomotopy0_auxiliaryBitBoundary]
omit [DecidableEq F] in
theorem boundary_allPrimaryBitCopies [CharP F 2] (b : Bit) :
    boundary (F := F) R (allPrimaryBitCopies (F := F) R b) =
      allPrimaryCheckCopies (F := F) R b := by
  classical
  ext q
  rw [boundary_apply_eq_dot_basisCoboundary]
  cases q with
  | inl e =>
      cases hp : pathPrevious (checkPosition R e) <;>
        cases hn : pathNext (checkPosition R e) <;>
        simp [basisCoboundary, primaryCheckCoboundary, allPrimaryBitCopies,
          allPrimaryCheckCopies, optionalSingle, hp, hn, add_dotProduct,
          single_dotProduct, auxiliaryBitIndex]
  | inr a =>
      rcases a with ⟨b', j⟩
      by_cases hb : b' = b
      · subst b'
        simp [basisCoboundary, auxiliaryCheckCoboundary,
          allPrimaryBitCopies, allPrimaryCheckCopies, bitIncidenceAt,
          add_dotProduct, single_dotProduct,
          add_self_eq_zero_of_char_two (F := F)]
      · simp [basisCoboundary, auxiliaryCheckCoboundary,
          allPrimaryBitCopies, allPrimaryCheckCopies, bitIncidenceAt,
          add_dotProduct, single_dotProduct, hb]
omit [DecidableEq F] in
theorem combineInverse_commutes_primaryBit [CharP F 2] (b : Bit) :
    boundary (F := F) R
        (combineInverseMap1Basis (F := F) R (Sum.inl b)) =
      combineInverseMap0 (F := F) R
        (bitSplitBasisBoundary (F := F) R (Sum.inl b)) := by
  change boundary (F := F) R (allPrimaryBitCopies (F := F) R b) =
    combineInverseMap0 (F := F) R (bitSplitPrimaryBoundary (F := F) R b)
  rw [boundary_allPrimaryBitCopies, combineInverseMap0_bitSplitPrimaryBoundary]
omit [Fintype F] [DecidableEq F] in
theorem combineInverse_commutes_auxiliaryBit (a : AuxiliaryBit R) :
    boundary (F := F) R
        (combineInverseMap1Basis (F := F) R (Sum.inr a)) =
      combineInverseMap0 (F := F) R
        (bitSplitBasisBoundary (F := F) R (Sum.inr a)) := by
  classical
  simp [combineInverseMap1Basis, boundary_single, basisBoundary,
    bitSplitBasisBoundary, bitSplitAuxiliaryBoundary, auxiliaryBitBoundary,
    combineInverseMap0Basis]
omit [DecidableEq F] in
/-- The complete degree-one chain-map equation for the inverse of cell
combining. -/
theorem combineInverse_commutes_boundary [CharP F 2] :
    (boundary (F := F) R).comp (combineInverseMap1 (F := F) R) =
      (combineInverseMap0 (F := F) R).comp (bitSplitBoundary (F := F) R) := by
  apply linearMap_eq_of_single_one_eq (F := F)
  intro i
  cases i with
  | inl b =>
      rw [LinearMap.comp_apply, combineInverseMap1_single,
        LinearMap.comp_apply, bitSplitBoundary_single]
      exact combineInverse_commutes_primaryBit (F := F) R b
  | inr a =>
      rw [LinearMap.comp_apply, combineInverseMap1_single,
        LinearMap.comp_apply, bitSplitBoundary_single]
      exact combineInverse_commutes_auxiliaryBit (F := F) R a
section SameUniverseComplex
universe x
variable {F₀ Check₀ Bit₀ : Type x}
variable [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable [Fintype Check₀] [DecidableEq Check₀]
variable [Fintype Bit₀] [DecidableEq Bit₀]
variable (R₀ : Check₀ → Bit₀ → Prop) [DecidableRel R₀]
noncomputable def bitSplitComplex :
    ChainComplexData F₀ (Word F₀ (BitSplitCheck R₀))
      (Word F₀ (BitSplitBit R₀)) (Word F₀ (Fin 0)) where
  boundary1 := bitSplitBoundary (F := F₀) R₀
  boundary2 := 0
  boundary_squared := by simp
noncomputable def combineForwardChainMap [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainMap (weightReducedComplex (F₀ := F₀) R₀)
      (bitSplitComplex (F₀ := F₀) R₀) where
  map0 := combineForwardMap0 (F := F₀) R₀
  map1 := combineForwardMap1 (F := F₀) R₀ h
  map2 := LinearMap.id
  commutes_boundary1 := combineForward_commutes_boundary (F := F₀) R₀ h
  commutes_boundary2 := by
    simp [weightReducedComplex, bitSplitComplex]
noncomputable def combineInverseChainMap [CharP F₀ 2] :
    ThreeTermChainMap (bitSplitComplex (F₀ := F₀) R₀)
      (weightReducedComplex (F₀ := F₀) R₀) where
  map0 := combineInverseMap0 (F := F₀) R₀
  map1 := combineInverseMap1 (F := F₀) R₀
  map2 := LinearMap.id
  commutes_boundary1 := combineInverse_commutes_boundary (F := F₀) R₀
  commutes_boundary2 := by
    simp [weightReducedComplex, bitSplitComplex]
noncomputable def combineInverseForwardHomotopy [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopy
      ((combineInverseChainMap (F₀ := F₀) R₀).comp
        (combineForwardChainMap (F₀ := F₀) R₀ h))
      (ThreeTermChainMap.id (weightReducedComplex (F₀ := F₀) R₀)) where
  homotopy0 := combineHomotopy0 (F := F₀) R₀
  homotopy1 := 0
  degree0 := combineInverseForward_homotopy_degree0 (F := F₀) R₀
  degree1 := by
    simpa [combineInverseChainMap, combineForwardChainMap,
      weightReducedComplex] using
      combineInverseForward_homotopy_degree1 (F := F₀) R₀ h
  degree2 := by
    simp [combineInverseChainMap, combineForwardChainMap,
      weightReducedComplex]
noncomputable def combineForwardInverseHomotopy [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopy
      ((combineForwardChainMap (F₀ := F₀) R₀ h).comp
        (combineInverseChainMap (F₀ := F₀) R₀))
      (ThreeTermChainMap.id (bitSplitComplex (F₀ := F₀) R₀)) where
  homotopy0 := 0
  homotopy1 := 0
  degree0 := by
    simp only [ThreeTermChainMap.comp_map0, ThreeTermChainMap.id_map0]
    change (combineForwardMap0 (F := F₀) R₀).comp
        (combineInverseMap0 (F := F₀) R₀) - LinearMap.id = _
    rw [combineForwardMap0_comp_combineInverseMap0]
    simp
  degree1 := by
    simp only [ThreeTermChainMap.comp_map1, ThreeTermChainMap.id_map1]
    change (combineForwardMap1 (F := F₀) R₀ h).comp
        (combineInverseMap1 (F := F₀) R₀) - LinearMap.id = _
    rw [combineForwardMap1_comp_combineInverseMap1]
    simp
  degree2 := by
    simp [combineForwardChainMap, combineInverseChainMap,
      bitSplitComplex]
noncomputable def combineHomotopyEquiv [CharP F₀ 2]
    (h : HasNoIsolatedVertices R₀) :
    ThreeTermChainHomotopyEquiv
      (weightReducedComplex (F₀ := F₀) R₀)
      (bitSplitComplex (F₀ := F₀) R₀) where
  forward := combineForwardChainMap (F₀ := F₀) R₀ h
  inverse := combineInverseChainMap (F₀ := F₀) R₀
  inverse_forward := combineInverseForwardHomotopy (F₀ := F₀) R₀ h
  forward_inverse := combineForwardInverseHomotopy (F₀ := F₀) R₀ h
end SameUniverseComplex
end QEC.Coding.ClassicalWeightReduction


