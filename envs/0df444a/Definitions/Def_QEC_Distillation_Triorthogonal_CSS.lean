-- Prove2me | Definitions.Def_QEC_Distillation_Triorthogonal_CSS
-- name    : QEC_Distillation_Triorthogonal_CSS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:05:25.789309+00:00
-- url     : https://prove2.me/theorems/55673782-15d7-4d6d-8ab5-38bd15af9b0b
-- title:
--   CSS
-- statement:
--   Definitions and structural lemmas for CSS, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
import Theorems.Thm_QEC_Coding_PauliSymplectic_finrank_binaryCSSLogicalBasisQuotient_eq
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
theorem quotientMkFiber_natCard
    {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype M] (S : Submodule R M) (q : M ⧸ S) :
    Nat.card {x : M // S.mkQ x = q} = Nat.card S := by
  classical
  have hcard := AddMonoidHom.card_fiber_eq_of_mem_range S.mkQ
    (S.mkQ_surjective q) (S.mkQ_surjective 0)
  let ezero : {x : M // S.mkQ x = 0} ≃ S :=
    { toFun := fun x => ⟨x, (Submodule.Quotient.mk_eq_zero S).mp x.2⟩
      invFun := fun x => ⟨x, (Submodule.Quotient.mk_eq_zero S).mpr x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  change Nat.card {x : M // S.mkQ x = q} = Nat.card S
  calc
    _ = Fintype.card {x : M // S.mkQ x = q} := Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun x : M => S.mkQ x = q).card := Fintype.card_subtype _
    _ = (Finset.univ.filter fun x : M => S.mkQ x = 0).card := hcard
    _ = Fintype.card {x : M // S.mkQ x = 0} := (Fintype.card_subtype _).symm
    _ = Nat.card {x : M // S.mkQ x = 0} := Nat.card_eq_fintype_card.symm
    _ = Nat.card S := Nat.card_congr ezero
theorem sum_quotientMk_eq_natCard_mul
    {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype M] (S : Submodule R M) (f : (M ⧸ S) → Complex) :
    (∑ x : M, f (Submodule.Quotient.mk x)) =
      (Nat.card S : Complex) * ∑ q : M ⧸ S, f q := by
  classical
  change (∑ x : M, f (S.mkQ x)) = _
  rw [← Fintype.sum_fiberwise (fun x : M => S.mkQ x)]
  simp_rw [show ∀ q : M ⧸ S,
      (∑ x : {x : M // S.mkQ x = q}, f (S.mkQ x)) =
          (Nat.card S : Complex) * f q by
    intro q
    simp_rw [show ∀ x : {x : M // S.mkQ x = q},
      f (S.mkQ x) = f q from fun x => congrArg f x.2]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    rw [quotientMkFiber_natCard S q]]
  exact (Finset.mul_sum Finset.univ f (Nat.card S : Complex)).symm
theorem sum_dite_submodule
    {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype M] (S : Submodule R M) [Fintype S]
    [DecidablePred fun x : M => x ∈ S] (f : S → Complex) :
    (∑ x : M, if hx : x ∈ S then f ⟨x, hx⟩ else 0) = ∑ x : S, f x := by
  classical
  let g : M → Complex := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have h := Finset.sum_subtype (p := fun x : M => x ∈ S) (F := inferInstance)
    (Finset.univ.filter fun x : M => x ∈ S) (by simp) g
  have hsub :
      ∑ x ∈ Finset.univ.filter (fun x : M => x ∈ S), g x = ∑ x : S, f x := by
    simpa [g] using h
  have hall :
      ∑ x ∈ Finset.univ.filter (fun x : M => x ∈ S), g x =
        ∑ x ∈ Finset.univ, g x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _hx hxnot
    have hxS : x ∉ S := by simpa using hxnot
    simp [g, hxS]
  exact hall.symm.trans hsub
theorem binaryCSSLogicalBasisQuotientToCarrier_inner
    {I : Type uI} [Fintype I] [DecidableEq I]
    (xCode zCode : LinearCode (ZMod 2) I)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (phi chi : EuclideanSpace Complex
      (binaryCSSLogicalBasisQuotient xCode zCode)) :
    inner Complex (binaryCSSLogicalBasisQuotientToCarrier xCode zCode hdual phi)
        (binaryCSSLogicalBasisQuotientToCarrier xCode zCode hdual chi) =
      (Nat.card xCode.carrier : Complex) * inner Complex phi chi := by
  letI : Fintype zCode.dual.carrier := Fintype.ofFinite _
  letI : Fintype (binaryCSSLogicalBasisQuotient xCode zCode) := inferInstance
  change inner Complex
      (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode phi)
      (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode chi) = _
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  classical
  calc
    _ = ∑ w : Word (ZMod 2) I,
        (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode chi)
            ((bitstringWordEquiv I).symm w) *
          starRingEnd Complex
            ((binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode phi)
              ((bitstringWordEquiv I).symm w)) := by
      exact ((bitstringWordEquiv I).symm.sum_comp fun bits =>
        (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode chi) bits *
          starRingEnd Complex
            ((binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode phi) bits)).symm
    _ = ∑ w : Word (ZMod 2) I,
        if hw : w ∈ zCode.dual.carrier then
          chi (Submodule.Quotient.mk ⟨w, hw⟩) *
            starRingEnd Complex (phi (Submodule.Quotient.mk ⟨w, hw⟩))
        else 0 := by
      apply Fintype.sum_congr _ _
      intro w
      by_cases hw : w ∈ zCode.dual.carrier
      · have hbits :
            bitstringWordEquiv I ((bitstringWordEquiv I).symm w) ∈
              zCode.dual.carrier := by simpa using hw
        rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
          xCode zCode chi hbits,
          binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
            xCode zCode phi hbits, dif_pos hw]
        simp
      · have hbits :
            bitstringWordEquiv I ((bitstringWordEquiv I).symm w) ∉
              zCode.dual.carrier := by simpa using hw
        rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
          xCode zCode chi hbits,
          binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
            xCode zCode phi hbits, dif_neg hw]
        simp
    _ = ∑ u : zCode.dual.carrier,
        chi (Submodule.Quotient.mk u) *
          starRingEnd Complex (phi (Submodule.Quotient.mk u)) := by
      exact sum_dite_submodule (R := ZMod 2) (M := Word (ZMod 2) I)
        zCode.dual.carrier fun u =>
          chi (Submodule.Quotient.mk u) *
            starRingEnd Complex (phi (Submodule.Quotient.mk u))
    _ = (Nat.card (binaryCSSXCodeInZDual xCode zCode) : Complex) *
        ∑ q : binaryCSSLogicalBasisQuotient xCode zCode,
          chi q * starRingEnd Complex (phi q) := by
      exact sum_quotientMk_eq_natCard_mul
        (R := ZMod 2) (M := zCode.dual.carrier)
        (binaryCSSXCodeInZDual xCode zCode)
        (fun q => chi q * starRingEnd Complex (phi q))
    _ = (Nat.card xCode.carrier : Complex) *
        ∑ q : binaryCSSLogicalBasisQuotient xCode zCode,
          chi q * starRingEnd Complex (phi q) := by
      rw [Nat.card_congr (binaryCSSXCodeInZDualEquiv xCode zCode hdual).toEquiv]
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
structure BinaryRowFamily (OddRow : Type u) (EvenRow : Type v) (Col : Type w) where
  oddRow : OddRow → Word (ZMod 2) Col
  evenRow : EvenRow → Word (ZMod 2) Col
namespace BinaryRowFamily
def row (R : BinaryRowFamily OddRow EvenRow Col) :
    Sum OddRow EvenRow → Word (ZMod 2) Col
  | .inl a => R.oddRow a
  | .inr b => R.evenRow b
def pairOverlap (x y : Word (ZMod 2) Col) : Nat :=
  ∑ j, (x j * y j).val
def tripleOverlap (x y z : Word (ZMod 2) Col) : Nat :=
  ∑ j, (x j * y j * z j).val
theorem pairOverlap_cast (x y : Word (ZMod 2) Col) :
    (pairOverlap x y : ZMod 2) = wordPairing x y := by
  classical
  simp [pairOverlap, wordPairing_apply, dotProduct]
theorem pairOverlap_self_eq_hammingWeight (x : Word (ZMod 2) Col) :
    pairOverlap x x = HammingWeight x := by
  classical
  simp only [pairOverlap, HammingWeight, hammingSupport]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hx : x j = 0
  · simp [hx]
  · rw [if_pos hx]
    have hmul : x j * x j ≠ 0 := mul_ne_zero hx hx
    have hpos : 0 < (x j * x j).val :=
      Nat.pos_of_ne_zero ((ZMod.val_eq_zero (x j * x j)).not.mpr hmul)
    have hlt : (x j * x j).val < 2 := ZMod.val_lt (x j * x j)
    omega
structure IsTriorthogonal (R : BinaryRowFamily OddRow EvenRow Col) : Prop where
  odd_weight : ∀ a, Odd (HammingWeight (R.oddRow a))
  even_weight : ∀ b, Even (HammingWeight (R.evenRow b))
  pair_even : ∀ a b : Sum OddRow EvenRow, a ≠ b →
    Even (pairOverlap (R.row a) (R.row b))
  triple_even : ∀ a b c : Sum OddRow EvenRow,
    a ≠ b → a ≠ c → b ≠ c →
      Even (tripleOverlap (R.row a) (R.row b) (R.row c))
def oddCode (R : BinaryRowFamily OddRow EvenRow Col) : LinearCode (ZMod 2) Col where
  carrier := Submodule.span (ZMod 2) (Set.range R.oddRow)
def evenCode (R : BinaryRowFamily OddRow EvenRow Col) : LinearCode (ZMod 2) Col where
  carrier := Submodule.span (ZMod 2) (Set.range R.evenRow)
def rowCode (R : BinaryRowFamily OddRow EvenRow Col) : LinearCode (ZMod 2) Col where
  carrier := Submodule.span (ZMod 2) (Set.range R.row)
@[simp] theorem oddRow_mem_oddCode (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow) :
    R.oddRow a ∈ R.oddCode.carrier :=
  Submodule.subset_span ⟨a, rfl⟩
@[simp] theorem evenRow_mem_evenCode (R : BinaryRowFamily OddRow EvenRow Col) (b : EvenRow) :
    R.evenRow b ∈ R.evenCode.carrier :=
  Submodule.subset_span ⟨b, rfl⟩
@[simp] theorem row_mem_rowCode (R : BinaryRowFamily OddRow EvenRow Col)
    (a : Sum OddRow EvenRow) : R.row a ∈ R.rowCode.carrier :=
  Submodule.subset_span ⟨a, rfl⟩
theorem cast_even_eq_zero {n : Nat} (h : Even n) : (n : ZMod 2) = 0 := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.cast_add, ← two_mul]
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [htwo, zero_mul]
theorem cast_odd_eq_one {n : Nat} (h : Odd n) : (n : ZMod 2) = 1 := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.cast_add, Nat.cast_mul]
  have htwo : ((2 : Nat) : ZMod 2) = 0 := ZMod.natCast_self 2
  have hone : ((1 : Nat) : ZMod 2) = 1 := Nat.cast_one
  rw [htwo, zero_mul, zero_add, hone]
@[simp] theorem oddRow_self_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a : OddRow) :
    wordPairing (R.oddRow a) (R.oddRow a) = 1 := by
  rw [← pairOverlap_cast, pairOverlap_self_eq_hammingWeight]
  exact cast_odd_eq_one (hR.odd_weight a)
@[simp] theorem evenRow_self_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (b : EvenRow) :
    wordPairing (R.evenRow b) (R.evenRow b) = 0 := by
  rw [← pairOverlap_cast, pairOverlap_self_eq_hammingWeight]
  exact cast_even_eq_zero (hR.even_weight b)
theorem row_pairing_eq_zero_of_ne (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) {a b : Sum OddRow EvenRow} (hab : a ≠ b) :
    wordPairing (R.row a) (R.row b) = 0 := by
  rw [← pairOverlap_cast]
  exact cast_even_eq_zero (hR.pair_even a b hab)
@[simp] theorem oddRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a b : OddRow) :
    wordPairing (R.oddRow a) (R.oddRow b) = if a = b then 1 else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [oddRow_self_pairing R hR]
  · rw [if_neg hab]
    exact R.row_pairing_eq_zero_of_ne hR
      (a := Sum.inl a) (b := Sum.inl b) (by simpa using hab)
@[simp] theorem evenRow_oddRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (b : EvenRow) (a : OddRow) :
    wordPairing (R.evenRow b) (R.oddRow a) = 0 :=
  R.row_pairing_eq_zero_of_ne hR
    (a := Sum.inr b) (b := Sum.inl a) (by simp)
@[simp] theorem oddRow_evenRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a : OddRow) (b : EvenRow) :
    wordPairing (R.oddRow a) (R.evenRow b) = 0 :=
  R.row_pairing_eq_zero_of_ne hR
    (a := Sum.inl a) (b := Sum.inr b) (by simp)
@[simp] theorem evenRow_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (a b : EvenRow) :
    wordPairing (R.evenRow a) (R.evenRow b) = 0 := by
  by_cases hab : a = b
  · subst b
    exact evenRow_self_pairing R hR a
  · exact R.row_pairing_eq_zero_of_ne hR
      (a := Sum.inr a) (b := Sum.inr b) (by simpa using hab)
theorem wordPairing_span_right
    {Index : Type*} [Fintype Index]
    (v : Index → Word (ZMod 2) Col) (x : Word (ZMod 2) Col)
    (h : ∀ i, wordPairing x (v i) = 0)
    {y : Word (ZMod 2) Col} (hy : y ∈ Submodule.span (ZMod 2) (Set.range v)) :
    wordPairing x y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨i, rfl⟩
      exact h i
  | zero => exact (wordPairing x).map_zero
  | add y z _ _ hy hz =>
      rw [(wordPairing x).map_add, hy, hz, add_zero]
  | smul c y _ hy =>
      rw [(wordPairing x).map_smul, hy, smul_zero]
theorem wordPairing_span_left
    {Index : Type*} [Fintype Index]
    (v : Index → Word (ZMod 2) Col) (y : Word (ZMod 2) Col)
    (h : ∀ i, wordPairing (v i) y = 0)
    {x : Word (ZMod 2) Col} (hx : x ∈ Submodule.span (ZMod 2) (Set.range v)) :
    wordPairing x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact h i
  | zero => simp
  | add x z _ _ hx hz =>
      rw [wordPairing.map_add]
      change wordPairing x y + wordPairing z y = 0
      rw [hx, hz, add_zero]
  | smul c x _ hx =>
      rw [wordPairing.map_smul]
      change c * wordPairing x y = 0
      rw [hx, mul_zero]
theorem wordPairing_sum_oddRow (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (c : OddRow → ZMod 2) (a : OddRow) :
    wordPairing (∑ i, c i • R.oddRow i) (R.oddRow a) = c a := by
  classical
  simp [R.oddRow_pairing hR]
theorem oddRows_linearIndependent (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) : LinearIndependent (ZMod 2) R.oddRow := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hp := congrArg (fun x => wordPairing x (R.oddRow a)) hc
  have hp' : wordPairing (∑ i, c i • R.oddRow i) (R.oddRow a) = 0 := by
    simpa using hp
  rw [R.wordPairing_sum_oddRow hR c a] at hp'
  exact hp'
theorem eq_zero_of_mem_oddCode_of_pairing_eq_zero
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.oddCode.carrier)
    (hpair : ∀ a, wordPairing x (R.oddRow a) = 0) : x = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hx
  have hc0 : ∀ a, c a = 0 := by
    intro a
    rw [← R.wordPairing_sum_oddRow hR c a, hc]
    exact hpair a
  calc
    x = ∑ a, c a • R.oddRow a := hc.symm
    _ = 0 := by simp [hc0]
theorem wordPairing_evenCode_oddCode
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x y : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.carrier)
    (hy : y ∈ R.oddCode.carrier) : wordPairing x y = 0 := by
  apply wordPairing_span_left R.evenRow y (fun b => ?_) hx
  exact wordPairing_span_right R.oddRow (R.evenRow b)
    (fun a => R.evenRow_oddRow_pairing hR b a) hy
theorem rowCode_eq_evenCode_sup_oddCode (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.carrier = R.evenCode.carrier ⊔ R.oddCode.carrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨a, rfl⟩
    rcases a with a | b
    · exact Submodule.mem_sup_right (R.oddRow_mem_oddCode a)
    · exact Submodule.mem_sup_left (R.evenRow_mem_evenCode b)
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨b, rfl⟩
      exact R.row_mem_rowCode (.inr b)
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with ⟨a, rfl⟩
      exact R.row_mem_rowCode (.inl a)
theorem evenCode_inf_oddCode_eq_bot
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.evenCode.carrier ⊓ R.oddCode.carrier = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxEven : x ∈ R.evenCode.carrier := hx.1
  have hxOdd : x ∈ R.oddCode.carrier := hx.2
  have hzero := R.eq_zero_of_mem_oddCode_of_pairing_eq_zero hR hxOdd (fun a =>
    R.wordPairing_evenCode_oddCode hR hxEven (R.oddRow_mem_oddCode a))
  simpa [hzero]
theorem oddCode_inf_rowCode_dual_eq_bot
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.oddCode.carrier ⊓ R.rowCode.dual.carrier = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hzero := R.eq_zero_of_mem_oddCode_of_pairing_eq_zero hR hx.1 (fun a =>
    R.rowCode.orthogonal_of_mem_dual hx.2 (R.row_mem_rowCode (.inl a)))
  simpa [hzero]
theorem oddCode_disjoint_rowCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Disjoint R.oddCode.carrier R.rowCode.dual.carrier := by
  rw [disjoint_iff]
  exact R.oddCode_inf_rowCode_dual_eq_bot hR
theorem oddCode_le_evenCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.oddCode.carrier ≤ R.evenCode.dual.carrier := by
  intro x hx
  rw [LinearCode.mem_dual]
  intro e he
  rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply]
  exact R.wordPairing_evenCode_oddCode hR he hx
theorem rowCode_dual_le_evenCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.dual.carrier ≤ R.evenCode.dual.carrier := by
  intro x hx
  rw [LinearCode.mem_dual]
  intro e he
  exact R.rowCode.orthogonal_of_mem_dual hx (by
    rw [R.rowCode_eq_evenCode_sup_oddCode]
    exact Submodule.mem_sup_left he)
def oddProjection (R : BinaryRowFamily OddRow EvenRow Col)
    (x : Word (ZMod 2) Col) : Word (ZMod 2) Col :=
  ∑ a, wordPairing x (R.oddRow a) • R.oddRow a
theorem oddProjection_mem_oddCode (R : BinaryRowFamily OddRow EvenRow Col)
    (x : Word (ZMod 2) Col) : R.oddProjection x ∈ R.oddCode.carrier := by
  classical
  exact Submodule.sum_mem R.oddCode.carrier (fun a _ =>
    R.oddCode.carrier.smul_mem _ (R.oddRow_mem_oddCode a))
@[simp] theorem oddProjection_pairing (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) (x : Word (ZMod 2) Col) (a : OddRow) :
    wordPairing (R.oddProjection x) (R.oddRow a) =
      wordPairing x (R.oddRow a) := by
  classical
  exact R.wordPairing_sum_oddRow hR (fun b => wordPairing x (R.oddRow b)) a
theorem sub_oddProjection_mem_rowCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {x : Word (ZMod 2) Col} (hx : x ∈ R.evenCode.dual.carrier) :
    x - R.oddProjection x ∈ R.rowCode.dual.carrier := by
  rw [LinearCode.mem_dual]
  intro y hy
  apply wordPairing_span_right R.row (x - R.oddProjection x) (fun a => ?_) hy
  rcases a with a | b
  · change wordPairing (x - R.oddProjection x) (R.oddRow a) = 0
    rw [sub_eq_add_neg, ZModModule.neg_eq_self, wordPairing.map_add]
    change wordPairing x (R.oddRow a) +
      wordPairing (R.oddProjection x) (R.oddRow a) = 0
    rw [R.oddProjection_pairing hR]
    exact ZModModule.add_self _
  · have hxEven := R.evenCode.orthogonal_of_mem_dual hx (R.evenRow_mem_evenCode b)
    have hpEven := R.wordPairing_evenCode_oddCode hR (R.evenRow_mem_evenCode b)
      (R.oddProjection_mem_oddCode x)
    rw [wordPairing_apply, dotProduct_comm, ← wordPairing_apply] at hpEven
    change wordPairing (x - R.oddProjection x) (R.evenRow b) = 0
    rw [sub_eq_add_neg, ZModModule.neg_eq_self, wordPairing.map_add]
    change wordPairing x (R.evenRow b) +
      wordPairing (R.oddProjection x) (R.evenRow b) = 0
    rw [hxEven, hpEven, add_zero]
theorem evenCode_dual_eq_oddCode_sup_rowCode_dual
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.evenCode.dual.carrier = R.oddCode.carrier ⊔ R.rowCode.dual.carrier := by
  apply le_antisymm
  · intro x hx
    refine Submodule.mem_sup.mpr ⟨R.oddProjection x, R.oddProjection_mem_oddCode x,
      x - R.oddProjection x, R.sub_oddProjection_mem_rowCode_dual hR hx, ?_⟩
    abel
  · exact sup_le (R.oddCode_le_evenCode_dual hR) R.rowCode_dual_le_evenCode_dual
theorem dimension_oddCode (R : BinaryRowFamily OddRow EvenRow Col)
    (hR : R.IsTriorthogonal) : Dimension R.oddCode = Fintype.card OddRow := by
  change Module.finrank (ZMod 2) R.oddCode.carrier = _
  exact finrank_span_eq_card (R.oddRows_linearIndependent hR)
theorem cssDualContainment (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.dual.carrier ≤ R.evenCode.dual.carrier :=
  R.rowCode_dual_le_evenCode_dual
noncomputable def cssQuantumCode (R : BinaryRowFamily OddRow EvenRow Col) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister Col) :=
  PauliSymplectic.binaryCSSQuantumCodeOfDualLe
    R.evenCode R.rowCode.dual R.cssDualContainment
theorem cssLogicalExponent_eq_card_oddRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Length (ZMod 2) Col - Dimension R.evenCode - Dimension R.rowCode.dual =
      Fintype.card OddRow := by
  have hGrass := Submodule.finrank_sup_add_finrank_inf_eq
    R.oddCode.carrier R.rowCode.dual.carrier
  rw [(R.oddCode_disjoint_rowCode_dual hR).eq_bot, finrank_bot, add_zero] at hGrass
  have hSplit :
      Dimension R.evenCode.dual =
        Dimension R.oddCode + Dimension R.rowCode.dual := by
    rw [Dimension_eq_finrank_carrier, R.evenCode_dual_eq_oddCode_sup_rowCode_dual hR]
    exact hGrass
  rw [← R.evenCode.dual_dimension_eq_length_sub_dimension,
    hSplit, R.dimension_oddCode hR]
  omega
noncomputable def cssNormalizationScalar
    (R : BinaryRowFamily OddRow EvenRow Col) : Complex :=
  (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex)⁻¹
theorem cssNormalizationScalar_identity
    (R : BinaryRowFamily OddRow EvenRow Col) :
    starRingEnd Complex R.cssNormalizationScalar * R.cssNormalizationScalar *
        (Nat.card R.evenCode.carrier : Complex) = 1 := by
  have hcard : 0 < Nat.card R.evenCode.carrier := Nat.card_pos
  have hsqrtPos :
      0 < Real.sqrt (Nat.card R.evenCode.carrier : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) *
          (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) =
        (Nat.card R.evenCode.carrier : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Nat.card R.evenCode.carrier)
  simp only [cssNormalizationScalar, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) =
        (Real.sqrt (Nat.card R.evenCode.carrier : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]
noncomputable def normalizedLogicalQuotientToCarrierLinearMap
    (R : BinaryRowFamily OddRow EvenRow Col) :
    EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) →ₗ[Complex] R.cssQuantumCode.carrier :=
  R.cssNormalizationScalar •
    PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
      R.evenCode R.rowCode.dual R.cssDualContainment
@[simp] theorem normalizedLogicalQuotientToCarrierLinearMap_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (phi : EuclideanSpace Complex
      (PauliSymplectic.binaryCSSLogicalBasisQuotient
        R.evenCode R.rowCode.dual)) :
    R.normalizedLogicalQuotientToCarrierLinearMap phi =
      R.cssNormalizationScalar •
        PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
          R.evenCode R.rowCode.dual R.cssDualContainment phi :=
  rfl
theorem normalizedLogicalQuotientToCarrierLinearMap_inner
    (R : BinaryRowFamily OddRow EvenRow Col)
    (phi chi : EuclideanSpace Complex
      (PauliSymplectic.binaryCSSLogicalBasisQuotient
        R.evenCode R.rowCode.dual)) :
    inner Complex (R.normalizedLogicalQuotientToCarrierLinearMap phi)
        (R.normalizedLogicalQuotientToCarrierLinearMap chi) =
      inner Complex phi chi := by
  rw [normalizedLogicalQuotientToCarrierLinearMap_apply,
    normalizedLogicalQuotientToCarrierLinearMap_apply]
  calc
    inner Complex
          (R.cssNormalizationScalar •
            PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
              R.evenCode R.rowCode.dual R.cssDualContainment phi)
          (R.cssNormalizationScalar •
            PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
              R.evenCode R.rowCode.dual R.cssDualContainment chi) =
        starRingEnd Complex R.cssNormalizationScalar *
          inner Complex
            (PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
              R.evenCode R.rowCode.dual R.cssDualContainment phi)
            (R.cssNormalizationScalar •
              PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
                R.evenCode R.rowCode.dual R.cssDualContainment chi) :=
      inner_smul_left _ _ _
    _ = starRingEnd Complex R.cssNormalizationScalar *
          (R.cssNormalizationScalar *
            inner Complex
              (PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
                R.evenCode R.rowCode.dual R.cssDualContainment phi)
              (PauliSymplectic.binaryCSSLogicalBasisQuotientToCarrier
                R.evenCode R.rowCode.dual R.cssDualContainment chi)) := by
      rw [inner_smul_right]
    _ = starRingEnd Complex R.cssNormalizationScalar *
          (R.cssNormalizationScalar *
            ((Nat.card R.evenCode.carrier : Complex) * inner Complex phi chi)) := by
      rw [binaryCSSLogicalBasisQuotientToCarrier_inner]
    _ = (starRingEnd Complex R.cssNormalizationScalar * R.cssNormalizationScalar *
          (Nat.card R.evenCode.carrier : Complex)) * inner Complex phi chi := by ring
    _ = inner Complex phi chi := by rw [R.cssNormalizationScalar_identity, one_mul]
noncomputable def normalizedLogicalQuotientToCarrierLinearIsometry
    (R : BinaryRowFamily OddRow EvenRow Col) :
    EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) →ₗᵢ[Complex] R.cssQuantumCode.carrier :=
  R.normalizedLogicalQuotientToCarrierLinearMap.isometryOfInner
    R.normalizedLogicalQuotientToCarrierLinearMap_inner
noncomputable def normalizedLogicalQuotientToCarrier
    (R : BinaryRowFamily OddRow EvenRow Col) :
    EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) ≃ₗᵢ[Complex] R.cssQuantumCode.carrier := by
  let L := R.normalizedLogicalQuotientToCarrierLinearIsometry
  have hdim :
      Module.finrank Complex
          (EuclideanSpace Complex
            (PauliSymplectic.binaryCSSLogicalBasisQuotient
              R.evenCode R.rowCode.dual)) =
        Module.finrank Complex R.cssQuantumCode.carrier := by
    exact (PauliSymplectic.binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
      R.evenCode R.rowCode.dual R.cssDualContainment).finrank_eq.symm
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp L.injective
  exact LinearIsometryEquiv.ofSurjective L hsurj
@[simp] theorem normalizedLogicalQuotientToCarrier_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (phi : EuclideanSpace Complex
      (PauliSymplectic.binaryCSSLogicalBasisQuotient
        R.evenCode R.rowCode.dual)) :
    R.normalizedLogicalQuotientToCarrier phi =
      R.normalizedLogicalQuotientToCarrierLinearMap phi :=
  rfl
def oddCombination (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) OddRow →ₗ[ZMod 2] Word (ZMod 2) Col :=
  Fintype.linearCombination (ZMod 2) R.oddRow
@[simp] theorem oddCombination_apply
    (R : BinaryRowFamily OddRow EvenRow Col) (c : Word (ZMod 2) OddRow) :
    R.oddCombination c = ∑ a, c a • R.oddRow a := by
  exact Fintype.linearCombination_apply (ZMod 2) R.oddRow c
theorem oddCombination_mem_oddCode
    (R : BinaryRowFamily OddRow EvenRow Col) (c : Word (ZMod 2) OddRow) :
    R.oddCombination c ∈ R.oddCode.carrier := by
  rw [oddCombination_apply]
  exact Submodule.sum_mem R.oddCode.carrier (fun a _ =>
    R.oddCode.carrier.smul_mem _ (R.oddRow_mem_oddCode a))
theorem oddCombination_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) (c : Word (ZMod 2) OddRow) :
    R.oddCombination c ∈ R.rowCode.carrier := by
  rw [R.rowCode_eq_evenCode_sup_oddCode]
  exact Submodule.mem_sup_right (R.oddCombination_mem_oddCode c)
def oddCombinationInRowDoubleDual (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) OddRow →ₗ[ZMod 2] R.rowCode.dual.dual.carrier :=
  R.oddCombination.codRestrict R.rowCode.dual.dual.carrier fun c => by
    rw [LinearCode.mem_dual]
    intro y hy
    exact R.rowCode.dual_orthogonal (R.oddCombination_mem_rowCode c) hy
noncomputable def oddWordToLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) OddRow →ₗ[ZMod 2]
      PauliSymplectic.binaryCSSLogicalBasisQuotient R.evenCode R.rowCode.dual :=
  (PauliSymplectic.binaryCSSXCodeInZDual R.evenCode R.rowCode.dual).mkQ.comp
    R.oddCombinationInRowDoubleDual
theorem oddWordToLogicalQuotient_injective
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Function.Injective R.oddWordToLogicalQuotient := by
  refine (injective_iff_map_eq_zero R.oddWordToLogicalQuotient).mpr ?_
  intro c hc
  have hmem :
      R.oddCombinationInRowDoubleDual c ∈
        PauliSymplectic.binaryCSSXCodeInZDual R.evenCode R.rowCode.dual := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact hc
  have heven : R.oddCombination c ∈ R.evenCode.carrier := by
    exact hmem
  have hinter :
      R.oddCombination c ∈ R.evenCode.carrier ⊓ R.oddCode.carrier :=
    ⟨heven, R.oddCombination_mem_oddCode c⟩
  have hcomb : R.oddCombination c = 0 := by
    rw [R.evenCode_inf_oddCode_eq_bot hR] at hinter
    simpa using hinter
  apply funext
  intro a
  exact (Fintype.linearIndependent_iff.mp (R.oddRows_linearIndependent hR))
    c (by simpa using hcomb) a
theorem finrank_logicalQuotient_eq_card_oddRows
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Module.finrank (ZMod 2)
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) = Fintype.card OddRow := by
  rw [PauliSymplectic.finrank_binaryCSSLogicalBasisQuotient_eq
    R.evenCode R.rowCode.dual R.cssDualContainment,
    R.cssLogicalExponent_eq_card_oddRows hR]
noncomputable def oddWordLinearEquivLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Word (ZMod 2) OddRow ≃ₗ[ZMod 2]
      PauliSymplectic.binaryCSSLogicalBasisQuotient R.evenCode R.rowCode.dual :=
  R.oddWordToLogicalQuotient.linearEquivOfInjective
    (R.oddWordToLogicalQuotient_injective hR) (by
      rw [finrank_word_eq_length, Length,
        R.finrank_logicalQuotient_eq_card_oddRows hR])
noncomputable def logicalBasisEquivLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Qubit.Bitstring OddRow ≃
      PauliSymplectic.binaryCSSLogicalBasisQuotient R.evenCode R.rowCode.dual :=
  (PauliSymplectic.bitstringWordEquiv OddRow).trans
    (R.oddWordLinearEquivLogicalQuotient hR).toEquiv
noncomputable def logicalBasisReindex
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Qubit.QubitRegister OddRow ≃ₗᵢ[Complex]
      EuclideanSpace Complex
        (PauliSymplectic.binaryCSSLogicalBasisQuotient
          R.evenCode R.rowCode.dual) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (R.logicalBasisEquivLogicalQuotient hR)
noncomputable def encoding
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Qubit.QubitRegister OddRow ≃ₗᵢ[Complex] R.cssQuantumCode.carrier :=
  (R.logicalBasisReindex hR).trans R.normalizedLogicalQuotientToCarrier
noncomputable def encodedCode
    {LogicalRow PhysicalCol : Type u} {StabilizerRow : Type v}
    [Fintype LogicalRow] [Fintype StabilizerRow] [Fintype PhysicalCol]
    [DecidableEq LogicalRow] [DecidableEq StabilizerRow] [DecidableEq PhysicalCol]
    (R : BinaryRowFamily LogicalRow StabilizerRow PhysicalCol)
    (hR : R.IsTriorthogonal) :
    EncodedCode (Qubit.QubitRegister LogicalRow)
      (Qubit.QubitRegister PhysicalCol) where
  code := R.cssQuantumCode
  encoding := R.encoding hR
def logicalXPauli (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow) :
    PauliSymplectic.Binary Col :=
  PauliSymplectic.cssXCheck (R.oddRow a)
def logicalZPauli (R : BinaryRowFamily OddRow EvenRow Col) (a : OddRow) :
    PauliSymplectic.Binary Col :=
  PauliSymplectic.cssZCheck (R.oddRow a)
noncomputable def logicalComputationalState (label : Qubit.Bitstring OddRow) :
    Qubit.QubitRegister OddRow :=
  EuclideanSpace.basisFun (Qubit.Bitstring OddRow) Complex label
noncomputable def encodedComputationalState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) : R.cssQuantumCode.carrier :=
  R.encoding hR (logicalComputationalState label)
noncomputable def logicalUniformScalar (Index : Type u) [Fintype Index] : Complex :=
  (Real.sqrt (Nat.card (Qubit.Bitstring Index) : Real) : Complex)⁻¹
noncomputable def logicalPlusState (Index : Type u) [Fintype Index] :
    Qubit.QubitRegister Index :=
  WithLp.toLp 2 fun _ => logicalUniformScalar Index
noncomputable def encodedPlusState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.cssQuantumCode.carrier :=
  R.encoding hR (logicalPlusState OddRow)
noncomputable def piDivFourPhase : Complex :=
  OneQubitMagic.phaseAmplitude (Real.pi / 4)
noncomputable def logicalMagicState (Index : Type u) [Fintype Index] :
    Qubit.QubitRegister Index :=
  WithLp.toLp 2 fun bits =>
    logicalUniformScalar Index *
      piDivFourPhase ^ HammingWeight (bitstringWordEquiv Index bits)
noncomputable def encodedMagicState
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    R.cssQuantumCode.carrier :=
  R.encoding hR (logicalMagicState OddRow)
attribute [-instance] Fintype.ofFinite
end BinaryRowFamily
end Triorthogonal
end Distillation
end QEC


