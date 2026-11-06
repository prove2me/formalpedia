-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
-- name    : QEC_Coding_CodeReduction_Classical_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:07:28.371662+00:00
-- url     : https://prove2.me/theorems/3e1ca05c-b6e4-48fc-9bf8-a4361fc102c1
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/Classical/Core.lean

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
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
abbrev Incidence := { edge : Check × Bit // R edge.1 edge.2 }
abbrev BitNeighbor (b : Bit) := { c : Check // R c b }
abbrev CheckNeighbor (c : Check) := { b : Bit // R c b }
noncomputable def bitNeighborOrder (b : Bit) :
    Fin (Fintype.card (BitNeighbor R b)) ≃ BitNeighbor R b :=
  (Fintype.equivFin (BitNeighbor R b)).symm
noncomputable def checkNeighborOrder (c : Check) :
    Fin (Fintype.card (CheckNeighbor R c)) ≃ CheckNeighbor R c :=
  (Fintype.equivFin (CheckNeighbor R c)).symm
noncomputable def bitIncidenceAt (b : Bit)
    (i : Fin (Fintype.card (BitNeighbor R b))) : Incidence R :=
  ⟨((bitNeighborOrder R b i).1, b), (bitNeighborOrder R b i).2⟩
noncomputable def checkIncidenceAt (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) : Incidence R :=
  ⟨(c, (checkNeighborOrder R c i).1), (checkNeighborOrder R c i).2⟩
noncomputable def bitPosition (e : Incidence R) :
    Fin (Fintype.card (BitNeighbor R e.1.2)) :=
  (bitNeighborOrder R e.1.2).symm ⟨e.1.1, e.2⟩
noncomputable def checkPosition (e : Incidence R) :
    Fin (Fintype.card (CheckNeighbor R e.1.1)) :=
  (checkNeighborOrder R e.1.1).symm ⟨e.1.2, e.2⟩
omit [DecidableEq Check] [Fintype Bit] [DecidableEq Bit] in
@[simp]
theorem bitIncidenceAt_bitPosition (e : Incidence R) :
    bitIncidenceAt R e.1.2 (bitPosition R e) = e := by
  apply Subtype.ext
  simp [bitIncidenceAt, bitPosition]
omit [Fintype Check] [DecidableEq Check] [DecidableEq Bit] in
@[simp]
theorem checkIncidenceAt_checkPosition (e : Incidence R) :
    checkIncidenceAt R e.1.1 (checkPosition R e) = e := by
  apply Subtype.ext
  simp [checkIncidenceAt, checkPosition]
omit [DecidableEq Check] [Fintype Bit] [DecidableEq Bit] in
@[simp]
theorem bitPosition_bitIncidenceAt (b : Bit)
    (i : Fin (Fintype.card (BitNeighbor R b))) :
    bitPosition R (bitIncidenceAt R b i) = i := by
  exact (bitNeighborOrder R b).symm_apply_apply i
omit [Fintype Check] [DecidableEq Check] [DecidableEq Bit] in
@[simp]
theorem checkPosition_checkIncidenceAt (c : Check)
    (i : Fin (Fintype.card (CheckNeighbor R c))) :
    checkPosition R (checkIncidenceAt R c i) = i := by
  exact (checkNeighborOrder R c).symm_apply_apply i
def pathLeft {n : Nat} (j : Fin (n - 1)) : Fin n :=
  ⟨j.1, by omega⟩
def pathRight {n : Nat} (j : Fin (n - 1)) : Fin n :=
  ⟨j.1 + 1, by omega⟩
def optionalSingle {Index : Type*} [DecidableEq Index]
    (o : Option Index) : Word F Index :=
  match o with
  | none => 0
  | some i => Pi.single i 1
def pathPrevious {n : Nat} (i : Fin n) : Option (Fin (n - 1)) :=
  if h : 0 < i.1 then some ⟨i.1 - 1, by omega⟩ else none
def pathNext {n : Nat} (i : Fin n) : Option (Fin (n - 1)) :=
  if h : i.1 + 1 < n then some ⟨i.1, by omega⟩ else none
omit [Fintype F] [DecidableEq F] [Fintype Bit] in
@[simp]
theorem optionalSingle_pathPrevious_apply {n : Nat} (i : Fin n)
    (j : Fin (n - 1)) :
    optionalSingle (F := F) (pathPrevious i) j =
      if pathRight j = i then 1 else 0 := by
  classical
  by_cases hi : 0 < i.1
  · by_cases hRight : pathRight j = i
    · subst i
      simp [pathPrevious, optionalSingle, pathRight]
    · have hne : (⟨i.1 - 1, by omega⟩ : Fin (n - 1)) ≠ j := by
        intro h
        apply hRight
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simp [pathRight]
        omega
      simp [pathPrevious, hi, optionalSingle, hRight, hne]
  · have hRight : pathRight j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [pathRight] at hv
      omega
    simp [pathPrevious, hi, optionalSingle, hRight]
omit [Fintype F] [DecidableEq F] [Fintype Bit] in
@[simp]
theorem optionalSingle_pathNext_apply {n : Nat} (i : Fin n)
    (j : Fin (n - 1)) :
    optionalSingle (F := F) (pathNext i) j =
      if pathLeft j = i then 1 else 0 := by
  classical
  by_cases hi : i.1 + 1 < n
  · by_cases hLeft : pathLeft j = i
    · subst i
      have hj : j.1 + 1 < n := by omega
      simp [pathNext, optionalSingle, pathLeft, hj]
    · have hne : (⟨i.1, by omega⟩ : Fin (n - 1)) ≠ j := by
        intro h
        apply hLeft
        ext
        have hv := congrArg Fin.val h
        simp only at hv
        simpa [pathLeft] using hv.symm
      simp [pathNext, hi, optionalSingle, hLeft, hne]
  · have hLeft : pathLeft j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [pathLeft] at hv
      omega
    simp [pathNext, hi, optionalSingle, hLeft]
omit [Fintype F] [DecidableEq F] [Fintype Check] in
@[simp]
theorem optionalSingle_map_inr_apply_inl
    {Left Right Source : Type*} [DecidableEq (Left ⊕ Right)]
    (o : Option Source) (f : Source → Right) (x : Left) :
    optionalSingle (F := F) (o.map (fun y => Sum.inr (f y))) (Sum.inl x) = 0 := by
  cases o <;> simp [optionalSingle]
abbrev AuxiliaryCheck :=
  Σ b : Bit, Fin (Fintype.card (BitNeighbor R b) - 1)
abbrev AuxiliaryBit :=
  Σ c : Check, Fin (Fintype.card (CheckNeighbor R c) - 1)
abbrev WeightReducedBit := Incidence R ⊕ AuxiliaryBit R
abbrev WeightReducedCheck := Incidence R ⊕ AuxiliaryCheck R
def auxiliaryCheckIndex (b : Bit)
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    WeightReducedCheck R :=
  Sum.inr ⟨b, j⟩
def auxiliaryBitIndex (c : Check)
    (j : Fin (Fintype.card (CheckNeighbor R c) - 1)) :
    WeightReducedBit R :=
  Sum.inr ⟨c, j⟩
omit [Fintype F] [DecidableEq F] [Fintype Bit] in
@[simp]
theorem optionalSingle_map_auxiliaryCheckIndex_apply_same
    (b : Bit) (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (j : Fin (Fintype.card (BitNeighbor R b) - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryCheckIndex R b))
        (Sum.inr ⟨b, j⟩) = optionalSingle (F := F) o j := by
  cases o with
  | none => rfl
  | some k =>
      by_cases hk : k = j
      · subst j
        simp [optionalSingle, auxiliaryCheckIndex]
      · have hs : (Sum.inr ⟨b, k⟩ : WeightReducedCheck R) ≠ Sum.inr ⟨b, j⟩ := by
          intro h
          apply hk
          exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h) |>.2)
        simp [optionalSingle, auxiliaryCheckIndex, hk, hs]
omit [Fintype F] [DecidableEq F] [Fintype Check] in
@[simp]
theorem optionalSingle_map_auxiliaryBitIndex_apply_same
    (c : Check) (o : Option (Fin (Fintype.card (CheckNeighbor R c) - 1)))
    (j : Fin (Fintype.card (CheckNeighbor R c) - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryBitIndex R c))
        (Sum.inr ⟨c, j⟩) = optionalSingle (F := F) o j := by
  cases o with
  | none => rfl
  | some k =>
      by_cases hk : k = j
      · subst j
        simp [optionalSingle, auxiliaryBitIndex]
      · have hs : (Sum.inr ⟨c, k⟩ : WeightReducedBit R) ≠ Sum.inr ⟨c, j⟩ := by
          intro h
          apply hk
          exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h) |>.2)
        simp [optionalSingle, auxiliaryBitIndex, hk, hs]
noncomputable def primaryBitBoundary (e : Incidence R) :
    Word F (WeightReducedCheck R) :=
  Pi.single (Sum.inl e) 1 +
    optionalSingle (F := F)
      ((pathPrevious (bitPosition R e)).map (auxiliaryCheckIndex R e.1.2)) +
    optionalSingle (F := F)
      ((pathNext (bitPosition R e)).map (auxiliaryCheckIndex R e.1.2))
noncomputable def auxiliaryBitBoundary (a : AuxiliaryBit R) :
    Word F (WeightReducedCheck R) :=
  Pi.single
      (Sum.inl (checkIncidenceAt R a.1 (pathLeft a.2))) 1 +
    Pi.single
      (Sum.inl (checkIncidenceAt R a.1 (pathRight a.2))) 1
noncomputable def primaryCheckCoboundary (e : Incidence R) :
    Word F (WeightReducedBit R) :=
  Pi.single (Sum.inl e) 1 +
    optionalSingle (F := F)
      ((pathPrevious (checkPosition R e)).map (auxiliaryBitIndex R e.1.1)) +
    optionalSingle (F := F)
      ((pathNext (checkPosition R e)).map (auxiliaryBitIndex R e.1.1))
noncomputable def auxiliaryCheckCoboundary (a : AuxiliaryCheck R) :
    Word F (WeightReducedBit R) :=
  Pi.single
      (Sum.inl (bitIncidenceAt R a.1 (pathLeft a.2))) 1 +
    Pi.single
      (Sum.inl (bitIncidenceAt R a.1 (pathRight a.2))) 1
noncomputable def basisCoboundary : WeightReducedCheck R →
    Word F (WeightReducedBit R)
  | Sum.inl e => primaryCheckCoboundary (F := F) R e
  | Sum.inr a => auxiliaryCheckCoboundary (F := F) R a
noncomputable def basisBoundary : WeightReducedBit R →
    Word F (WeightReducedCheck R)
  | Sum.inl e => primaryBitBoundary (F := F) R e
  | Sum.inr a => auxiliaryBitBoundary (F := F) R a
noncomputable def linearMapOfBasisImages
    {Source : Type*} {Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (image : Source → Word F Target) :
    Word F Source →ₗ[F] Word F Target where
  toFun x := ∑ i : Source, x i • image i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' coefficient x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply]
    simp only [smul_eq_mul]
noncomputable def boundary :
    Word F (WeightReducedBit R) →ₗ[F]
      Word F (WeightReducedCheck R) :=
  linearMapOfBasisImages (F := F) (basisBoundary (F := F) R)
noncomputable def originalBasisBoundary (b : Bit) : Word F Check :=
  fun c => if R c b then 1 else 0
noncomputable def originalBoundary : Word F Bit →ₗ[F] Word F Check :=
  linearMapOfBasisImages (F := F) (originalBasisBoundary (F := F) R)
section SameUniverseComplex
universe x
variable {F₀ Check₀ Bit₀ : Type x}
variable [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable [Fintype Check₀] [DecidableEq Check₀]
variable [Fintype Bit₀] [DecidableEq Bit₀]
variable (R₀ : Check₀ → Bit₀ → Prop) [DecidableRel R₀]
noncomputable def originalComplex :
    ChainComplexData F₀ (Word F₀ Check₀) (Word F₀ Bit₀)
      (Word F₀ (Fin 0)) where
  boundary1 := originalBoundary (F := F₀) R₀
  boundary2 := 0
  boundary_squared := by simp
noncomputable def weightReducedComplex :
    ChainComplexData F₀ (Word F₀ (WeightReducedCheck R₀))
      (Word F₀ (WeightReducedBit R₀)) (Word F₀ (Fin 0)) where
  boundary1 := boundary (F := F₀) R₀
  boundary2 := 0
  boundary_squared := by simp
end SameUniverseComplex
end QEC.Coding.ClassicalWeightReduction


