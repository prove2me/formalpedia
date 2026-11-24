-- Prove2me | Definitions.Def_InverseZeroSum_Candidate3
-- name    : InverseZeroSum_Candidate3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:21:51.679459+00:00
-- url     : https://prove2.me/theorems/4b2a6db9-6b6c-4926-b432-beec6f728603
-- title:
--   Candidate3
-- statement:
--   Definitions and structural lemmas for Candidate3, from John Fairfax-Ball (jfairfaxball-348/Inverse-Zero-Sum-Research; see pinned Apache-2.0 LICENSE)'s pinned Inverse zero-sum classification in C_3^3 for length-24 sequences development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace InverseZeroSum.Candidate3
abbrev G := Fin 3 → ZMod 3
abbrev Alphabet := {x : G // x ≠ 0}
abbrev PosSeq (n : ℕ) := Fin n → Alphabet
def posSum {n : ℕ} (S : PosSeq n) (I : Finset (Fin n)) : G :=
  ∑ i ∈ I, (S i : G)
def ShortZero {n : ℕ} (S : PosSeq n) (I : Finset (Fin n)) : Prop :=
  I.Nonempty ∧ I.card ≤ 3 ∧ posSum S I = 0
def ShortFree {n : ℕ} (S : PosSeq n) : Prop :=
  ∀ I : Finset (Fin n), ¬ ShortZero S I
def Squarefree {n : ℕ} (S : PosSeq n) : Prop :=
  Function.Injective S
def innerJointSum {n : ℕ} (S : PosSeq n)
    (I J : Finset (Fin n)) : G :=
  posSum S (I ∩ J)
def AvoidsInnerJointPair {n : ℕ} (S : PosSeq n) : Prop :=
  ∀ I J : Finset (Fin n),
    ShortZero S I → ShortZero S J → innerJointSum S I J = 0
@[expose] def baseIndex (i : Fin 24) : Fin 8 :=
  ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
def tripleRep (U : PosSeq 8) : PosSeq 24 :=
  fun i => U (baseIndex i)
def IsTriplePower (S : PosSeq 24) (U : PosSeq 8) : Prop :=
  ∃ e : Fin 24 ≃ Fin 24, ∀ i, S (e i) = tripleRep U i
def totalSum {n : ℕ} (S : PosSeq n) : G :=
  posSum S Finset.univ
def FrozenClassification : Prop :=
  ∀ S : PosSeq 24,
    AvoidsInnerJointPair S ↔
      ∃ U : PosSeq 8,
        Squarefree U ∧ ShortFree U ∧ IsTriplePower S U
def Length16SumZeroInput : Prop :=
  ∀ R : PosSeq 16, ShortFree R → totalSum R = 0
def ThreeTerm19Input : Prop :=
  ∀ R : PosSeq 19, ∃ I : Finset (Fin 19), I.card = 3 ∧ posSum R I = 0
def Eta17Input : Prop :=
  ∀ R : PosSeq 17, ∃ I : Finset (Fin 17), ShortZero R I
def Length15NonzeroInput : Prop :=
  ∀ R : PosSeq 15, ShortFree R → totalSum R ≠ 0
def ShortFreeOn {n : ℕ} (S : PosSeq n) (A : Finset (Fin n)) : Prop :=
  ∀ I : Finset (Fin n), I ⊆ A → ¬ ShortZero S I
def S039Signature (l s r : ℕ) : Prop :=
  (l = 6 ∧ s = 8 ∧ r = 2) ∨
  (l = 7 ∧ s = 8 ∧ r = 1) ∨
  (l = 8 ∧ s = 8 ∧ r = 0) ∨
  (l = 6 ∧ s = 9 ∧ r = 0)
def blockUnion {s : ℕ} (blocks : Fin s → Finset (Fin 24)) : Finset (Fin 24) :=
  Finset.univ.biUnion blocks
def representativeSet {s : ℕ} (rep : Fin s → Fin 24) : Finset (Fin 24) :=
  Finset.univ.image rep
structure S039PackingCertificate (S : PosSeq 24) where
  s : ℕ
  l : ℕ
  r : ℕ
  signature : S039Signature l s r
  blocks : Fin s → Finset (Fin 24)
  block_shortZero : ∀ j, ShortZero S (blocks j)
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)
  block_card : ∀ j, (blocks j).card = (if j.val < l then 3 else 2)
  remainder_card : (Finset.univ \ blockUnion blocks).card = r
  every_representative_residual_shortFree :
    ∀ rep : Fin s → Fin 24,
      (∀ j, rep j ∈ blocks j) →
      ShortFreeOn S (Finset.univ \ representativeSet rep)
def S039PackingInput : Prop :=
  ∀ S : PosSeq 24, AvoidsInnerJointPair S → Nonempty (S039PackingCertificate S)
def pullSeq {m n : ℕ} (S : PosSeq n) (e : Fin m ↪ Fin n) : PosSeq m :=
  fun i => S (e i)
noncomputable def s039AllBlocks (S : PosSeq 24) : Finset (Finset (Fin 24)) := by
  classical
  exact Finset.univ.filter (ShortZero S)
abbrev F3G := Fin 3 → Fin 3
abbrev F3T := Fin 3 × Fin 3 × Fin 3
def f3ToG : F3G ≃+ G :=
  AddEquiv.piCongrRight (fun _ => (ZMod.finEquiv 3).toAddEquiv)
def f3TupleEquiv : F3G ≃+ F3T where
  toFun x := (x 0, x 1, x 2)
  invFun x := ![x.1, x.2.1, x.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨x0, x1, x2⟩
    rfl
  map_add' x y := rfl
def finiteModelEquiv : G ≃+ F3T :=
  f3ToG.symm.trans f3TupleEquiv
abbrev PlaneCoord := Fin 3 × Fin 3
abbrev PlaneIdx := Fin 13 × Fin 3
def planeValueT (d : Fin 13) (x : F3T) : Fin 3 :=
  let k := d.val
  if h9 : k < 9 then
    let a : Fin 3 := ⟨k / 3, by omega⟩
    let b : Fin 3 := ⟨k % 3, Nat.mod_lt _ (by omega)⟩
    x.1 + a * x.2.1 + b * x.2.2
  else if h12 : k < 12 then
    let b : Fin 3 := ⟨k - 9, by omega⟩
    x.2.1 + b * x.2.2
  else
    x.2.2
def onPlaneTB (p : PlaneIdx) (x : F3T) : Bool :=
  planeValueT p.1 x == p.2
def planePointT (p : PlaneIdx) (q : PlaneCoord) : F3T :=
  let d := p.1.val
  let c : Fin 3 := p.2
  let y : Fin 3 := q.1
  let z : Fin 3 := q.2
  if h9 : d < 9 then
    let a : Fin 3 := ⟨d / 3, by omega⟩
    let b : Fin 3 := ⟨d % 3, Nat.mod_lt _ (by omega)⟩
    (c - a * y - b * z, y, z)
  else if h12 : d < 12 then
    let b : Fin 3 := ⟨d - 9, by omega⟩
    (y, c - b * z, z)
  else
    (y, z, c)
def planeSetT (p : PlaneIdx) : Finset F3T :=
  Finset.univ.filter (fun x => onPlaneTB p x = true)
def IsCapT (A : Finset F3T) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0
def thirdCoordT (x : F3T) : Fin 3 := x.2.2
def horizontalPlaneT (c : Fin 3) : PlaneIdx :=
  (⟨12, by omega⟩, c)
def horizontalSliceT (A : Finset F3T) (c : Fin 3) : Finset F3T :=
  A.filter (fun x => thirdCoordT x = c)
def tupleValueT {n : ℕ} (R : PosSeq n) (i : Fin n) : F3T :=
  finiteModelEquiv (R i : G)
def tupleSupportT {n : ℕ} (R : PosSeq n) : Finset F3T :=
  (Finset.univ : Finset (Fin n)).image (tupleValueT R)
def directionSliceT (A : Finset F3T) (d : Fin 13) (c : Fin 3) : Finset F3T :=
  A.filter (fun x => planeValueT d x = c)
def S8RepresentativeSwapOutput (S : PosSeq 24)
    (c : S039PackingCertificate S) : Prop :=
  c.l = 8 ∧ c.r = 0 ∧
    ∀ j : Fin c.s, ∀ x ∈ c.blocks j, ∀ y ∈ c.blocks j, S x = S y
def S8RepresentativeSwapInput : Prop :=
  ∀ S : PosSeq 24, ∀ c : S039PackingCertificate S,
    c.s = 8 → S8RepresentativeSwapOutput S c
set_option maxHeartbeats 500000
def S9PackingEliminationInput : Prop :=
  ∀ S : PosSeq 24, ∀ c : S039PackingCertificate S, c.s = 9 → False
def S9SwapCountShape (A : Finset (Fin 24)) (f : Fin 24 → F3T)
    (a b : F3T) : Prop :=
  ((A.filter (fun i => f i = a)).card = 0 ∧
    (A.filter (fun i => f i = b)).card = 1) ∨
  ((A.filter (fun i => f i = a)).card = 1 ∧
    (A.filter (fun i => f i = b)).card = 2)
end InverseZeroSum.Candidate3


