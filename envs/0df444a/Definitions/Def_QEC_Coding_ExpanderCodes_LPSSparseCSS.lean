-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
-- name    : QEC_Coding_ExpanderCodes_LPSSparseCSS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:09:31.561789+00:00
-- url     : https://prove2.me/theorems/b2ec22aa-8bc4-4e48-a100-de482fe7e9d3
-- title:
--   LPSSparse CSS
-- statement:
--   Definitions and structural lemmas for LPSSparse CSS, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_980d0372b5_23 (q : ℕ) [Fact q.Prime] : DecidableEq PSL(2, ZMod q) := lpsPSLDecidableEq q
abbrev LPSSparseGroupIndex (q : ℕ) [Fact q.Prime] := Fin (lpsPSLList q).length
abbrev LPSSparseQubitIndex (q D r r' : ℕ) [Fact q.Prime] :=
  Sum (Fin D × Fin D × LPSSparseGroupIndex q) (Fin (2 * r) × Fin (2 * r') × LPSSparseGroupIndex q)
abbrev LPSSparseXIndex (q D r : ℕ) [Fact q.Prime] := Fin (2 * r) × Fin D × LPSSparseGroupIndex q
abbrev LPSSparseZIndex (q D r' : ℕ) [Fact q.Prime] := Fin D × Fin (2 * r') × LPSSparseGroupIndex q
def lpsSparseVoltage {q D : ℕ} [Fact q.Prime] (label : Fin D → LPSSparseGroupIndex q)
    (side : Fin 2) (j : Fin D) : LPSSparseGroupIndex q :=
  if side = 0 then lpsPSLIndexOne q else label j
def lpsSparseXRow {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r) :
    List (LPSSparseQubitIndex q D r r' × F) :=
  let ar := finProdFinEquiv.symm row.1
  (List.ofFn fun ac : Fin D =>
    (Sum.inl (ac, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsPSLIndexInv q (lpsSparseVoltage label ar.1 ac))), h ar.2 ac)) ++
  (List.ofFn fun bc : Fin (2 * r') =>
    let bcPair := finProdFinEquiv.symm bc
    (Sum.inr (row.1, bc, lpsPSLIndexMul q
      (lpsSparseVoltage label bcPair.1 row.2.1) row.2.2), -h' bcPair.2 row.2.1))
def lpsSparseZRow {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r') :
    List (LPSSparseQubitIndex q D r r' × F) :=
  let bc := finProdFinEquiv.symm row.2.1
  (List.ofFn fun br : Fin D =>
    (Sum.inl (row.1, br, lpsPSLIndexMul q
      (lpsPSLIndexInv q (lpsSparseVoltage label bc.1 br)) row.2.2), h' bc.2 br)) ++
  (List.ofFn fun ar : Fin (2 * r) =>
    let arPair := finProdFinEquiv.symm ar
    (Sum.inr (ar, row.2.1, lpsPSLIndexMul q row.2.2
      (lpsSparseVoltage label arPair.1 row.1)), h arPair.2 row.1))
def lpsSparseRowValue {Q F : Type} [DecidableEq Q] [AddCommMonoid F]
    (row : List (Q × F)) (q : Q) : F :=
  (row.map fun entry => if entry.1 = q then entry.2 else 0).sum
def lpsSparseQubitDecode {q D r r' : ℕ} [Fact q.Prime] :
    LPSSparseQubitIndex q D r r' →
      LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
        (Fin 2 × Fin r') PSL(2, ZMod q)
  | Sum.inl (ac, br, g) => Sum.inl (ac, br, (lpsPSLEnumerationEquiv q) g)
  | Sum.inr (ar, bc, g) => Sum.inr (finProdFinEquiv.symm ar,
      finProdFinEquiv.symm bc, (lpsPSLEnumerationEquiv q) g)
def lpsSparseXDecode {q D r : ℕ} [Fact q.Prime] (row : LPSSparseXIndex q D r) :
    LiftedProduct.C0Index (Fin 2 × Fin r) (Fin D) PSL(2, ZMod q) :=
  (finProdFinEquiv.symm row.1, row.2.1, (lpsPSLEnumerationEquiv q) row.2.2)
def lpsSparseZDecode {q D r' : ℕ} [Fact q.Prime] (row : LPSSparseZIndex q D r') :
    LiftedProduct.C2Index (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q) :=
  (row.1, finProdFinEquiv.symm row.2.1, (lpsPSLEnumerationEquiv q) row.2.2)
def lpsSparseQubitEquiv {q D r r' : ℕ} [Fact q.Prime] :
    LPSSparseQubitIndex q D r r' ≃
      LiftedProduct.QubitIndex (Fin 2 × Fin r) (Fin D) (Fin D)
        (Fin 2 × Fin r') PSL(2, ZMod q) :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
      (lpsPSLEnumerationEquiv q)))
    (Equiv.prodCongr finProdFinEquiv.symm
      (Equiv.prodCongr finProdFinEquiv.symm (lpsPSLEnumerationEquiv q)))
def lpsSparseTripleEquiv (a b c : ℕ) :
    (Fin a × Fin b × Fin c) ≃ Fin (a * (b * c)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv
def lpsSparseQubitNumbering {q D r r' : ℕ} [Fact q.Prime] :
    LPSSparseQubitIndex q D r r' ≃
      Fin (D * (D * (lpsPSLList q).length) + (2 * r) * ((2 * r') * (lpsPSLList q).length)) :=
  (Equiv.sumCongr (lpsSparseTripleEquiv _ _ _) (lpsSparseTripleEquiv _ _ _)).trans
    finSumFinEquiv
def lpsSparseXOutput {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :=
  List.ofFn fun i : Fin ((2 * r) * (D * (lpsPSLList q).length)) =>
    (lpsSparseXRow label h h' ((lpsSparseTripleEquiv _ _ _).symm i)).map
      (fun e => (lpsSparseQubitNumbering e.1, e.2))
def lpsSparseZOutput {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :=
  List.ofFn fun i : Fin (D * ((2 * r') * (lpsPSLList q).length)) =>
    (lpsSparseZRow label h h' ((lpsSparseTripleEquiv _ _ _).symm i)).map
      (fun e => (lpsSparseQubitNumbering e.1, e.2))
def lpsEffectiveSparseXRow {p D r r' : ℕ} {F : Type} [Field F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r) :=
  lpsSparseXRow (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' x
def lpsEffectiveSparseZRow {p D r r' : ℕ} {F : Type} [Field F]
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex (lpsEffectiveResiduePrimeAt hp hp4 n).q D r') :=
  lpsSparseZRow (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j)) h h' z
end QEC.Coding.TannerLiftedProduct


