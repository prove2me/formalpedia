-- Prove2me | Definitions.Def_K230_zfc
-- name    : K230_zfc
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:13:04.485249+00:00
-- url     : https://prove2.me/theorems/16da4040-24ac-4259-9d8d-7fe9bfb8e62e
-- title:
--   K230: the standard ZFC theory
-- statement:
--   The reference first-order ZFC theory `StandardZFC` in the minimal membership/equality signature: the ZF axioms (extensionality, empty set, pairing, union, power set, infinity, the separation and replacement schemes with closed instances, and the equality axioms) together with Foundation (`axReg'`) and Choice (`axAc'`). `ZFc` is ZF with closed schema instances; `StandardZFC φ := (ZFc φ ∨ φ = axReg') ∨ φ = axAc'`, exactly as in `KQuotZFC.v`. The axiom formulas port `minZF.v`, `Std_iface.v`, `regcon/MinZF.v` and `zfc/Z_wo.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KQuotZFC.v

import Definitions.Def_K230_fol
namespace K230
def isEset (t : Nat) : Form := .all (neg (mem 0 (t + 1)))
def isPair (x y t : Nat) : Form := .all (iff' (mem 0 (t + 1)) (.disj (eqf 0 (x + 1)) (eqf 0 (y + 1))))
def isUnion (x t : Nat) : Form := .all (iff' (mem 0 (t + 1)) (.ex (.conj (mem 0 (x + 2)) (mem 1 0))))
def sub' (x y : Nat) : Form := .all (.impl (mem 0 (x + 1)) (mem 0 (y + 1)))
def isPower (x t : Nat) : Form := .all (iff' (mem 0 (t + 1)) (sub' 0 (x + 1)))
def isSigma (x t : Nat) : Form := .all (iff' (mem 0 (t + 1)) (.disj (mem 0 (x + 1)) (eqf 0 (x + 1))))
def isInductive (t : Nat) : Form :=
  .conj (.ex (.conj (isEset 0) (mem 0 (t + 1))))
    (.all (.impl (mem 0 (t + 1)) (.ex (.conj (isSigma 1 0) (mem 0 (t + 2))))))
def isOm (t : Nat) : Form := .conj (isInductive t) (.all (.impl (isInductive 0) (sub' (t + 1) 0)))
def axExt' : Form := .all (.all (.impl (sub' 1 0) (.impl (sub' 0 1) (eqf 1 0))))
def axEset' : Form := .ex (isEset 0)
def axPair' : Form := .all (.all (.ex (isPair 2 1 0)))
def axUnion' : Form := .all (.ex (isUnion 1 0))
def axPower' : Form := .all (.ex (isPower 1 0))
def axOm' : Form := .ex (isOm 0)
def axSep' (φ : Form) : Form := .all (.ex (.all (iff' (mem 0 1) (.conj (mem 0 2) (subst φ (scons 0 (fun k => k + 3)))))))
def funRel' (φ : Form) : Form :=
  .all (.all (.all (.impl (subst φ (scons 2 (scons 1 (fun k => k + 3))))
    (.impl (subst φ (scons 2 (scons 0 (fun k => k + 3)))) (eqf 1 0)))))
def axRep' (φ : Form) : Form :=
  .impl (funRel' φ) (.all (.ex (.all (iff' (mem 0 1) (.ex (.conj (mem 0 3) (subst φ (scons 0 (scons 1 (fun k => k + 4))))))))))
def axReg' : Form := .all (.impl (.ex (mem 0 1)) (.ex (.conj (mem 0 1) (.all (.impl (mem 0 1) (neg (mem 0 2)))))))
def ACmat (x : Nat) : Form :=
  .impl (.all (.impl (mem 0 (x + 1)) (.ex (mem 0 1))))
    (.impl (.all (.impl (mem 0 (x + 1)) (.all (.impl (mem 0 (x + 2)) (.impl (neg (eqf 1 0)) (neg (.ex (.conj (mem 0 2) (mem 0 1)))))))))
      (.ex (.all (.impl (mem 0 (x + 2)) (.ex (.conj (mem 0 1) (.conj (mem 0 2) (.all (.impl (mem 0 2) (.impl (mem 0 3) (eqf 0 1)))))))))))
def axAc' : Form := .all (ACmat 0)
def ZF0base : List Form := [axRefl', axSym', axTrans', axEqElem', axExt', axEset', axPair', axUnion', axPower']
inductive ZF0 : Form → Prop where
  | base {φ : Form} : φ ∈ ZF0base → ZF0 φ
  | sep (φ : Form) (n : Nat) : closedf (forallTimes n (axSep' φ)) → ZF0 (forallTimes n (axSep' φ))
  | rep (φ : Form) (n : Nat) : closedf (forallTimes n (axRep' φ)) → ZF0 (forallTimes n (axRep' φ))
def ZFc (φ : Form) : Prop := ZF0 φ ∨ φ = axOm'
def StandardZFC (φ : Form) : Prop := (ZFc φ ∨ φ = axReg') ∨ φ = axAc'
end K230


