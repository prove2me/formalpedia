-- Prove2me | Definitions.Def_CircuitLowerBound_Circ_Clause
-- name    : CircuitLowerBound_Circ_Clause
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:43:42.657809+00:00
-- url     : https://prove2.me/theorems/815b26eb-5af8-4364-89b5-090e69b2e81f
-- title:
--   Clause
-- statement:
--   Definitions and structural lemmas for Clause, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_testBit
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
namespace CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
def litI (c : TCl) (ι : ℕ) : TLit := if ι = 0 then c.1 else if ι = 1 then c.2.1 else c.2.2
def fbit (kbm : ℕ) (l : TLit) (f : ℕ) : Bool :=
  if f = 0 then l.2.1.testBit 0 else if f = 1 then l.2.1.testBit 1 else if f = 2 then l.2.2.1.testBit 0 else if f = 3 then l.2.2.1.testBit 1
  else if f = 4 then l.2.2.2.2 else if f < 5 + kbm then l.1.testBit (f - 5) else l.2.2.2.1.testBit (f - 5 - kbm)
def Ew (n rb k : ℕ) : ℕ := prevW (n + 2 + rb * k) (n + 1) rb
def selGate (n bq bt rb k i : ℕ) : GateD := ((if k.testBit i then opAnd else opAndN), prevW (n + 2 + rb * k) (n + 1) i, bq + bt + i)
def selChain (n bq bt rb k : ℕ) : List GateD := (List.range rb).map (selGate n bq bt rb k)
def selG (n bq bt rb R : ℕ) : List GateD := (List.range R).flatMap (selChain n bq bt rb)
def Fw (n rb R nf ι f : ℕ) : ℕ := prevW (n + 2 + rb * R + R * (ι * nf + f)) n R
def fldGate (n rb kbm nf : ℕ) (tb : List TCl) (a k : ℕ) : GateD :=
  ((if fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) then opOr else opFst), prevW (n + 2 + rb * tb.length + tb.length * a) n k, Ew n rb k)
def fldChain (n rb kbm nf : ℕ) (tb : List TCl) (a : ℕ) : List GateD := (List.range tb.length).map (fldGate n rb kbm nf tb a)
def fldG (n rb kbm nf : ℕ) (tb : List TCl) : List GateD := (List.range (3 * nf)).flatMap (fldChain n rb kbm nf tb)
def cinT (a i : ℕ) : ℕ := if i = 0 then a + 1 else a + 3 + 3 * (i - 1) + 2
def cinQ (z b i : ℕ) : ℕ := if i = 0 then z else b + 1 + 7 * (i - 1) + 6
def timeBit (bq a i : ℕ) : List GateD := [(opAnd, a, bq + i), (opXor, a + 3 + 3 * i, cinT a i), (opAnd, a + 3 + 3 * i, cinT a i)]
def timeG (bq bt a m0 m1 : ℕ) : List GateD :=
  [(opXor, m0, m1), (opAndN, m1, m0), (opAnd, m0, m1)] ++ (List.range bt).flatMap (timeBit bq a) ++ [(opOr, cinT a bt, a + 2)]
def posBit (z bq P b p1 : ℕ) (dW : ℕ → ℕ) (i : ℕ) : List GateD :=
  [(opAnd, b, if i < bq then i else z), ((if P.testBit i then opOr else opFst), b + 1 + 7 * i, p1), (opXor, b + 1 + 7 * i + 1, dW i),
   (opXor, b + 1 + 7 * i + 2, cinQ z b i), (opAnd, b + 1 + 7 * i + 1, dW i), (opAnd, b + 1 + 7 * i + 2, cinQ z b i),
   (opOr, b + 1 + 7 * i + 4, b + 1 + 7 * i + 5)]
def posG (z bq P b p0 p1 : ℕ) (dW : ℕ → ℕ) : List GateD := [(opAndN, p0, p1)] ++ (List.range (bq + 1)).flatMap (posBit z bq P b p1 dW)
def szL (bq bt : ℕ) : ℕ := 3 * bt + 7 * bq + 12
def offA (n bq bt rb R nf ι : ℕ) : ℕ := n + 2 + rb * R + R * (3 * nf) + szL bq bt * ι
def dWire (n rb R kbm Dq ι i : ℕ) : ℕ := if i < Dq then Fw n rb R (5 + kbm + Dq) ι (5 + kbm + i) else n
def litG (n bq bt rb R kbm Dq P ι : ℕ) : List GateD :=
  timeG bq bt (offA n bq bt rb R (5 + kbm + Dq) ι) (Fw n rb R (5 + kbm + Dq) ι 0) (Fw n rb R (5 + kbm + Dq) ι 1) ++
    posG n bq P (offA n bq bt rb R (5 + kbm + Dq) ι + 4 + 3 * bt) (Fw n rb R (5 + kbm + Dq) ι 2) (Fw n rb R (5 + kbm + Dq) ι 3) (dWire n rb R kbm Dq ι)
def gatesC (n bq bt rb kbm Dq P : ℕ) (tb : List TCl) : List GateD :=
  [(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length ++ fldG n rb kbm (5 + kbm + Dq) tb ++
    (List.range 3).flatMap (litG n bq bt rb tb.length kbm Dq P)
def outsL (n bq bt rb R kbm Dq L ι : ℕ) : List ℕ :=
  ((List.range (bq + 1)).map fun i => offA n bq bt rb R (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3) ++
    ((List.range bt).map fun i => offA n bq bt rb R (5 + kbm + Dq) ι + 3 + 3 * i + 1) ++ [offA n bq bt rb R (5 + kbm + Dq) ι + 3 + 3 * bt] ++
    ((List.range kbm).map fun i => Fw n rb R (5 + kbm + Dq) ι (5 + i)) ++ ((List.range (L - (bq + bt + 2 + kbm))).map fun _ => n) ++
    [Fw n rb R (5 + kbm + Dq) ι 4]
def dSum (tb : List TCl) : ℕ := (tb.map fun c => c.1.2.2.2.1 + c.2.1.2.2.2.1 + c.2.2.2.2.2.1).sum
def coreB (n bq bt rb kbm Dq L P : ℕ) (tb : List TCl) : List GateD × List ℕ :=
  (gatesC n bq bt rb kbm Dq P tb, (List.range 3).flatMap (outsL n bq bt rb tb.length kbm Dq L))
def B (x : MCode × List Unit × ℕ) : List GateD × List ℕ :=
  coreB (nb x.1 x.2.1.length) (min (bq x.1 x.2.1.length) x.2.1.length) (bt x.1 x.2.1.length) (rb x.1) (min (kb x.1) x.2.1.length)
    (min (Nat.size (dSum (tab x.1))) (min (bq x.1 x.2.1.length) x.2.1.length + 1)) x.2.1.length x.2.2 (tab x.1)
section poly
variable {α : Type} [Enc α]
end poly
end CircuitLowerBound.Clause
namespace CircuitLowerBound
open ENP Groundwork CircuitLowerBound.Blocks CircuitLowerBound.Clause
end CircuitLowerBound


