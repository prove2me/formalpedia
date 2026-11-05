-- Prove2me | Definitions.Def_CircuitLowerBound_Circ_Form
-- name    : CircuitLowerBound_Circ_Form
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:46:04.975203+00:00
-- url     : https://prove2.me/theorems/8201e35f-cc38-4871-87ea-e009b8645c24
-- title:
--   Form
-- statement:
--   Definitions and structural lemmas for Form, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound
open ENP Groundwork
namespace Form
def GE (a : ℕ → Bool) (N : ℕ) (K : List GateD) : Prop := ∀ t (h : t < K.length), a (N + t) = K[t].toGate.op (a K[t].2.1) (a K[t].2.2)
def gateCl (i : ℕ) (g : GateD) : Cnf :=
  [[(g.2.1, true), (g.2.2, true), (i, g.1.1)], [(g.2.1, true), (g.2.2, false), (i, g.1.2.1)],
   [(g.2.1, false), (g.2.2, true), (i, g.1.2.2.1)], [(g.2.1, false), (g.2.2, false), (i, g.1.2.2.2)]]
def dG : GateD := ((false, false, false, false), 0, 0)
def tseitin (n : ℕ) (K : List GateD) : Cnf := (List.range K.length).flatMap fun t => gateCl (n + t) (K.getD t dG)
def rho (L N : ℕ) (o : List ℕ) (off k : ℕ) : ℕ := if k < L then o.getD (off + k) 0 else N + (k - L)
def reloc (L N : ℕ) (o : List ℕ) (off : ℕ) (C : List GateD) : List GateD := C.map fun g => (g.1, rho L N o off g.2.1, rho L N o off g.2.2)
def xorT : Bool × Bool × Bool × Bool := (false, true, true, false)
def andT : Bool × Bool × Bool × Bool := (false, false, false, true)
def fin (L N c : ℕ) (o : List ℕ) : List GateD :=
  [(xorT, rho L N o 0 (L + c - 1), o.getD (0 + L) 0),
   (xorT, rho L (N + c) o (L + 1) (L + c - 1), o.getD (L + 1 + L) 0),
   (xorT, rho L (N + c + c) o (L + 1 + (L + 1)) (L + c - 1), o.getD (L + 1 + (L + 1) + L) 0),
   (andT, N + c + c + c, N + c + c + c + 1), (andT, N + c + c + c + 3, N + c + c + c + 2)]
def check (L N : ℕ) (G : List GateD) (o : List ℕ) (C : List GateD) : List GateD :=
  G ++ (reloc L N o 0 C ++ (reloc L (N + C.length) o (L + 1) C ++ (reloc L (N + C.length + C.length) o (L + 1 + (L + 1)) C ++ fin L N C.length o)))
def nF (e : MCode) (L : ℕ) : ℕ := min (nb e L) (rb e + L)
section Program
variable (B : MCode × List Unit × ℕ → List GateD × List ℕ)
def cK (q : (MCode × List Unit × ℕ) × List GateD) : List GateD :=
  check q.1.2.1.length (nF q.1.1 q.1.2.1.length + (B q.1).1.length) (B q.1).1 (B q.1).2 q.2
def F (q : (MCode × List Unit × ℕ) × List GateD) : List Unit × Cnf :=
  (List.replicate (nF q.1.1 q.1.2.1.length + (cK B q).length) (),
    (tseitin (nF q.1.1 q.1.2.1.length) (cK B q) ++ [[(nF q.1.1 q.1.2.1.length + (cK B q).length - 1, true)]]).dedup)
end Program
section Cert
variable {α : Type} [Enc α]
end Cert
end Form
open Form
end CircuitLowerBound


