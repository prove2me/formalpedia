-- Prove2me | Definitions.Def_CircuitLowerBound_InterfacesPolyT
-- name    : CircuitLowerBound_InterfacesPolyT
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:53:41.885573+00:00
-- url     : https://prove2.me/theorems/bbc5a461-67f4-437e-97f3-a6f37c1295ca
-- title:
--   Interfaces Poly T
-- statement:
--   Definitions and structural lemmas for Interfaces Poly T, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/InterfacesPolyT.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Definitions.Def_ToTuring_PolyT
set_option autoImplicit false
section
section
namespace CircuitLowerBound
open ENP Groundwork Turing
abbrev GateD : Type := (Bool × Bool × Bool × Bool) × ℕ × ℕ
def GateD.toGate (g : GateD) : Gate :=
  ⟨fun x y => if x then (if y then g.1.2.2.2 else g.1.2.2.1) else (if y then g.1.2.1 else g.1.1), g.2.1, g.2.2⟩
def toC (C : List GateD) : Circuit := C.map GateD.toGate
def WF (n : ℕ) (C : List GateD) : Prop := ∀ (t : ℕ) (h : t < C.length), C[t].2.1 < n + t ∧ C[t].2.2 < n + t
def StNorm : Prop := ∀ (m : ℕ) (C : Circuit), 1 ≤ m → ∃ C' : List GateD, WF m C' ∧ C'.length = C.length ∧ ∀ x : List Bool, x.length = m → eval (toC C') x = eval C x
def StClauseCirc : Prop := ∃ (a₀ : ℕ) (g : MCode → ℕ) (B : MCode × List Unit × ℕ → List GateD × List ℕ), PolyT B ∧
  ∀ (e : MCode) (L P : ℕ), Fits e L P →
    WF (nb e L) (B (e, List.replicate L (), P)).1 ∧ (B (e, List.replicate L (), P)).1.length ≤ a₀ * (L + 1) + g e ∧
    (B (e, List.replicate L (), P)).2.length = 3 * (L + 1) ∧ (∀ w ∈ (B (e, List.replicate L (), P)).2, w < nb e L + (B (e, List.replicate L (), P)).1.length) ∧
    ∀ j < 2 ^ nb e L, ∀ i < 3,
      (ofWord ((((B (e, List.replicate L (), P)).2.drop (i * (L + 1))).take L).map fun w => (wires (toWord (nb e L) j) (toC (B (e, List.replicate L (), P)).1)).getD w false),
        (wires (toWord (nb e L) j) (toC (B (e, List.replicate L (), P)).1)).getD ((B (e, List.replicate L (), P)).2.getD (i * (L + 1) + L) 0) false)
      = (clauseAt e L P j).getD i (0, false)
def Shaped3 (Nv : ℕ) (ψ : Cnf) : Prop := (∀ D ∈ ψ, D.length ≤ 3 ∧ ∀ l ∈ D, l.1 < Nv) ∧ ψ.Nodup
def StForm : Prop := ∃ (a₀ : ℕ) (g : MCode → ℕ) (F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf), PolyT F ∧
  ∀ (e : MCode) (L P : ℕ) (C : List GateD), Fits e L P → WF L C →
    Shaped3 (F ((e, List.replicate L (), P), C)).1.length (F ((e, List.replicate L (), P), C)).2 ∧
    (F ((e, List.replicate L (), P), C)).1.length ≤ 3 * C.length + a₀ * (L + 1) + g e ∧
    (Sat (F ((e, List.replicate L (), P), C)).2 ↔ ¬∀ D ∈ tabF e L P, ∃ l ∈ D, eval (toC C) (toWord L l.1) = l.2)
def StCertSched : Prop :=
  PolyT (fun u : List Unit => codeOf (nu u.length)) ∧ PolyT (fun u : List Unit => next u.length) ∧ PolyT (fun u : List Unit => nu u.length) ∧
  PolyT (fun u : List Unit => decide (pos u.length < top (nu u.length))) ∧ PolyT (fun u : List Unit => decide (pos u.length = top (nu u.length))) ∧
  PolyT (fun p : MCode × List Unit × ℕ => decide (Fits p.1 p.2.1.length p.2.2))
def StCertTabF : Prop := ∃ G : (MCode × List Unit × ℕ) × List Unit → Cnf, PolyT G ∧
  ∀ (e : MCode) (L P : ℕ) (pad : List Unit), Fits e L P → 2 ^ nb e L ≤ pad.length → G ((e, List.replicate L (), P), pad) = tabF e L P
def StFlip : Prop := ∃ fb : List Unit → Bool, PolyT fb ∧ ∀ m : ℕ, pos m = top (nu m) →
  (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)))
def StRestart : Prop := ∀ L : Lang, InENP' L → InENP L
end CircuitLowerBound


