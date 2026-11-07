-- Prove2me | Definitions.Def_NaturalProofs_GGM
-- name    : NaturalProofs_GGM
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:27:37.334204+00:00
-- url     : https://prove2.me/theorems/a663f12c-0726-4427-8f4a-57f4277df169
-- title:
--   GGM
-- statement:
--   Definitions and structural lemmas for GGM, from zzyzek / NaturalProof-Lean contributors's pinned NaturalProof-Lean development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace NaturalProofs
open MCircuit
abbrev Bits (k : ℕ) := Fin k → Bool
def half {k : ℕ} (b : Bool) (y : Fin (2 * k) → Bool) : Bits k :=
  fun j => y ⟨(if b then k else 0) + j, by have := j.isLt; split <;> omega⟩
def firstBit {k : ℕ} (v : Bits k) : Bool := if h : 0 < k then v ⟨0, h⟩ else false
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
def walk {k : ℕ} (v : Bits k) (bs : List Bool) : Bits k :=
  bs.foldl (fun v b => half b (G k v)) v
def prf (k n : ℕ) (s : Bits k) : BoolFn n := fun x => firstBit (walk G s (List.ofFn x))
def pre {n : ℕ} (i : ℕ) (x : Fin n → Bool) : Fin i → Bool := fun j => (List.ofFn x).getD j false
def hybF {k n : ℕ} (i : ℕ) (L : (Fin i → Bool) → Bits k) : BoolFn n :=
  fun x => firstBit (walk G (L (pre i x)) ((List.ofFn x).drop i))
def expand {k i : ℕ} (M : (Fin i → Bool) → Fin (2 * k) → Bool) : (Fin (i + 1) → Bool) → Bits k :=
  fun q => half (q (Fin.last i)) (M (Fin.init q))
section Circuits
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
noncomputable def genC (k : ℕ) : MCircuit (Fin k) (Fin (2 * k)) :=
  parAll (fun j => ofCircuit (gc k j))
def bitval (x : β → Bool) (s : β ⊕ Bool) : Bool := Sum.elim x id s
def muxC (k : ℕ) (s : β ⊕ Bool) (j : Fin k) : MCircuit (β ⊕ (Fin k ⊕ Fin (2 * k))) Unit :=
  let bw : Wire (β ⊕ (Fin k ⊕ Fin (2 * k))) :=
    match s with
    | .inl b => .input (.inl b)
    | .inr c => .const c
  let hi : Wire (β ⊕ (Fin k ⊕ Fin (2 * k))) := .input (.inr (.inr ⟨k + j, by omega⟩))
  let lo : Wire (β ⊕ (Fin k ⊕ Fin (2 * k))) := .input (.inr (.inr ⟨j, by omega⟩))
  ⟨[.not bw, .and bw hi, .and (.gate 0) lo, .or (.gate 1) (.gate 2)], fun _ => .gate 3⟩
noncomputable def stepC {k : ℕ} (s : β ⊕ Bool) (Cv : MCircuit β (Fin k)) : MCircuit β (Fin k) :=
  ((Cv.extend ((genC gc k).mapIn Sum.inr)).extend (parAll (muxC k s))).mapOut Sum.inr
noncomputable def walkC {k : ℕ} (Cv : MCircuit β (Fin k)) (ss : List (β ⊕ Bool)) :
    MCircuit β (Fin k) :=
  ss.foldl (fun C s => stepC gc s C) Cv
noncomputable def prfC {k : ℕ} (hk : 0 < k) (n : ℕ) (s : Bits k) : Circuit (Fin n) :=
  ((walkC gc (wires (fun j => .const (s j))) ((List.finRange n).map Sum.inl)).mapOut
    (fun _ : Unit => (⟨0, hk⟩ : Fin k))).toCircuit ()
noncomputable def startC {k n : ℕ} (i : ℕ) (e : Fin i → Bool)
    (c : (Fin i → Bool) → Fin (2 * k) → Bool) (x : Fin n → Bool) :
    MCircuit (Fin (2 * k)) (Fin k) :=
  let b := (List.ofFn x).getD i false
  if pre i x = e then
    wires (fun j => .input ⟨(if b then k else 0) + j, by have := j.isLt; split <;> omega⟩)
  else wires (fun j => .const (half b (c (pre i x)) j))
noncomputable def leafC {k n : ℕ} (hk : 0 < k) (i : ℕ) (e : Fin i → Bool)
    (c : (Fin i → Bool) → Fin (2 * k) → Bool) (x : Fin n → Bool) : MCircuit (Fin (2 * k)) Unit :=
  (walkC gc (startC i e c x) (((List.ofFn x).drop (i + 1)).map Sum.inr)).mapOut
    (fun _ => (⟨0, hk⟩ : Fin k))
noncomputable def distC {k n : ℕ} (hk : 0 < k) (i : ℕ) (e : Fin i → Bool)
    (c : (Fin i → Bool) → Fin (2 * k) → Bool) (D : Circuit (Fin n → Bool)) :
    Circuit (Fin (2 * k)) :=
  ((ofCircuit D).comp (parAll (leafC gc hk i e c))).toCircuit ()
end Circuits
end NaturalProofs


