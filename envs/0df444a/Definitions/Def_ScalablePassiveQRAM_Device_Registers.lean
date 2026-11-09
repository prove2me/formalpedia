-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Registers
-- name    : ScalablePassiveQRAM_Device_Registers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:24.7592+00:00
-- url     : https://prove2.me/theorems/5e694213-b7db-497b-82a2-c5fc616fb6e8
-- title:
--   Physical qubits, unary encodings, and the logical memory query
-- statement:
--   Each mode is a two-level qubit. An address or bus register has two rails; each carrier has three rails; every switch slice has two rails; and each leaf has a memory qubit. Carriers are indexed by every scheduled layer and every possible node at that depth, rather than by a chosen address. The physical Hilbert space contains every bit configuration, including invalid unary patterns.
--
--   $$U|a,b,D\rangle=|a,b\mathbin\oplus D_a,D\rangle.$$
--
--   Single-rail raising, lowering, and number operators act as identity on all other modes. The initial and final endpoint configurations specify all physical qubits. Pinning weights are one except for bit-carrying carrier rails, whose weight is two, and memory rails, whose weight is zero. These are register data and operators, not assumptions that the device works.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §§1.2,3.1, equations (1),(2),(11),(14)–(18), pp.7,13–15. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Schedule
import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace ScalablePassiveQRAM.Device

abbrev Address (n : ℕ) := Fin n → Bool
abbrev Ports (n : ℕ) := Fin (n + 1) × Bool
abbrev Carrier (n : ℕ) := (j : Fin (length n + 1)) × ((Fin (layerDepth n j) → Bool) × Fin 3)
abbrev Switch (n : ℕ) := (d : Fin n) × ((Fin d → Bool) × Fin (visits n d + 1) × Bool)
abbrev Auxiliary (n : ℕ) := Carrier n ⊕ Switch n
abbrev Qubit (n : ℕ) := Ports n ⊕ (Auxiliary n ⊕ Address n)
abbrev Basis (n : ℕ) := Qubit n → Bool
abbrev AuxBasis (n : ℕ) := Auxiliary n → Bool
abbrev PortBasis (n : ℕ) := Ports n → Bool
abbrev Logical (n : ℕ) := Address n × Bool
abbrev Database (n : ℕ) := Address n → Bool

noncomputable instance auxBasisFintype (n : ℕ) : Fintype (AuxBasis n) := by
  classical
  infer_instance
noncomputable instance basisFintype (n : ℕ) : Fintype (Basis n) := by
  classical
  infer_instance
abbrev Op (a : Type) := Matrix a a ℂ
abbrev Vector (a : Type) := a → ℂ

/-- Basis vector; no restriction to unary-valid configurations. -/
def ket {a : Type} [DecidableEq a] (x : a) : Vector a := fun y => if y = x then 1 else 0

def outer {a b : Type} (u : Vector a) (v : Vector b) : Matrix a b ℂ :=
  fun i j => u i * star (v j)

/-- A finite register value lifted to all depths, with zero beyond its domain. -/
def bits (n : ℕ) (x : Address n) (i : ℕ) : Bool := if h : i < n then x ⟨i,h⟩ else false

def portQ (n k : ℕ) (b : Bool) : Qubit n := .inl (⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩, b)

def carrierQ (n j : ℕ) (p : ℕ → Bool) (s : Fin 3) : Qubit n :=
  let jj : Fin (length n + 1) := ⟨j % (length n + 1), Nat.mod_lt _ (by omega)⟩
  .inr (.inl (.inl ⟨jj, (fun i => p i, s)⟩))

/-- The `none` case can only arise at depth n or in the unused n=0 device. -/
def switchQ (n d r : ℕ) (p : ℕ → Bool) (b : Bool) : Option (Qubit n) :=
  if h : d < n then
    some (.inr (.inl (.inr ⟨⟨d,h⟩, (fun i => p i,
      ⟨r % (visits n d + 1), Nat.mod_lt _ (by omega)⟩, b)⟩)))
  else none

def memoryQ (n : ℕ) (x : Address n) : Qubit n := .inr (.inr x)

def isAux {n : ℕ} : Qubit n → Bool
  | .inr (.inl _) => true
  | _ => false

def bitFlavor (b : Bool) : Fin 3 := if b then 2 else 1

def pinningWeight {n : ℕ} : Qubit n → ℝ
  | .inl _ => 1
  | .inr (.inl (.inl ⟨_,_,s⟩)) => if s = 0 then 1 else 2
  | .inr (.inl (.inr _)) => 1
  | .inr (.inr _) => 0

/-- Kronecker lift of a one-qubit matrix to the full physical tensor product. -/
def onQubit {n : ℕ} (q : Qubit n) (A : Op Bool) : Op (Basis n) := by
  classical
  exact fun u v => if (∀ r, r ≠ q → u r = v r) then A (u q) (v q) else 0

def raising {n : ℕ} (q : Qubit n) : Op (Basis n) :=
  onQubit q (outer (ket true) (ket false))

def lowering {n : ℕ} (q : Qubit n) : Op (Basis n) := (raising q).conjTranspose

def number {n : ℕ} (q : Qubit n) : Op (Basis n) :=
  onQubit q (outer (ket true) (ket true))

/-- Unencoded query (1), including the physical memory as a quantum register. -/
def queryUnitary (n : ℕ) : Op (Logical n × Database n) := by
  classical
  exact fun out inp => if out = ((inp.1.1, xor inp.1.2 (inp.2 inp.1.1)), inp.2) then 1 else 0

/-- Empty configuration except for dual-rail ports, classical memory and one root ⋆. -/
def endpoint (n j : ℕ) (x : Address n) (b : Bool) (D : Database n) : Basis n := by
  classical
  exact fun q => match q with
    | .inl (k,c) => c == (if h : k.val < n then x ⟨k.val,h⟩ else b)
    | .inr (.inr a) => D a
    | .inr (.inl _) => q == carrierQ n j (fun _ => false) 0

end ScalablePassiveQRAM.Device


