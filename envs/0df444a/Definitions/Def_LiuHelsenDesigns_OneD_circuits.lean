-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_circuits
-- name    : LiuHelsenDesigns_OneD_circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:05:53.324349+00:00
-- url     : https://prove2.me/theorems/f79621d3-1b1b-416c-aaa9-84fc2ccc7c9f
-- title:
--   Computational-basis elementary circuits
-- statement:
--   The physical register has exactly $n$ binary wires in a fixed open-line order. Gate tags denote the actual H, S, X, Z, CNOT, T, T†, S†, Toffoli and SWAP matrices, with identity outside their listed supports. Legal layers have disjoint supports and nearest-neighbor two-wire gates. The headline alphabet excludes Toffoli and SWAP as free primitives.
--
--   $$D(C)=\#\{\text{layers of }C\},\qquad T(C)=\#T+\#T^\dagger.$$
--
--   These are operational resources of the evaluated circuit. Toffoli appears only in the permutation-generator interface; elementary implementations are required wherever Clifford+T resources are claimed.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), pp.3–7, §1.1, Figs.1–3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Mathlib

namespace LiuHelsenDesigns.OneD

/-- Computational basis on exactly n physical qubits. -/
abbrev Basis (n : ℕ) := Fin n → Bool
abbrev Mat (n : ℕ) := Matrix (Basis n) (Basis n) ℂ

/-- Gate tags: H,S,X,Z,CNOT,T,T†,S†,Toffoli,SWAP. -/
def arity (t : ℕ) : ℕ := if t = 4 ∨ t = 9 then 2 else if t = 8 then 3 else 1
abbrev Operation := ℕ × List ℕ
abbrev Circuit := List (List Operation)

def boolNat (b : Bool) : ℕ := if b then 1 else 0

noncomputable def gateEntry (t : ℕ) (x y : ℕ → Bool) : ℂ :=
  if t = 0 then (-1 : ℂ) ^ (boolNat (x 0) * boolNat (y 0)) / Real.sqrt 2
  else if t = 1 then if x 0 = y 0 then (if y 0 then Complex.I else 1) else 0
  else if t = 2 then if x 0 = !y 0 then 1 else 0
  else if t = 3 then if x 0 = y 0 then (if y 0 then -1 else 1) else 0
  else if t = 4 then if x 0 = y 0 ∧ x 1 = Bool.xor (y 1) (y 0) then 1 else 0
  else if t = 5 then if x 0 = y 0 then
    (if y 0 then Complex.exp (Complex.I * (Real.pi / 4)) else 1) else 0
  else if t = 6 then if x 0 = y 0 then
    (if y 0 then Complex.exp (-Complex.I * (Real.pi / 4)) else 1) else 0
  else if t = 7 then if x 0 = y 0 then (if y 0 then -Complex.I else 1) else 0
  else if t = 8 then if x 0 = y 0 ∧ x 1 = y 1 ∧
    x 2 = Bool.xor (y 2) (y 0 && y 1) then 1 else 0
  else if t = 9 then if x 0 = y 1 ∧ x 1 = y 0 then 1 else 0
  else 0

def readWire {n : ℕ} (x : Basis n) (i : ℕ) : Bool :=
  if h : i < n then x ⟨i,h⟩ else false

noncomputable def operationMatrix (n : ℕ) (o : Operation) : Mat n :=
  fun x y => if ∀ i : Fin n, i.val ∉ o.2 → x i = y i then
    gateEntry o.1
      (fun j => readWire x (o.2[j]?.getD n))
      (fun j => readWire y (o.2[j]?.getD n)) else 0

noncomputable def circuitMatrix (n : ℕ) (C : Circuit) : Mat n :=
  C.foldl (fun U layer => layer.foldl (fun V o => operationMatrix n o * V) 1 * U) 1

def gateLegal (n : ℕ) (o : Operation) : Prop :=
  o.1 ≤ 9 ∧ o.2.length = arity o.1 ∧ o.2.Nodup ∧
    (∀ i ∈ o.2, i < n) ∧
    (∀ i ∈ o.2, ∀ j ∈ o.2, i ≤ j + 2 ∧ j ≤ i + 2) ∧
    (arity o.1 = 2 → ∃ a, o.2 = [a,a+1] ∨ o.2 = [a+1,a])

/-- All gates in a layer have disjoint supports; the line has no wraparound. -/
def LegalCircuit (n : ℕ) (C : Circuit) : Prop :=
  ∀ layer ∈ C, (layer.flatMap Prod.snd).Nodup ∧ ∀ o ∈ layer, gateLegal n o

/-- The headline uses elementary Clifford+T gates only: no free Toffoli or SWAP. -/
def ElementaryCircuit (C : Circuit) : Prop := ∀ layer ∈ C, ∀ o ∈ layer, o.1 ≤ 7
def CliffordCircuit (C : Circuit) : Prop :=
  ∀ layer ∈ C, ∀ o ∈ layer, o.1 ≤ 4 ∨ o.1 = 7
def depth (C : Circuit) : ℕ := C.length
def tCount (C : Circuit) : ℕ :=
  (C.flatMap id).countP (fun o => o.1 == 5 || o.1 == 6)

end LiuHelsenDesigns.OneD


