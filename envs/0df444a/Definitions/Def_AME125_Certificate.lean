-- Prove2me | Definitions.Def_AME125_Certificate
-- name    : AME125_Certificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:11:07.692284+00:00
-- url     : https://prove2.me/theorems/a72b9dfa-c08f-4017-b30c-52eeb7a4c2bf
-- title:
--   Certificate
-- statement:
--   Definitions and structural lemmas for Certificate, from Zayn Blore (zblore/fc-ame-12-5; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned Existence of a twelve-party absolutely maximally entangled state in local dimension five (AME(12,5)) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace AME125
open scoped Matrix
def thetaN (i j : ℕ) : ℕ := (thetaRows.getD i []).getD j 0
def theta : Matrix (Fin 12) (Fin 12) (ZMod 5) := fun i j ↦ (thetaN i.1 j.1 : ZMod 5)
def U : Matrix (Fin 12) (Fin 12) (ZMod 5) := fun i j ↦ if i.1 ≤ j.1 then theta i j else 0
def posIn (m k : ℕ) : ℕ := ((List.range k).filter fun i ↦ m.testBit i).length
def posOut (m j : ℕ) : ℕ := ((List.range j).filter fun i ↦ !m.testBit i).length
def certN (m : ℕ) (L : List ℕ) (j k : ℕ) : ℕ := L.getD (6 * posOut m j + posIn m k) 0
def entryN (m : ℕ) (L : List ℕ) (i k : ℕ) : ℕ :=
  ((List.range 12).map fun j ↦ if m.testBit j then 0 else thetaN i j * certN m L j k).sum
def certOK (c : ℕ × List ℕ) : Bool :=
  (List.range 12).all fun i ↦ (List.range 12).all fun k ↦
    !(c.1.testBit i && c.1.testBit k) || entryN c.1 c.2 i k % 5 == if i = k then 1 else 0
def popcount (m : ℕ) : ℕ := ((List.range 12).filter fun i ↦ m.testBit i).length
def maskOf (A : Finset (Fin 12)) : ℕ := ∑ i ∈ A.map Fin.valEmbedding, 2 ^ i
end AME125


