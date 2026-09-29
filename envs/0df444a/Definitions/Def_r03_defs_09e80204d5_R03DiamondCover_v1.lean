-- Prove2me | Definitions.Def_r03_defs_09e80204d5_R03DiamondCover_v1
-- name    : r03_defs_09e80204d5_R03DiamondCover_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:52:48.66113+00:00
-- url     : https://prove2.me/theorems/1c5088b4-daa8-4b79-a351-f1e681b15ede
-- title:
--   R03 candidate definition: r03 defs 09e80204d5 R03DiamondCover v1
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_09e80204d5_R03DiamondCover_v1.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only exact finite relations and arbitrary finite chain induction.
   The relation's interpretation as a physical diamond cover, switching-class
   classification and graph connectivity are separate graph proof candidates. -/
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 100000
namespace R03DiamondCover

abbrev Rel := Fin 3 → Fin 3 → Fin 3 → Fin 3 → Prop

def forbidden (a b c d : Fin 3) : Prop :=
  (a=1 ∧ b=2 ∧ c=2 ∧ d=2) ∨
  (a=2 ∧ b=1 ∧ c=2 ∧ d=2) ∨
  (a=2 ∧ b=2 ∧ c=1 ∧ d=2) ∨
  (a=2 ∧ b=2 ∧ c=2 ∧ d=1)

def Diamond : Rel := fun a b c d => a+b+c+d=1 ∧ ¬forbidden a b c d

def Full (r : Fin 3) : Rel := fun a b c d => a+b+c+d=r

def Compose (R S : Rel) : Rel := fun a b c d =>
  ∃ x y : Fin 3, R a b x y ∧ S (2*x) (2*y) c d

def Chain : Nat → Rel
  | 0 => Diamond
  | n+1 => Compose (Chain n) Diamond

def phase : Nat → Fin 3
  | 0 => 2
  | n+1 => phase n + 1

def Hub (a b c : Fin 3) : Prop :=
  (a=1 ∧ b=0 ∧ c=0) ∨ (a=0 ∧ b=1 ∧ c=0) ∨ (a=0 ∧ b=0 ∧ c=1) ∨
  (a=2 ∧ b=2 ∧ c=0) ∨ (a=2 ∧ b=0 ∧ c=2) ∨ (a=0 ∧ b=2 ∧ c=2)

end R03DiamondCover


