-- Prove2me | Definitions.Def_AME125_Control
-- name    : AME125_Control
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:12:04.045115+00:00
-- url     : https://prove2.me/theorems/41778fec-7a70-504b-a669-f0da3d978371
-- title:
--   Control
-- statement:
--   Definitions and structural lemmas for Control, from Zayn Blore (zblore/fc-ame-12-5; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned Existence of a twelve-party absolutely maximally entangled state in local dimension five (AME(12,5)) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Control.lean

module
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace AME125
open OpenQuantumProblem35
open scoped Matrix
def controlU : Matrix (Fin 12) (Fin 12) (ZMod 5) :=
  fun i j ↦ if i.1 = 0 ∧ 6 ≤ j.1 then 0 else U i j
noncomputable def controlState : StateVector 12 5 := graphState controlU
def e0 : Config 6 5 := fun i ↦ if i.1 = 0 then 1 else 0
end AME125


