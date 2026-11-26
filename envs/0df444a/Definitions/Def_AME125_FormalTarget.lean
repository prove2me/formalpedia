-- Prove2me | Definitions.Def_AME125_FormalTarget
-- name    : AME125_FormalTarget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:12:02.337627+00:00
-- url     : https://prove2.me/theorems/3dd9ce9e-a669-5564-9422-dce1add52795
-- title:
--   Formal Target
-- statement:
--   Definitions and structural lemmas for Formal Target, from Zayn Blore (zblore/fc-ame-12-5; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned Existence of a twelve-party absolutely maximally entangled state in local dimension five (AME(12,5)) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/FormalTarget.lean

module
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace AME125
open OpenQuantumProblem35
noncomputable def ame125State : StateVector 12 5 := graphState U
end AME125
namespace OpenQuantumProblem35
end OpenQuantumProblem35


