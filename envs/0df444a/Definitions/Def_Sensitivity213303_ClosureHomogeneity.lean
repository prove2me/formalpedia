-- Prove2me | Definitions.Def_Sensitivity213303_ClosureHomogeneity
-- name    : Sensitivity213303_ClosureHomogeneity
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:56:54.346771+00:00
-- url     : https://prove2.me/theorems/b9f4d85a-eafe-4366-8536-ed40aaa8dcc4
-- title:
--   Uniform scaling of a finite sensitivity profile
-- statement:
--   For a natural number c and a profile v, scale(c,v) multiplies each A, B, M, P and D coordinate by c. This pointwise operation is the numerical scaling used when one complete period of the recursive construction is repeated. The associated semantic and arithmetic lemmas show that profile bounds and closure operations respect this scaling.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ClosureHomogeneity; source SHA256 435b0dc3e32b040d7866d760d5f5bde2dcece93d93d7793713473114a15991a5.

import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange



set_option autoImplicit false

namespace ThreeBoundFullProfile
variable {n : ℕ}

def scale (c : ℕ) (v : Profile n) : Profile n := fun i => c * v i











end ThreeBoundFullProfile


