-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22Seeds
-- name    : Sensitivity213981Formal_Endpoint22Seeds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:06:11.82837+00:00
-- url     : https://prove2.me/theorems/4b7ce8cf-9c03-4df5-af89-f73ab8afcdda
-- title:
--   Endpoint22 Seeds — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Seeds in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Seeds.prefactor`, `ThreeBoundEndpoint22Seeds.coordinates`, `ThreeBoundEndpoint22Seeds.finiteFamily`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22Seeds.lean, lines 1–92.

import Definitions.Def_Sensitivity213981Formal_ClosureHomogeneity
import Definitions.Def_Sensitivity213981Formal_Endpoint22Recipes
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Actual third-endpoint finite Boolean functions and their growing disjoint
block witnesses.  The periodic upper profile is the final transfer invariant. -/


set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint22Seeds
open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundFullProfile
open Sensitivity5591Endpoint22

noncomputable def coordinates (n : ℕ) :
    IterProd (Fin 5591 × Bool) n ≃ Fin (11182^n) :=
  (Fintype.equivFin _).trans (finCongr (by
    simpa only [Fintype.card_fin,Nat.reduceMul] using
      (tower_input_dimension (V:=Fin 5591) n)))

noncomputable def finiteFamily (Adj : Fin 5591 → Fin 5591 → Prop)
    (loopless : ∀ w, ¬Adj w w) (label : Fin 5591 → Fin 5591 → Bool)
    (n : ℕ) (l : Fin 22) : (Fin (11182^n) → Bool) → Bool :=
  reindex (coordinates n) (family Adj loopless label n l)

variable (Adj : Fin 5591 → Fin 5591 → Prop) (loopless : ∀ w, ¬Adj w w)
  (label : Fin 5591 → Fin 5591 → Bool)







def prefactor (W : Profile 22) : ℕ := max 2 (max (W (.a 0 0)) (W (.b 0 0)))









end ThreeBoundEndpoint22Seeds





end
end Sensitivity213981Formal


