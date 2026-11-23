-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:42.335797+00:00
-- url     : https://prove2.me/theorems/1d21b872-0179-4a3e-a134-6ae868fe030d
-- title:
--   Iwahori Proj Surjective
-- statement:
--   Definitions and structural lemmas for Iwahori Proj Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
namespace GlobalTheory.SmGL.IwahoriOnto
section Abstract
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
end Abstract
section Factor
variable {R n : Type} [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n] [LinearOrder n]
end Factor
section Local
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
def lowerInt : Set (GL n k) :=
  {c | (∀ i j, valuation k ((c : Matrix n n k) i j) ≤ 1) ∧ (∀ i j, i < j → (c : Matrix n n k) i j = 0) ∧
    ∀ i, (c : Matrix n n k) i i = 1}
end Local
end GlobalTheory.SmGL.IwahoriOnto


