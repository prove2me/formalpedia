-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:26.986629+00:00
-- url     : https://prove2.me/theorems/9587580b-2e04-41fb-9195-160f4bfee931
-- title:
--   PSerre Poly Laurent Cohom
-- statement:
--   Definitions and structural lemmas for PSerre Poly Laurent Cohom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurentCohom.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u
namespace LaurentCohomProof
variable {S : Type u} [CommRing S] {N : ℕ}
def negSet (a : Fin (N + 1) → ℤ) : Finset (Fin (N + 1)) := Finset.univ.filter fun j => a j < 0
variable (S) in

def part (J : Finset (Fin (N + 1))) : Laurent S N →ₗ[S] Laurent S N where
  toFun f := f.filter fun a => negSet a = J
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul
variable (S N) in

def wPart (c : ℤ) (J : Finset (Fin (N + 1))) : Submodule S (Laurent S N) :=
  Finsupp.supported S S {a | negSet a = J ∧ ∑ j, a j = c}
variable (S N) in

abbrev G : StdCell N → Type u := fun _ => Laurent S N
variable (S N) in

abbrev ρ := Cech.idRes S (Laurent S N) (Finset.univ : Finset (Fin (N + 1)))
variable (S) in

def partC (J : Finset (Fin (N + 1))) (i : ℕ) : Cech.Cochain (G S N) i →ₗ[S] Cech.Cochain (G S N) i :=
  Cech.mapC (fun _ => part S J) i
def bnd (c : ℤ) : Set (Fin (N + 1) → ℤ) :=
  {a | ∑ j, a j = c ∧ (negSet a = ∅ ∨ negSet a = Finset.univ)}
end LaurentCohomProof
end
end GroundTheory.Heights₂.Heights.Kleiman


