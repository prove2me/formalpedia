-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:26.694826+00:00
-- url     : https://prove2.me/theorems/5ea95a5a-7b61-4b03-a42e-44ed4c75563c
-- title:
--   Char Id
-- statement:
--   Definitions and structural lemmas for Char Id, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.REAL
def CharId_M {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Fin n → V) where
  toFun y := fun a => ∑ b, E a b (y b)
  map_add' y z := by funext a; simp [Finset.sum_add_distrib]
  map_smul' c y := by funext a; simp [Finset.smul_sum]
def twistedAction {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) : Module.End ℂ (Fin n → V) where
  toFun y := fun x => E c d (y x) - if x = d then y c else 0
  map_add' y z := by
    funext x; by_cases h : x = d <;> simp [h] <;> abel
  map_smul' r y := by
    funext x; by_cases h : x = d <;> simp [h, smul_sub]
def CharId_F {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (j : ℕ) : Submodule ℂ (Fin n → V) :=
  sInf {W | (∀ t : Fin n, j ≤ (t : ℕ) → Pi.single t v ∈ W) ∧
    ∀ c d, ∀ y ∈ W, twistedAction E c d y ∈ W}
def CharId_P {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (a b : Fin n) : Module.End ℂ V :=
  ∑ i ∈ range (n + 1),
    (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b
end Formalism.REAL


