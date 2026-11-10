-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Indexed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:14:37.696255+00:00
-- url     : https://prove2.me/theorems/0552072e-fc88-4f84-8198-25cb5730d313
-- title:
--   Indexed
-- statement:
--   Definitions and structural lemmas for Indexed, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Indexed.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes1

set_option autoImplicit false
namespace QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
noncomputable def nextCocycle (S : OddScale) (n : Nat) (C : ConstructionState) :
    Cocycle C.presentation →ₗ[Field] Cocycle (nextState S n C).presentation where
  toFun v := ⟨nextMap1 S n C v.1, by
    apply (BDL26RZCohomology.mem_cocycle_iff _ _).mpr
    have hc := LinearMap.congr_fun (nextMap_commutes1 S n C) v.1
    change tannerCoboundary1 (nextState S n C).presentation (nextMap1 S n C v.1) =
      nextMap2 S n C (tannerCoboundary1 C.presentation v.1) at hc
    rw [(BDL26RZCohomology.mem_cocycle_iff _ _).mp v.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((nextMap1 S n C).map_add _ _)
  map_smul' _ _ := Subtype.ext ((nextMap1 S n C).map_smul _ _)
noncomputable def nextEquiv (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : n % 2 = 0) :
    H1 C.presentation ≃ₗ[Field] H1 (nextState S n C).presentation := by
  exact Eq.mpr (congrArg (fun T : ConstructionState =>
    H1 C.presentation ≃ₗ[Field] H1 T.presentation)
    (show nextState S n C = rxState S C from if_pos h))
    (equiv C.presentation C.admissible C.regular S)
theorem even_lower (k : Nat) : (2 * k) % 2 = 0 := by omega
noncomputable def evenEquiv (S : OddScale) (k : Nat) :
    H1 (state S (2 * k)).presentation ≃ₗ[Field]
      H1 (state S (2 * k + 1)).presentation :=
  nextEquiv S (2 * k) (state S (2 * k)) (even_lower k)
noncomputable def evenCocycle (S : OddScale) (k : Nat) :
    Cocycle (state S (2 * k)).presentation →ₗ[Field]
      Cocycle (state S (2 * k + 1)).presentation :=
  nextCocycle S (2 * k) (state S (2 * k))
open BDL26IndexedDecoder MultiscaleDecoder
noncomputable def indexedEquiv (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    ((indexedFamily S depth).complex i.castSucc).middleCohomology ≃ₗ[Field]
      ((indexedFamily S depth).complex i.succ).middleCohomology :=
  nextEquiv S i.val (state S i.val) h
noncomputable def indexedCocycle (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    ((indexedFamily S depth).complex i.castSucc).middleCocycleCode.carrier →ₗ[Field]
      ((indexedFamily S depth).complex i.succ).middleCocycleCode.carrier :=
  nextCocycle S i.val (state S i.val)
end QEC.Coding.BDL26RXCohomology


