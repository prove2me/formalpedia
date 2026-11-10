-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T04:41:36.141269+00:00
-- url     : https://prove2.me/theorems/aae15331-1993-4580-9eec-4ddf57cf17d8
-- title:
--   Indexed
-- statement:
--   Definitions and structural lemmas for Indexed, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCohomology/Indexed.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Theorems.Thm_QEC_Coding_BDL26AlternatingCochain_nextMap_commutes1

set_option autoImplicit false
namespace QEC.Coding.BDL26RZCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps
open BDL26RZMap1CoordinateBridge
open scoped Classical
universe u
noncomputable def nextCocycle (S : OddScale) (n : Nat) (C : ConstructionState) :
    Cocycle C.presentation →ₗ[Field] Cocycle (nextState S n C).presentation where
  toFun v := ⟨nextMap1 S n C v.1, by
    apply (mem_cocycle_iff _ _).mpr
    have hc := LinearMap.congr_fun (nextMap_commutes1 S n C) v.1
    change tannerCoboundary1 (nextState S n C).presentation (nextMap1 S n C v.1) =
      nextMap2 S n C (tannerCoboundary1 C.presentation v.1) at hc
    rw [(mem_cocycle_iff _ _).mp v.2, map_zero] at hc
    exact hc⟩
  map_add' _ _ := Subtype.ext ((nextMap1 S n C).map_add _ _)
  map_smul' _ _ := Subtype.ext ((nextMap1 S n C).map_smul _ _)
noncomputable def nextEquiv (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) :
    H1 C.presentation ≃ₗ[Field] H1 (nextState S n C).presentation := by
  exact Eq.mpr (congrArg (fun T : ConstructionState =>
    H1 C.presentation ≃ₗ[Field] H1 T.presentation)
    (show nextState S n C = rzState S C from if_neg h))
    (equiv C.presentation C.admissible C.regular S)
noncomputable def nextBackwardCocycle (S : OddScale) (n : Nat) (C : ConstructionState)
    (h : ¬ n % 2 = 0) :
    Cocycle (nextState S n C).presentation →ₗ[Field] Cocycle C.presentation := by
  exact Eq.mpr (congrArg (fun T : ConstructionState =>
    Cocycle T.presentation →ₗ[Field] Cocycle C.presentation)
    (show nextState S n C = rzState S C from if_neg h))
    (backwardCocycle C.presentation C.admissible S)
theorem odd_lower (k : Nat) : ¬ (2 * k + 1) % 2 = 0 := by omega
noncomputable def oddEquiv (S : OddScale) (k : Nat) :
    H1 (state S (2 * k + 1)).presentation ≃ₗ[Field]
      H1 (state S (2 * k + 2)).presentation :=
  nextEquiv S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k)
noncomputable def oddCocycle (S : OddScale) (k : Nat) :
    Cocycle (state S (2 * k + 1)).presentation →ₗ[Field]
      Cocycle (state S (2 * k + 2)).presentation :=
  nextCocycle S (2 * k + 1) (state S (2 * k + 1))
noncomputable def oddBackwardCocycle (S : OddScale) (k : Nat) :
    Cocycle (state S (2 * k + 2)).presentation →ₗ[Field]
      Cocycle (state S (2 * k + 1)).presentation :=
  nextBackwardCocycle S (2 * k + 1) (state S (2 * k + 1)) (odd_lower k)
end QEC.Coding.BDL26RZCohomology


