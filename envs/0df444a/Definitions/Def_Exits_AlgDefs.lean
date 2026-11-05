-- Prove2me | Definitions.Def_Exits_AlgDefs
-- name    : Exits_AlgDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:19:36.110192+00:00
-- url     : https://prove2.me/theorems/71a3db61-f387-4559-b70b-02604c8425b2
-- title:
--   Alg Defs
-- statement:
--   Definitions and structural lemmas for Alg Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/AlgDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_Suffices_Defs
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_Level_SecPseudocode
import Definitions.Def_ThmEveryDeltaStatement
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Unary_const
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace Exits
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate
def search {C : Type} [HasSize C] (K g : ℕ) (Np : Procs C) : Stepped C (Option ℕ) := firstUntil (nCol K g) (Stepped.ofFun (goodP K g Np)) id
def netAlg (K g : ℕ) (E : CliqueAlgorithm) : NetAlg := ⟨fun Np => Stepped.optBind (search K g Np) (E.app (lamP K g Np) (tableM K g Np)) zeroOf⟩
def CLIQUE : ℕ → CliqueAlgorithm
  | 0 => bruteE (levelK 0)
  | ℓ + 1 => levelAlgP (levelG ℓ) (gridPsi (levelG ℓ) false) (gridPsi (levelG ℓ) true) (netAlg (levelK ℓ) (levelG ℓ) (CLIQUE ℓ))
def NETWORK (ℓ : ℕ) : NetAlg := netAlg (levelK ℓ) (levelG ℓ) (CLIQUE ℓ)
def COUNT (ℓ : ℕ) : StepMachine Formula ℤ := Stepped.ite (fun Φ : Formula => Φ.isEmpty) (Stepped.const 1) ((NETWORK ℓ).app (satProcs (levelG ℓ) 3))
def SAT (ℓ τ : ℕ) : StepMachine (List Bool) Bool := satLoop τ (COUNT ℓ)
def levelUp (K : ℕ) (E : CliqueAlgorithm) : CliqueAlgorithm := levelAlgP (3 * K ^ 8) (gridPsi (3 * K ^ 8) false) (gridPsi (3 * K ^ 8) true) (netAlg K (3 * K ^ 8) E)
def StSearchStops : Prop := ∀ (K g : ℕ) (C : Type) [HasSize C] (Np : Procs C) (c : C) (x : ℕ), (List.range (K ^ g)).find? (fun y => goodP K g Np (c, y)) = some x →
  (search K g Np).Runs c (2 * (x + 1)) (4 * (size c + size (K ^ g)) + 10) (some x)
def StSearchStopsOf : Prop := StFirstUntil → StSearchStops
def StGroupingLemma : Prop := ∀ (K : ℕ) (e : ℝ) (E : CliqueAlgorithm), 2 ≤ K → 0 ≤ e → E.Within K e → Correct (netAlg K (3 * K ^ 8) E) (3 * K ^ 8) K e (e + 2)
def StGroupingLemmaOf : Prop := StSearchStops → ViaGrouping.StSearch → ViaGrouping.StTable → ViaGrouping.StValue → StGroupingLemma
def StKeeps : Prop := ∀ (K g : ℕ) (E : CliqueAlgorithm), E.PolyTimeSteps → AlgKeeps (netAlg K g E)
def StKeepsOf : Prop := StFoldUntilPoly → StKeeps
def StLevelUp : Prop := ∀ (K : ℕ) (e : ℝ) (E : CliqueAlgorithm), 2 ≤ K → 0 ≤ e → E.PolyTimeSteps → E.Within K e →
  (levelUp K E).PolyTimeSteps ∧ (levelUp K E).Within (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)
def StLevelUpOf : Prop := StGroupingLemma → StKeeps → StLevelUp
def StClique : Prop := ∀ ℓ : ℕ, (CLIQUE ℓ).PolyTimeSteps ∧ (CLIQUE ℓ).Within (levelK ℓ) (Level.levelE ℓ)
def StCliqueOf : Prop := StLevelUp → StClique
def StCountNil : Prop := ∀ ℓ : ℕ, ∃ S : ℕ, (COUNT ℓ).Runs [] 1 S 1
def StCountCost : Prop := ∀ (δ' : ℝ) (ℓ : ℕ), 0 < δ' → δ' ≤ 1 → 72 / δ' ≤ levelK ℓ → Level.levelE ℓ ≤ δ' / 12 →
  PolyTimeSteps (COUNT ℓ) ∧ ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (COUNT ℓ).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)
def StCountCostOf : Prop := StGroupingLemma → StKeeps → StClique → StCountCost
def StAlgorithm : Prop := ∀ (δ : ℝ) (M τ : ℕ) (hδ' : 0 < δ / (3 * (M : ℝ))), 0 < δ → δ ≤ 1 → 1 ≤ M → Enumerates (δ / 3) M τ →
  PolyTimeSteps (SAT (Level.firstLevel hδ') τ) ∧ Paper.DecidesInSteps (SAT (Level.firstLevel hδ') τ) δ
def StAlgorithmOf : Prop := StSuffices → StCountCost → StAlgorithm
def StDecides : Prop := ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (SAT ℓ τ) ∧ Paper.DecidesInSteps (SAT ℓ τ) δ
def StDecidesOf : Prop := StAlgorithm → StEnumeration → StDecides
def StProofNamed : Prop := ∀ (δ : ℝ) (M τ K : ℕ) (E : CliqueAlgorithm), 0 < δ → δ ≤ 1 → 1 ≤ M → Enumerates (δ / 3) M τ → 72 / (δ / (3 * (M : ℝ))) ≤ K → E.PolyTimeSteps → E.Within K (δ / (3 * (M : ℝ)) / 12) →
  PolyTimeSteps (satLoop τ ((netAlg K (3 * K ^ 8) E).app (satProcs (3 * K ^ 8) 3))) ∧ Paper.DecidesInSteps (satLoop τ ((netAlg K (3 * K ^ 8) E).app (satProcs (3 * K ^ 8) 3))) δ
def StProofNamedOf : Prop := StSuffices → StGroupingLemma → StKeeps → StProofNamed
def StLevelAchievable : Prop := ∀ (K : ℕ) (e : ℝ), 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)
def StLevelAchievableOf : Prop := StLevelUp → StLevelAchievable
def StEStarOf : Prop := StLevelAchievable → eStar = 0
def StThroughEStarOf : Prop := eStar = 0 → StEnumeration → StProofNamed → Sat3.ThmEveryDelta
def StByAlgorithmOf : Prop := StDecides → Sat3.ThmEveryDelta
end Exits


