-- Prove2me | Definitions.Def_Eight_Level_Defs
-- name    : Eight_Level_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:45:39.383683+00:00
-- url     : https://prove2.me/theorems/f4b8d669-3feb-40c8-be95-4591032d88b1
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecPseudocode_Algorithm
import Definitions.Def_ClauseBound_Alg_Grid
set_option autoImplicit false
section
section
namespace Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped
def numPat8 {C : Type} (g : ℕ) (lam : C → ℕ) (c : C) : ℕ := (tOf (lam c) + 1) ^ nRect g
noncomputable def netOfι (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : Network (Fin (nParts g g tr)) (List Bool) (List Bool) :=
  gridN eightF [] g g tr 0 lam y Rm
def levelNet (g : ℕ) (tr : Bool) : NetFormer := fun lam R =>
  { n := fun c _ => nMemb g g tr * (g * g) * lam c.1
    cap := fun c a b => capG eightF g g tr 0 (lam c.1) c.2 a b
    W := sideWP g tr lam R
    f := ofFun fun x => gridFf eightF [] g g tr 0 (lam x.1.1) x.1.2 x.2 }
def useRowP {C : Type} (g : ℕ) (lam : C → ℕ) (x : C × ℕ) : Bool :=
  decide (totalG eightF g g false 0 (lam x.1) x.2 ≤ totalG eightF g g true 0 (lam x.1) x.2)
def levelAlg (g : ℕ) (NE : NetEvaluator) : Evaluator :=
  ⟨fun lam R => bind (sumRange (numPat8 g lam) (Stepped.ite (useRowP g lam) (NE.app (levelNet g false lam R)) (NE.app (levelNet g true lam R))))
    (ofFun fun p => p.2 / ((2 ^ (tOf (lam p.1) * nRect g) : ℕ) : ℤ))⟩
def StPieces : Prop := ∀ lam : ℕ, 1 ≤ lam →
  (∀ x y u v : Bits lam, ∑ i ∈ Finset.range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v) ∧
    CutsOK eightF [] 0 lam fun i => A lam i
def StPresents : Prop := ∀ (g : ℕ) (tr : Bool), ∃ a : ℕ, ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
  (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
  (levelNet g tr lam R).Presents (c, y) (netOfι g tr (lam c) y Rm) (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a)
def StNetKeeps : Prop := ∀ (g : ℕ) (tr : Bool), NetFormer.Keeps (levelNet g tr)
def StMin : Prop := ∀ g lam y : ℕ, 1 ≤ lam →
  ((min (totalG eightF g g false 0 lam y) (totalG eightF g g true 0 lam y) : ℕ) : ℝ) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4
def StLevel : Prop := ∀ (K g : ℕ) (e : ℝ) (NE : NetEvaluator), 2 ≤ K → K ≤ g → 0 ≤ e → NE.Correct g K e (e + 2) →
  (levelAlg g NE).Correct (g * g) ((rho + 2 / K) * e + 2 / K)
def StLevelKeeps : Prop := ∀ (g : ℕ) (NE : NetEvaluator), NE.Keeps → (levelAlg g NE).Keeps
noncomputable def levelE : ℕ → ℝ
  | 0 => 1 / 2
  | ℓ + 1 => (rho + 2 / Paper.levelK ℓ) * levelE ℓ + 2 / Paper.levelK ℓ
open Paper
end Eight.Level


