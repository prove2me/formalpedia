-- Prove2me | Definitions.Def_GeneralPieces_Tied_Defs
-- name    : GeneralPieces_Tied_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:49:09.96225+00:00
-- url     : https://prove2.me/theorems/66a0d21b-b16c-46f0-841c-288c4d776392
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_Pad
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Unary_poly
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace GeneralPieces
def x₀Of (c : ℕ) : ℕ := max 18 (Nat.clog 2 (c + 5))
end GeneralPieces
namespace GeneralPieces.Tied
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen Turing
def runB (P : PiecesF) (x₀ : ℕ) (p : U × U × PInst) : ℤ :=
  solveG P p.1 (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.2.length (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.1 p.2.2
def needB (P : PiecesF) (x₀ l lam B : ℕ) : ℕ := needG P (K x₀ l) lam B 1 1 (sched P x₀ l)
structure PartB (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) : Prop where
  /-- the program is polynomial-time in (pad, ℓ, instance) -/
  poly : PolyT (runB P x₀)
  /-- on a (K_ℓ, λ)-clique it is the recursion on the schedule of display (40), from K_ℓ nodes down
  to K₀ nodes (`sched P x₀ ℓ` is, by definition, the list step ℓ−1, …, step 0) -/
  sched_eq : ∀ (pad lu : U) (l lam B : ℕ) (I : PInst), WFe (K x₀ l) lam B I → runB P x₀ (pad, lu, I) = solveG P pad (K x₀ 0) (sched P x₀ l) I
  /-- the step from K_{ℓ+1} = g_ℓ² nodes to K_ℓ nodes has the numbers of display (40) -/
  step_eq : ∀ l, (step P x₀ l).K = K x₀ l ∧ (step P x₀ l).p = g x₀ l ∧ (step P x₀ l).d = g x₀ l ∧ zetaOf (step P x₀ l) = zeta l
  /-- and meets the hypotheses of case (ii) of Lemma 8 (fields `dvd` and `hoeffding` of `LevelOK2`)
  at every label length -/
  caseII : ∀ l lam, 1 ≤ lam → LevelOK2 P (step P x₀ l) lam
  /-- the program returns the value of the clique if the pad has 2^needB units -/
  value : ∀ (pad : U) (l lam B : ℕ) (I : PInst), 1 ≤ lam → 1 ≤ B → WFe (K x₀ l) lam B I → 2 ^ needB P x₀ l lam B ≤ pad.length →
    runB P x₀ (pad, List.replicate l (), I) = zval (K x₀ l) I
  /-- 2^needB ≤ 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ + B))^{C₀K_ℓ²} -/
  rate : ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
    (needB P x₀ l lam B : ℝ) ≤ e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam + C₀ * (K x₀ l : ℝ) ^ 2 * Real.logb 2 (K x₀ l * (lam + B))
structure TopM {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (r : ℕ → ℝ) : Prop where
  /-- both are polynomial-time -/
  poly_A : PolyT (AM S pick)
  poly_e : PolyT (eM S pick)
  /-- the function returns the number of satisfying assignments, in n + 1 bits, if the pad has 2^eM
  units -/
  correct : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ → ∀ pad : U, 2 ^ eM S pick (SatM.enc k φ) ≤ pad.length →
    AM S pick (SatM.enc k φ, pad) = SatK.binary n (SatK.numSat φ)
  /-- the exponent is O(k·m·r(m)), the O not depending on k -/
  rate : ∃ G : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
    (eM S pick (SatM.enc k φ) : ℝ) ≤ G * ((k : ℝ) * φ.length * r φ.length)
  /-- one machine computes, on every input x, the named function at (x, 2^{eM x} units) within
  q·(|x| + 2^{eM x} + 1)^q steps, and it counts within C·2^{C·k·m·r(m)} steps -/
  machine : ∃ (N : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
      (some ((AM S pick (x, pad (eM S pick x))).map N.outputAlphabet.invFun)) (q * (x.length + 2 ^ eM S pick x + 1) ^ q))) ∧
    SatM.CountsTM N (SatM.bound r C)
def PartCm (P : PiecesF) (ρ : ℝ) (x₀ : ℕ) : Prop := TopM (solverOf P) (Pick.pick P x₀) (SatM.rPow (AppRunningTime.alpha' ρ))
end GeneralPieces.Tied


