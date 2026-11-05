-- Prove2me | Definitions.Def_RecursionWithPieces_Defs
-- name    : RecursionWithPieces_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:38:33.125253+00:00
-- url     : https://prove2.me/theorems/52156c91-d2d0-4ebc-9649-ecc6212629fd
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionWithPieces/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_PlanUsedDefs
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
set_option autoImplicit false
section
section
namespace RecursionWithPieces
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen VariableBound VariableBound.Decide SparsifyThenCount
section
variable (Θ : ℕ → ℕ → ℕ → ℕ) (P₀ : PiecesF) (val : AppRunningTime.ValQ → ℤ) (c : ℕ)
def solverAB : Solver (List Step × U) := solverOf (GeneralPieces.Tied.recOf P₀ val c)
def pickAB : U → U × (List Step × U) := Pick.pick (GeneralPieces.Tied.recOf P₀ val c) (GeneralPieces.x₀Of c)
def prec (u : U) : U := () :: u
def fnAll : List Bool × U → List Bool := ABDG Θ (solverAB P₀ val c) (pickAB P₀ val c) prec
def expAll : List Bool → ℕ := eBD (solverAB P₀ val c) (pickAB P₀ val c) prec
end
structure TiedAt (Θ : ℕ → ℕ → ℕ → ℕ) (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ) : Prop where
  /-- (P₀, A, val) are the pieces of the proof of the theorem on pieces with ρ = 1/√2 in Appendix B,
  with the constant c: the body of `AppRunningTime.ThmHalfPieces` -/
  pieces : GeneralPieces.Tied.IsPiecesB c P₀ A val
  /-- part (b) of the theorem on the general recursion for the named program, with some constant C₀:
  the recursion on the schedule of display (40) for x₀ = `x₀Of c`; every step has the numbers of
  that display and meets the hypotheses of case (ii)
  of the lemma on groupings with explicit cost; the program is polynomial-time, returns the value of
  the clique if the pad has 2^needB units, and needB obeys the bound of part (b) -/
  partB : ∃ C₀ : ℕ, GeneralPieces.Tied.PartB (GeneralPieces.Tied.recOf P₀ val c) (1 / Real.sqrt 2) (GeneralPieces.x₀Of c) C₀
  /-- part (c), first sentence, for the named programs: the algorithm `AM` for the bound in m with
  its exponent `eM`, on `solverAB` and `pickAB`, at the rate 1/(log₂(m+2))^α' with α' = log₂(1/ρ) =
  log₂ √2; `AM` on these two is the branch of `fnAll` for the bound in m -/
  partCm : GeneralPieces.Tied.PartCm (GeneralPieces.Tied.recOf P₀ val c) (1 / Real.sqrt 2) (GeneralPieces.x₀Of c)
  /-- the pair (`fnAll`, `expAll`) is an algorithm for the two rates in the sense of
  `VariableBound.Decide.Alg`: both functions are polynomial-time; on the code of (k, φ), k ≥ 1, φ a
  k-CNF, with a pad of at least 2^(`expAll`) units, `fnAll` is the number of
  satisfying assignments in n + 1 bits; for every q the number q·(|x| + 2^(`expAll` x) + 1)^q, which
  bounds the steps of the padding machine, is within the bound in n if n ≥ 1, and within the bound
  in m if all variables occur and m ≥ 1, with
  constants that do not depend on k -/
  alg : Alg (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) (fnAll Θ P₀ val c) (expAll P₀ val c)
  /-- one machine puts out, on every bit string x, the value of `fnAll` on x with a pad of
  2^(`expAll` x) units, within C·(|x| + 2^(`expAll` x) + 1)^C steps, and counts within the three
  bounds, each under its conditions (`VariableBound.TiedOut`) -/
  counts : TiedOut (fnAll Θ P₀ val c) (expAll P₀ val c) id (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2))
  /-- a second machine does the same for «some bit is 1», that is, whether the count is not 0 -/
  decides : TiedOut (fnAll Θ P₀ val c) (expAll P₀ val c) bitOf (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2))
  /-- for every width k ≥ 1 and all large n, the plan exists on the code of (k, φ), for every k-CNF
  φ on n variables; where the plan exists the branch `SparsifyThenCount.ADG Θ` for the bound in n is
  `SparsifyThenCount.numDG Θ`, the walk through the counting tree with every leaf counted by
  `VariableBound.countD`, not exhaustive counting -/
  planUsed : PlanUsed (solverAB P₀ val c) (pickAB P₀ val c) prec
def TiedEvery (Θ : ℕ → ℕ → ℕ → ℕ) : Prop := ∀ (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), GeneralPieces.Tied.IsPiecesB c P₀ A val → TiedAt Θ c P₀ A val
def TiedAll (Θ : ℕ → ℕ → ℕ → ℕ) : Prop := ∃ (c : ℕ) (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), TiedAt Θ c P₀ A val
def TiedAllCal : Prop := TiedAll StepSparsify.thCal
end RecursionWithPieces


