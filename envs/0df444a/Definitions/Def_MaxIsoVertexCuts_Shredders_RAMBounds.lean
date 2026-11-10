-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_RAMBounds
-- name    : MaxIsoVertexCuts_Shredders_RAMBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:55:23.696463+00:00
-- url     : https://prove2.me/theorems/c6cf5990-0d76-4170-933f-08b9f8072310
-- title:
--   RAMBounds
-- statement:
--   Operational bounds on the published integer RAM: no oracle queries for standalone programs, no coins for deterministic programs, logarithmic register words at every step, and actual halting with instruction cost plus output length bounded by the budget. Success is the uniform fraction of all B-bit strings. Almost-linear budgets are ceil(K(m+2)^(1+ε)). These predicates assert no problem-specific correctness guarantee.
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_GraphData

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

open CongruencyTU

def NoQueries (P : Program) : Prop := ∀ a, Instr.query a ∉ P

def NoRandomness (P : Program) : Prop := ∀ a, Instr.coin a ∉ P

def WordBound (P : Program) (O : Oracle) (coins : ℕ → Bool) (input : List ℤ)
    (n m c : ℕ) : Prop :=
  ∀ t j, Nat.size ((run P O coins input t).reg j).natAbs ≤ c * (1 + Nat.log 2 (2+n+m))

def HaltWithin (P : Program) (O : Oracle) (coins : ℕ → Bool) (input : List ℤ)
    (B : ℕ) : Prop :=
  isHalted P (run P O coins input B) = true ∧
    (run P O coins input B).cost + (outputAfter P O coins input B).length ≤ B

noncomputable def successFraction (P : Program) (input : List ℤ) (B : ℕ)
    (Good : List ℤ → Prop) : ℝ :=
  ((Finset.univ.filter fun coins : Fin B → Bool =>
    Good (outputAfter P noOracle (extendCoins coins) input B)).card : ℝ) / (2 : ℝ)^B

noncomputable def almostLinearBudget (K : ℝ) (eps : ℝ) (m : ℕ) : ℕ :=
  ⌈K * ((m+2 : ℕ) : ℝ) ^ (1+eps)⌉₊

end MaxIsoVertexCuts.Shredders


