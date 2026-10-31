-- Prove2me | Definitions.Def_DynStochMatching_Reward_PureJump
-- name    : DynStochMatching_Reward_PureJump
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:37:42.783292+00:00
-- url     : https://prove2.me/theorems/ec3e8e6c-da5b-4eff-8189-f143bcc17b8c
-- title:
--   Finite-channel continuous-time jump execution
-- statement:
--   A general pure jump system has a possibly infinite state space, finitely many transition channels at each state, rates, destinations and an initial state. Independent exponential holding times and categorical transition choices generate its path. Zero total rate is absorbing. An explicit fallback applies only to exceptional explosive seed paths; the matching count systems have nonexplosive affine death rates. This general object is independent of the paper-specific count coordinates.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, B.4, printed 46–47 / PDF 47–48

import Definitions.Def_DynStochMatching_Reward_Poisson

open MeasureTheory Filter
open scoped Classical ENNReal

namespace DynStochMatching.Reward

/-- A general finite-channel pure jump process. The state type may be infinite. -/
structure JumpSystem (S : Type) (channels : ℕ) where
  rate : S → Fin channels → ℝ
  next : S → Fin channels → S
  initial : S

/-- Jump paths are generated from independent exponential and uniform random seeds. -/
noncomputable def jumpState {S : Type} {c : ℕ} (J : JumpSystem S c)
    (ω : RandomSeeds) : ℕ → S
  | 0 => J.initial
  | k + 1 =>
    let s := jumpState J ω k
    let total := ∑ a, max 0 (J.rate s a)
    match categorical c (fun a => max 0 (J.rate s a) / total) (Real.exp (-ω (k, 1))) with
    | some a => J.next s a
    | none => s

noncomputable def jumpEpoch {S : Type} {c : ℕ} (J : JumpSystem S c)
    (ω : RandomSeeds) : ℕ → ℝ≥0∞
  | 0 => 0
  | k + 1 =>
    let total := ∑ a, max 0 (J.rate (jumpState J ω k) a)
    jumpEpoch J ω k + if total = 0 then ⊤ else ENNReal.ofReal (ω (k, 0) / total)

/-- State at t. An explicit initial-state fallback handles exceptional explosive seed paths. -/
noncomputable def jumpAt {S : Type} {c : ℕ} (J : JumpSystem S c)
    (ω : RandomSeeds) (t : ℝ) : S :=
  if h : ∃ k, ENNReal.ofReal t < jumpEpoch J ω (k + 1) then
    jumpState J ω (Nat.find h) else J.initial

end DynStochMatching.Reward


