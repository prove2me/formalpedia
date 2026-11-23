-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_PreferenceGame
-- name    : StrategicRFx_Benefit_Supplement_PreferenceGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:09:58.819979+00:00
-- url     : https://prove2.me/theorems/14221d21-c62b-4ca2-8661-7bc80dfaf64c
-- title:
--   Ordinal games with arbitrary strategy spaces and outcome preferences
-- statement:
--   Let $I$ be a player type, $A_i$ each player's strategy space, and $O$ an outcome type. A game consists of an outcome function $g:\prod_i A_i\to O$ and a strict preference relation $\succ_i$ on outcomes for each player. A best response and a pure Nash equilibrium are defined by
--
--   $$s_i\in BR_i(s_{-i})\ \Longleftrightarrow\ \forall a_i,\ \neg\bigl(g(a_i,s_{-i})\succ_i g(s)\bigr),\qquad s\in NE\ \Longleftrightarrow\ \forall i,\ s_i\in BR_i(s_{-i}).$$
--
--   This general interface separates games from the specific RFx histories. It accommodates the paper's supplier tie preference without a fictitious real-valued perturbation of profits. It imposes no finite strategy set or equilibrium existence condition.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), p. 16, supplier tie preference

import Mathlib

namespace StrategicRFx.Benefit.Supplement

/-- An ordinal game with arbitrary strategy spaces and an explicit strict
preference on outcomes for each player. This separates the general game
interface from the quotation histories implementing this paper's mechanism. -/
structure PreferenceGame (ι : Type*) (A : ι → Type*) (O : Type*) where
  outcome : (∀ i, A i) → O
  prefers : ι → O → O → Prop

def PreferenceGame.IsBestResponse {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : PreferenceGame ι A O) (s : ∀ i, A i) (i : ι) : Prop := by
  classical
  exact ∀ a, ¬ G.prefers i (G.outcome (Function.update s i a)) (G.outcome s)

def PreferenceGame.IsNash {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : PreferenceGame ι A O) (s : ∀ i, A i) : Prop :=
  ∀ i, G.IsBestResponse s i

end StrategicRFx.Benefit.Supplement


