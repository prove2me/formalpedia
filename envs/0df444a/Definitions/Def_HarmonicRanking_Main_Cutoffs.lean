-- Prove2me | Definitions.Def_HarmonicRanking_Main_Cutoffs
-- name    : HarmonicRanking_Main_Cutoffs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:23.737173+00:00
-- url     : https://prove2.me/theorems/685fc870-725b-4639-a6cd-34cf54bc6522
-- title:
--   Target-rank sections and infimum-defined cutoffs
-- statement:
--   Fix a realized target pair $uv$, all other ranks $\rho$, and the two varied ranks $x,y\in[0,1)$. Replacing only these target coordinates gives the rank assignment $\rho^{x,y}$. Define the two matching-order cutoffs by
--
--   $$
--   a(x)=\inf\bigl(\{1\}\cup\{y\in[0,1):u\text{ is strictly earlier than }v\text{ at }\rho^{x,y}\}\bigr),
--   $$
--   $$
--   b(y)=\inf\bigl(\{1\}\cup\{x\in[0,1):v\text{ is strictly earlier than }u\text{ at }\rho^{x,y}\}\bigr).
--   $$
--
--   The inserted endpoint makes an empty section have cutoff 1. A full section has cutoff 0. No monotonicity across different sections is imposed, and neither boundary is classified by definition. The section-cutoff and gain-bound theorems use these same constructed functions.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), pp. 10–11, §3.1 and proof of Corollary 3.2

import Definitions.Def_HarmonicRanking_Main_Scan

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

variable {L R : Type*} [Fintype L] [Fintype R]

/-- Replace only the two target coordinates; all other ranks remain fixed. -/
def targetRanks (r : Ranks L R) (u : L) (v : R) (x y : Rank) : Ranks L R := by
  classical
  exact Function.update (Function.update r (Sum.inl u) x) (Sum.inr v) y

/-- Infimum of an upward section, including 1 so the empty section has cutoff 1. -/
def cutoffA (G : Instance L R) (τ : TieRule L R) (r : Ranks L R)
    (u : L) (v : R) (x : Rank) : ℝ :=
  sInf (insert 1 {y : ℝ | ∃ t : Rank, (t : ℝ) = y ∧
    earlier G τ (targetRanks r u v x t) (Sum.inl u) (Sum.inr v)})

def cutoffB (G : Instance L R) (τ : TieRule L R) (r : Ranks L R)
    (u : L) (v : R) (y : Rank) : ℝ :=
  sInf (insert 1 {x : ℝ | ∃ t : Rank, (t : ℝ) = x ∧
    earlier G τ (targetRanks r u v t y) (Sum.inr v) (Sum.inl u)})

end HarmonicRanking.Main


