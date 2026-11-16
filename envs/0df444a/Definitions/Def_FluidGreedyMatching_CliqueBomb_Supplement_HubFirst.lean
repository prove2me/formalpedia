-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_Supplement_HubFirst
-- name    : FluidGreedyMatching_CliqueBomb_Supplement_HubFirst
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:12:51.406708+00:00
-- url     : https://prove2.me/theorems/9a93514d-a302-4c43-90b6-7d81236bedab
-- title:
--   The fixed hub-first Double-Bomb preference profile
-- statement:
--   On the published bipartite Double-Bomb $S_n(\sigma)$, $X,Y$ are the hub classes, $X',Y'$ their paired antennas, and $P,Q$ the satellite classes, with $\lfloor\sigma n\rfloor$ paired satellites. The actor-dependent preferences, from most to least preferred among neighbors, are
--   $$
--   X:Y\succ P\succ X',\quad Y:X\succ Q\succ Y',\quad
--   P:X\succ Q,\quad Q:Y\succ P.
--   $$
--   Ties within each class are broken by the original index, lower index first. Antennas have one neighbor. Non-neighbors are placed after the listed neighbor classes, in a fixed total order; their positions cannot affect a choice. The profile is deterministic and is held fixed throughout the run.
--
--   The sequence $r_{\rm RDO}(S_{j+1}(\sigma),\pi)$ uses every positive integer size and the new RDO expectation, rather than the published MRG-only expectation. This is the preference profile and sequence in Theorem 1.2. The only helper lemma proves that the class/index label is injective.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), §4.2, pp. 14–15; §4.3, pp. 15–17

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_DoubleBomb
import Definitions.Def_FluidGreedyMatching_CliqueBomb_Supplement_RDOModel

set_option autoImplicit false

namespace FluidGreedyMatching.CliqueBomb.Supplement

noncomputable section

/-- Tags 0=X, 1=Y, 2=X', 3=Y', 4=P, 5=Q, with the original index. -/
def bombCode {n m : ℕ} : BombVertex n m → ℕ × ℕ
  | .inl (c, i) => (c.val, i.val)
  | .inr (c, i) => (4 + c.val, i.val)

/-- Structural injectivity of class and index. -/
theorem bombCode_injective {n m : ℕ} : Function.Injective (@bombCode n m) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => simpa [bombCode, Prod.ext_iff, Fin.ext_iff] using h
    | inr w => have hc := congrArg Prod.fst h; simp [bombCode] at hc; omega
  | inr v =>
    cases w with
    | inl w => have hc := congrArg Prod.fst h; simp [bombCode] at hc; omega
    | inr w => simpa [bombCode, Prod.ext_iff, Fin.ext_iff] using h

/-- §4.2, pp. 14–15: Y > P > X' for X, X > Q > Y' for Y,
X > Q for P, and Y > P for Q. Non-neighbors follow these tiers.
Antennas have only one neighbor. Smaller tier/index is preferred. -/
def hubTier (actor candidate : ℕ) : ℕ :=
  if actor = 0 then
    if candidate = 1 then 0 else if candidate = 4 then 1 else if candidate = 2 then 2 else 3
  else if actor = 1 then
    if candidate = 0 then 0 else if candidate = 5 then 1 else if candidate = 3 then 2 else 3
  else if actor = 4 then
    if candidate = 0 then 0 else if candidate = 5 then 1 else 2
  else if actor = 5 then
    if candidate = 1 then 0 else if candidate = 4 then 1 else 2
  else candidate

@[instance_reducible] def hubFirstProfile {n m : ℕ} (v : BombVertex n m) : LinearOrder (BombVertex n m) :=
  orderByTier bombCode bombCode_injective (hubTier (bombCode v).1)

/-- Size j means n=j+1, covering every positive size. -/
def rdoBombRatio (σ : ℝ) (j : ℕ) : ℝ :=
  rdoExpectedRatio (doubleBomb σ false (j + 1)) hubFirstProfile

end
end FluidGreedyMatching.CliqueBomb.Supplement


