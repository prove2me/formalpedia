-- Prove2me | Definitions.Def_Freiman_lowerSourceCover
-- name    : Freiman_lowerSourceCover
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:47:52.488419+00:00
-- url     : https://prove2.me/theorems/b1252841-8821-47b1-8453-76a6f56f1087
-- title:
--   Freiman lower construction: source auxiliary endpoint formula
-- statement:
--   The source form of the same shortened endpoint algorithm, with the e13 quantity |T_W(beta)-T_W13(alpha)| exactly as printed in lower_core. Its equality to the formal full-width version is a separate theorem.
-- source:
--   Freiman's Hall ray report, parts/lower_core.tex, endpoints and the meaning of a cover; parts/lower_section14.tex.

import Definitions.Def_Freiman_lowerCover

namespace Freiman
noncomputable def lowerSourceAuxWidth (w e : List ℕ+) : ℝ :=
  if e = [1,3] then |prefixEval w lowerBeta - prefixEval (w ++ [1,3]) lowerAlpha|
  else lowerWidth (w ++ e)
noncomputable def lowerSourceEqualWords (p : LowerPair) (upper : Bool) : LowerPair := by
  classical
  let q := lowerNormalize p
  let s₁ := lowerNaturalShort q.1 upper
  let s₂ := lowerNaturalShort q.2 upper
  let e : List ℕ+ := if (q.1.length % 2 = 0) = (!upper) then [3] else [1,3]
  let shorten := !s₁ && !s₂ && decide
    (lowerSourceAuxWidth q.1 e ≤ (7 / 5 : ℝ) * lowerSourceAuxWidth q.2 e)
  let r := (q.1 ++ lowerEndpointSuffix q.1 upper s₁,
            q.2 ++ lowerEndpointSuffix q.2 upper (s₂ || shorten))
  exact if lowerWidth p.2 ≤ lowerWidth p.1 then r else (r.2,r.1)
noncomputable def lowerSourceEndpointWords (p : LowerPair) (upper : Bool) : LowerPair := by
  classical
  exact if p.1.length % 2 = p.2.length % 2 then lowerSourceEqualWords p upper else
    let leftWide := lowerWidth p.2 ≤ lowerWidth p.1
    let w := if leftWide then p.1 else p.2
    let virtualUpper := decide (w.length % 2 = 0)
    if upper = virtualUpper then
      lowerSourceEqualWords (if leftWide then (p.1 ++ [1],p.2) else (p.1,p.2 ++ [1])) upper
    else lowerNaturalWords p upper
noncomputable def lowerSourceEndpoint (p : LowerPair) (upper : Bool) : ℝ :=
  let w := lowerSourceEndpointWords p upper
  4 + prefixEval w.1 lowerTau + prefixEval w.2 lowerTau
noncomputable def lowerSourceCover (p : LowerPair) : Set ℝ :=
  Set.Icc (lowerSourceEndpoint p false) (lowerSourceEndpoint p true)
def lowerSourceGood (p : LowerPair) : Prop :=
  (lowerSourceCover (lowerChild p ([1],[])) ∩ lowerSourceCover (lowerChild p ([2],[]))).Nonempty
end Freiman


