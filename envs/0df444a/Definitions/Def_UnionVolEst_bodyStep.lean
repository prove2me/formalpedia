-- Prove2me | Definitions.Def_UnionVolEst_bodyStep
-- name    : UnionVolEst_bodyStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:47.592113+00:00
-- url     : https://prove2.me/theorems/6e364307-bbbe-424e-bcc2-3e6bfcec0c7b
-- title:
--   One iteration of the for loop of Alpona / Alpona-modified (lines 6–15)
-- statement:
--   Processing body $K_i$ from state $(X,p=2^{-\ell})$ with volume answer $\tilde V_i$:
--   1. (lines 6–7) remove from $X$ every point lying in $K_i$;
--   2. (lines 8–9) draw $N_i\sim\mathrm{Pois}(\tilde V_i\,p)$;
--   3. (lines 10–12) while $|X|+N_i>\mathrm{threshold}$ — for Alpona-modified also only while $p\ge 1/F_0$ — keep each point of $X$ with probability $1/2$, set $N_i\leftarrow\mathrm{Binomial}(N_i,1/2)$ and $p\leftarrow p/2$;
--   4. (lines 13–15) add $N_i$ fresh samples from GenerateSamples on $K_i$ to $X$.
--
--   One ComputeVolume call and $N_i$ GenerateSamples calls are recorded. The step returns no state if the while loop never terminates.
--
--   **Formalization Note** A negative volume answer gives intensity $0$, a case the page does not consider. Non-termination requires some item to survive infinitely many fair coin flips, a null event.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, Algorithm 1, p.15 (PDF p.17); Algorithm 2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_UnionVolEst_poissonQuantile
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_thinRounds

namespace UnionVolEst

open Classical in
/-- One iteration of the for loop of Algorithm 1 / Algorithm 2 (lines 6–15) on body `K_i`
(Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, printed p.15, PDF p.17, and Algorithm 2, printed p.19, PDF p.21), given the volume
answer `v = Ṽᵢ`, the uniform number `u` of the Poisson draw, the sample stream `z` of
GenerateSamples on `K_i` and the coins `c`:

* lines 6–7: remove from `X` every point lying in `K_i`;
* lines 8–9: `Nᵢ = poissonQuantile (Ṽᵢ · p) u` (a draw from `Pois(Ṽᵢ · p)`), `p = 2^{−level}`;
* lines 10–12: halve (`thinRounds`) while `|X| + Nᵢ > threshold` — for Algorithm 2
  (`guard = some F₀`) also only while `p ≥ 1/F₀`; the loop runs for the least number of rounds
  after which the condition fails, and `p` is halved once per round;
* lines 13–15: add the samples `z 0, …, z (Nᵢ − 1)` to `X` (`Nᵢ` sampler calls);
* one ComputeVolume call.

Returns `none` if the while loop never terminates.

**Formalization Note** `guard = none` is Algorithm 1, `guard = some F` is Algorithm 2 with
`1/F₀` replaced by `1/F`. A negative volume answer gives intensity `0` (`Real.toNNReal`), a case
the page does not consider (it has probability at most `δ_v`). Non-termination (`none`) happens
only when some item meets `true` coins forever, a null event under the oracle model; the run's
output is then `0` (see `alponaOutput`), never a value that could look correct. -/
noncomputable def bodyStep {n M : ℕ} (K : Fin M → Set (EuclideanSpace ℝ (Fin n))) (T : ℕ)
    (guard : Option ℝ) (i : Fin M) (v u : ℝ) (z : ℕ → EuclideanSpace ℝ (Fin n))
    (c : ℕ → ℕ → Bool) (s : AlponaState n) : Option (AlponaState n) :=
  let X₁ := s.X.filter (fun x => decide (x ∉ K i))
  let N₀ := poissonQuantile (v * ((2 : ℝ)⁻¹) ^ s.level).toNNReal u
  let stop : ℕ → Prop := fun r =>
    (thinRounds c X₁ N₀ r).1.length + (thinRounds c X₁ N₀ r).2 ≤ T ∨
      (match guard with
       | none => False
       | some F => ((2 : ℝ)⁻¹) ^ (s.level + r) < 1 / F)
  if h : ∃ r, stop r then
    some
      { X := (thinRounds c X₁ N₀ (Nat.find h)).1 ++
          (List.range (thinRounds c X₁ N₀ (Nat.find h)).2).map z
        level := s.level + Nat.find h
        volCalls := s.volCalls + 1
        sampCalls := s.sampCalls + (thinRounds c X₁ N₀ (Nat.find h)).2 }
  else none

end UnionVolEst


