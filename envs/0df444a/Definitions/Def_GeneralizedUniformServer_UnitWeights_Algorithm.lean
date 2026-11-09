-- Prove2me | Definitions.Def_GeneralizedUniformServer_UnitWeights_Algorithm
-- name    : GeneralizedUniformServer_UnitWeights_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:50.258421+00:00
-- url     : https://prove2.me/theorems/ee9f5572-6003-4acf-b370-a216038f6d9e
-- title:
--   The repair-or-resample algorithm of §3.2
-- statement:
--   The algorithm computes $\mu_t$ from the requests seen so far, starts at $X_0=a$, and, when request $r_t$ arrives:
--
--   1. if $X_{t-1}\in G(r_t)$, it stays: $X_t=X_{t-1}$;
--   2. otherwise, with probability $1/2$ it moves to $R_i(X_{t-1},r_t)$ for a uniformly random $i\in[k]$, and with probability $1/2$ it moves to a configuration drawn from $\mu_t$, independently of everything else.
--
--   In every case $X_t\in G(r_t)$. A resampling move may change all $k$ coordinates and is charged its full Hamming distance.
--
--   This is the algorithm whose analysis proves Theorem 1.1.
--
--   **Formalization Note** The algorithm is a transition kernel in the sense of the online-algorithm interface: the coin is a uniform draw from the booleans, the repair index a uniform draw from `Fin k` (nonempty since $k\ge1$), and the resample a draw from the normalized weights after the prefix $(r_1,\dots,r_t)$. The trajectory law of the algorithm on $\rho$ is the composition of these transitions.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 9, §3.2

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Online
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Weights

noncomputable section

namespace GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

/-- The algorithm of §3.2 (source p. 9), started at `a`, as an online transition rule.
When request `r = r_t` arrives, with earlier requests `hist = (r₁, …, r_{t-1})` and current
configuration `x = X_{t-1}`:
1. if `x ∈ G(r)`, it stays: `X_t = x`;
2. otherwise a fresh fair coin is tossed: on one side it moves to `Rᵢ(x, r)` for `i` uniform
   in `[k]`; on the other it moves to a fresh draw from `μ_t = ϕ_t/Φ_t`, the normalized
   weights after the prefix `(r₁, …, r_t)` computed from the requests seen so far.
All draws are fresh and independent of everything else. -/
def hwangAlg [NeZero k] (a : Config M) : OnlineAlg M := fun hist x r => by
  classical
  exact if Serves x r then PMF.pure x else
    (PMF.uniformOfFintype Bool).bind fun b =>
      if b then (PMF.uniformOfFintype (Fin k)).map (repair x r)
      else normalizedLaw a (hist ++ [r]) x

/-- The law of the algorithm's reversed trajectory `[X_t, …, X₀]` on the requests `ρ`. -/
def algTraj [NeZero k] (a : Config M) (ρ : List (Config M)) (t : ℕ) : PMF (List (Config M)) :=
  trajLaw (hwangAlg a) a ρ t

end GeneralizedUniformServer.UnitWeights


