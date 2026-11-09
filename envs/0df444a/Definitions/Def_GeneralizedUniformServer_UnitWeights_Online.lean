-- Prove2me | Definitions.Def_GeneralizedUniformServer_UnitWeights_Online
-- name    : GeneralizedUniformServer_UnitWeights_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:45.61562+00:00
-- url     : https://prove2.me/theorems/aeae0885-0e9c-4d25-afc9-f160a60427b2
-- title:
--   Randomized online algorithms as transition kernels, their trajectory law and expected cost
-- statement:
--   A **randomized online algorithm** starts in configuration $X_0=a$. When request $r_t$ arrives it draws its next configuration $X_t$ from a probability distribution $A(r_1,\dots,r_{t-1};\,X_{t-1};\,r_t)$ on $X$ that depends only on the earlier requests, the current configuration and the new request, using fresh private randomness. The request sequence $\rho$ is fixed in advance (oblivious adversary).
--
--   Composing these transitions gives the joint law of the trajectory $(X_0,X_1,\dots,X_t)$ for each $t\le T$. The algorithm's cost on $\rho=(r_1,\dots,r_T)$ is
--   $$\mathrm{ALG}(\rho)=\sum_{t=1}^{T} d(X_{t-1},X_t),$$
--   and $\mathbb E[\mathrm{ALG}(\rho)]$ is its expectation under the trajectory law.
--
--   This is the online-algorithm interface of §2 in the form needed by the goal theorem and the algorithm of §3.2.
--
--   **Formalization Note** A transition is a `PMF` on configurations (no measurability or countability needed). Trajectories are stored reversed, $[X_t,\dots,X_0]$, as lists; after the last request the trajectory is frozen. Expectations are sums in $[0,\infty]$, so no integrability side condition and no default value enters. The interface lets the algorithm see the past requests and its current configuration; this is the information the algorithm of §3.2 uses.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 8, §2 (online algorithms, oblivious adversary)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Model

noncomputable section

namespace GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

/-- A randomized online algorithm (source §2, p. 8), in transition-kernel form: when the
request `r_t` arrives, the algorithm draws its next configuration `X_t` from
`A hist x r_t`, where `hist = (r₁, …, r_{t-1})` are the earlier requests and `x = X_{t-1}`
its current configuration. Fresh private randomness is used at every step; the law may
depend on the past requests and the current configuration only (never on future requests). -/
abbrev OnlineAlg (M : Fin k → Type*) : Type _ :=
  List (Config M) → Config M → Config M → PMF (Config M)

/-- The law of the reversed trajectory `[X_t, X_{t-1}, …, X₀]` of the online algorithm `A`
started at `X₀ = a` after the first `t` requests of `ρ`: the actual joint law obtained by
composing the transitions. After the last request (`t ≥ ρ.length`) the trajectory is frozen. -/
def trajLaw (A : OnlineAlg M) (a : Config M) (ρ : List (Config M)) : ℕ → PMF (List (Config M))
  | 0 => PMF.pure [a]
  | t + 1 => (trajLaw A a ρ t).bind fun p =>
      if h : t < ρ.length then
        (A (ρ.take t) (p.headD a) ρ[t]).map fun y => y :: p
      else PMF.pure p

/-- Movement cost of a reversed trajectory `[X_t, …, X₀]`: `∑ d(X_{s-1}, X_s)`. -/
def pathCost : List (Config M) → ℕ
  | x :: y :: rest => dist y x + pathCost (y :: rest)
  | _ => 0

/-- Cost `d(X_{t-1}, X_t)` of the most recent step of a reversed trajectory `[X_t, X_{t-1}, …]`
(zero on a trajectory with fewer than two entries). -/
def lastStepCost : List (Config M) → ℕ
  | x :: y :: _ => dist y x
  | _ => 0

/-- `E[ALG(ρ)]`: the expected total movement cost of `A` on the whole finite sequence `ρ`,
under the joint trajectory law, computed in `ℝ≥0∞` (no integrability side condition). -/
def expectedCost (A : OnlineAlg M) (a : Config M) (ρ : List (Config M)) : ENNReal :=
  ∑' p : List (Config M), trajLaw A a ρ ρ.length p * (pathCost p : ENNReal)

end GeneralizedUniformServer.UnitWeights


