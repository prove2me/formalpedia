-- Prove2me | Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Online
-- name    : GeneralizedUniformServer_UnitWeights_Supplement_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:38:39.032634+00:00
-- url     : https://prove2.me/theorems/8f94b27f-2042-4958-8db8-f28ea555b467
-- title:
--   General randomized online algorithms (history-dependent kernels), their trajectory law and expected unit cost
-- statement:
--   Let $X=M_1\times\cdots\times M_k$ be the configuration space of the mission's model and let requests range over a set $\mathcal R$ (tuples $r\in X$ for Theorems 1.2 and 1.3, set requests for Theorem 3.5). A **randomized online algorithm** starts in configuration $X_0=a$. When request $r_t$ arrives it draws its next configuration $X_t$ from a probability distribution
--   $$A\bigl(r_1,\dots,r_{t-1};\;X_{t-1},\dots,X_0;\;r_t\bigr)$$
--   on $X$, which may depend on all earlier requests, on the algorithm's whole configuration history and on the new request, but never on future requests; fresh private randomness is used at each step. The algorithm **serves** if every configuration it can move to serves the current request. The request sequence $\rho$ is fixed in advance (oblivious adversary).
--
--   Binding these transitions gives the joint law of the trajectory $(X_0,\dots,X_t)$. With unit distances the algorithm's cost on $\rho=(r_1,\dots,r_T)$ is $\mathrm{ALG}(\rho)=\sum_{t=1}^T d(X_{t-1},X_t)$, with $d$ the Hamming distance, and $\mathbb E[\mathrm{ALG}(\rho)]$ is its expectation under the trajectory law.
--
--   This is the general algorithm class of §2: a lower bound (Theorem 1.2) must hold against every algorithm, and the algorithm of Theorem 1.3 keeps hidden state, so the published Markov interface (which sees only the current configuration) does not suffice.
--
--   **Formalization Note** A transition is a `PMF` on configurations. This behavioural form represents every randomized online algorithm on a finite configuration space, including mixtures of deterministic algorithms and algorithms with internal memory: for a fixed request sequence the law of $X_t$ given the observed history $(r_1,\dots,r_t,X_0,\dots,X_{t-1})$ is such a kernel (Kuhn's theorem for perfect recall). Trajectories are stored reversed, $[X_t,\dots,X_0]$, and are frozen after the last request. Expectations are sums in $[0,\infty]$, so no integrability side condition or default value enters. Serving is required on every history, which loses nothing: since a request serves itself, an algorithm that serves on the histories it can reach can be changed on the others without changing its law.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 8, §2 (online algorithms, randomized online algorithms, oblivious adversary)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Online

noncomputable section

namespace GeneralizedUniformServer.UnitWeights.Supplement

variable {k : ℕ} {M : Fin k → Type*}

/-- A general randomized online algorithm (source §2, p. 8) for requests of type `R`, in
behavioural (transition-kernel) form. When request `r_t` arrives, the algorithm draws its next
configuration `X_t` from `A hist path r_t`, where `hist = (r₁, …, r_{t-1})` are the earlier
requests and `path = [X_{t-1}, …, X₁, X₀]` is its whole configuration history, most recent
first. Fresh private randomness is used at every step and future requests are never seen.
By Kuhn's theorem (perfect recall) this class realizes the trajectory law of every randomized
online algorithm on finite configuration spaces, including mixtures of deterministic ones. -/
abbrev GenOnlineAlg (M : Fin k → Type*) (R : Type*) : Type _ :=
  List R → List (Config M) → R → PMF (Config M)

/-- The algorithm always serves: every configuration it can move to serves the current
request, for the service relation `serves x r`. -/
def IsServing {R : Type*} (serves : Config M → R → Prop) (A : GenOnlineAlg M R) : Prop :=
  ∀ (hist : List R) (path : List (Config M)) (r : R) (y : Config M),
    y ∈ (A hist path r).support → serves y r

/-- The law of the reversed trajectory `[X_t, X_{t-1}, …, X₀]` of `A` started at `X₀ = a`
after the first `t` requests of `ρ`: the joint law obtained by binding the transition kernels.
After the last request (`t ≥ ρ.length`) the trajectory is frozen. -/
def genTrajLaw {R : Type*} (A : GenOnlineAlg M R) (a : Config M) (ρ : List R) :
    ℕ → PMF (List (Config M))
  | 0 => PMF.pure [a]
  | t + 1 => (genTrajLaw A a ρ t).bind fun p =>
      if h : t < ρ.length then
        (A (ρ.take t) p ρ[t]).map fun y => y :: p
      else PMF.pure p

/-- `E[ALG(ρ)]` with unit distances: the expected Hamming movement cost
`∑_{t=1}^T d(X_{t-1}, X_t)` of `A` on the whole finite sequence `ρ`, under the joint trajectory
law, computed in `ℝ≥0∞`. -/
def genExpectedCost {R : Type*} (A : GenOnlineAlg M R) (a : Config M) (ρ : List R) : ENNReal :=
  ∑' p : List (Config M), genTrajLaw A a ρ ρ.length p * (pathCost p : ENNReal)

end GeneralizedUniformServer.UnitWeights.Supplement


