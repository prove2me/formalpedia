-- Prove2me | Definitions.Def_LargeCongestion_Poisson_Supplement_PoissonCongestion
-- name    : LargeCongestion_Poisson_Supplement_PoissonCongestion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:28:02.495803+00:00
-- url     : https://prove2.me/theorems/061dec5a-e5f4-4515-a1b4-8d7b4a88f815
-- title:
--   §5.2 — independent Poisson populations (26), congestion specialization (27), and induced flows
-- statement:
--   The Poisson game is the general population game with independent populations of positive real means $d_t$:
--   $$\mu(n)=\prod_t e^{-d_t}\frac{d_t^{n_t}}{n_t!}.$$
--   Its equilibrium uses the general Palm posterior and multinomial mixture; posterior invariance is not installed as an assumption. The published Poisson probability function supplies the mass of each coordinate.
--
--   For congestion games, specialize $A_t$ to the subtype of feasible resource subsets $s\in S_t$. Given other-player strategy counts $n$, define
--   $$X_e^{-t}=\sum_{t',s'\in S_{t'}}n_{t',s'}\mathbf1_{\{e\in s'\}},\qquad C(n;t,s)=\sum_{e\in s}c_e(1+X_e^{-t}).$$
--   The distinguished active player contributes the $1$ inside every cost. From a type profile $q$, construct $y_{t,s}=d_tq_t(s)$ and $x_e=\sum_{t,s\in S_t}y_{t,s}\mathbf1_{\{e\in s\}}$, with zero flow outside feasible strategies.
--
--   This supplies the two different equilibrium models compared in Theorem 3. The costs are evaluated on full random count vectors; independent strategy counts do not assert independence of overlapping resource loads.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 22–23, (26)–(28), Theorem 3

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_Population

namespace LargeCongestion.Poisson.Supplement

/-- Independent Poisson populations (26), using the base Poisson mass function. -/
noncomputable def poissonPopulation {T : Type*} [Fintype T] (d : T → ℝ) (n : T → ℕ) : ℝ :=
  ∏ t, poissonPmf (d t) (n t)

/-- A Poisson game is the general population game with the independent populations (26).
Its equilibrium still uses the Palm posterior; posterior invariance is not assumed. -/
noncomputable def poissonGame {T : Type*} [Fintype T] {A : T → Type*}
    (d : T → ℝ) (C : (Sigma A → ℕ) → Sigma A → ℝ) :
    PopulationGame T A := ⟨poissonPopulation d, C⟩

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

/-- Congestion actions specialize the arbitrary action spaces of the population game. -/
abbrev CongestionAction (S : T → Finset (Finset E)) (t : T) := {s : Finset E // s ∈ S t}

/-- Aggregate other-player resource load in (27); resources need not be independent. -/
def countLoad (S : T → Finset (Finset E)) (n : Sigma (CongestionAction S) → ℕ) (e : E) : ℕ :=
  ∑ p : Sigma (CongestionAction S), if e ∈ p.2.val then n p else 0

/-- Exact congestion specialization (27), with the distinguished active player included by +1. -/
def congestionCost (S : T → Finset (Finset E)) (c : E → ℕ → ℝ)
    (n : Sigma (CongestionAction S) → ℕ) (p : Sigma (CongestionAction S)) : ℝ :=
  ∑ e ∈ p.2.val, c e (1 + countLoad S n e)

/-- The flow y_{t,s}=d_t sigma_t(s), extended by zero off the feasible action family. -/
def inducedFlow (S : T → Finset (Finset E)) (d : T → ℝ)
    (q : ∀ t, CongestionAction S t → ℝ) (t : T) (s : Finset E) : ℝ :=
  if h : s ∈ S t then d t * q t ⟨s, h⟩ else 0

/-- The resource-incidence map in Theorem 3. -/
def inducedLoad (S : T → Finset (Finset E)) (d : T → ℝ)
    (q : ∀ t, CongestionAction S t → ℝ) (e : E) : ℝ :=
  ∑ t, ∑ s ∈ S t, if e ∈ s then inducedFlow S d q t s else 0

end LargeCongestion.Poisson.Supplement


