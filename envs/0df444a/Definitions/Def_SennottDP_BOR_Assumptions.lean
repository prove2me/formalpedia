-- Prove2me | Definitions.Def_SennottDP_BOR_Assumptions
-- name    : SennottDP_BOR_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T11:17:51.89843+00:00
-- url     : https://prove2.me/theorems/569f9b5c-2d49-4a81-b1b6-431b3d1a9d40
-- title:
--   The (BOR) and (CAV) assumptions and the low-cost sets $D$, $D_U$, $D(e)$
-- statement:
--   For $U\in[0,\infty]$ let $D_U=\{i\mid C(i,a)\le U\text{ for some }a\in A_i\}$, and for a stationary policy $e$ let $D(e)=\{i\mid C(i,e)\le U\}$ (used with $U=J+\varepsilon$). For a $z$ standard policy $d$, $R_d$ denotes its positive recurrent class, the communicating class of $z$ in the chain induced by $d$, and $J_d$ its (constant) average cost.
--
--   The **(BOR) assumptions** (Theorem 7.5.6) for $z$, $d$ and $\varepsilon$:
--
--   1. (BOR1) $d$ is a $z$ standard policy with positive recurrent class $R_d$;
--   2. (BOR2) $\varepsilon>0$ and $D=\{i\mid C(i,a)\le J_d+\varepsilon\text{ for some }a\}$ is a finite set;
--   3. (BOR3) for every $i\in D-R_d$ there exists a policy $\theta_i\in\Re^*(z,i)$.
--
--   The **(CAV) assumptions** (Corollary 7.5.9) for $z$ and $d$:
--
--   1. (CAV1) = (BOR1);
--   2. (CAV2) for every $U>0$ the set $D_U$ is finite;
--   3. (CAV3) for every $i\in S-R_d$ there exists a policy $\theta_i\in\Re^*(z,i)$.
--
--   **Formalization Note** $J_d$ is written as $J_d(z)$, the average cost of $d$ from $z$ (it does not depend on the initial state for a $z$ standard policy, Proposition C.2.6(iii)). $R_d$ is the communicating class of $z$ (Proposition C.2.6(i)).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 145, Theorem 7.5.6 (BOR1)–(BOR3); p. 148, Corollary 7.5.9 (CAV1)–(CAV3); p. 301, Proposition C.2.6

import Mathlib
import Definitions.Def_SennottDP_BOR_FirstPassage

open scoped ENNReal NNReal

namespace SennottDP.BOR

variable {S : Type} [Countable S] {Act : Type}

/-- The states at which some action costs at most `U`: `{i | C(i,a) ≤ U for some a ∈ A_i}`.
With `U = J_d + ε` this is the set `D` of (BOR2), p. 145; with a real `U > 0` it is the set
`D_U` of (CAV2), p. 148. -/
def lowCostSet (M : SennottDP.Discounted.MDC S Act) (U : ℝ≥0∞) : Set S :=
  {i | ∃ a ∈ M.A i, (M.C i a : ℝ≥0∞) ≤ U}

/-- Sennott (1999), Theorem 7.5.6(ii), p. 145: for a stationary policy `e`, the set
`D(e) = {i | C(i,e) ≤ U}` (used with `U = J + ε`). -/
def lowCostSetOf (M : SennottDP.Discounted.MDC S Act) (e : StationaryPolicy M) (U : ℝ≥0∞) : Set S :=
  {i | (M.C i (e.1 i) : ℝ≥0∞) ≤ U}

/-- The positive recurrent class `R_d` of a `z` standard policy `d`: the communicating class of
`z` in the Markov chain induced by `d` (Proposition C.2.6(i), p. 301: a `z` standard chain
consists of one positive recurrent class containing `z` and transient states). -/
def recClass (M : SennottDP.Discounted.MDC S Act) (d : RandStationaryPolicy M) (z : S) : Set S :=
  commClass d.toPolicy z

/-- Sennott (1999), Theorem 7.5.6, p. 145: the (BOR) assumptions for the distinguished state
`z`, the (randomized) stationary policy `d` and the constant `ε`:
* (BOR1) `d` is a `z` standard policy, with positive recurrent class `R_d`;
* (BOR2) `ε > 0` and `D = {i | C(i,a) ≤ J_d + ε for some a}` is finite, where `J_d` is the
  (constant) average cost of `d`, written here as its value `J_d(z)`;
* (BOR3) for every `i ∈ D − R_d` there is a policy `θ_i ∈ ℜ*(z, i)`. -/
def BORAssumptions (M : SennottDP.Discounted.MDC S Act) (z : S) (d : RandStationaryPolicy M) (ε : ℝ) : Prop :=
  IsZStandard d.toPolicy z ∧
  (0 < ε ∧ (lowCostSet M (avgCost d.toPolicy z + ENNReal.ofReal ε)).Finite) ∧
  ∀ i ∈ lowCostSet M (avgCost d.toPolicy z + ENNReal.ofReal ε) \ recClass M d z,
    ∃ θ : SennottDP.Discounted.Policy M, InRStar θ z {i}

/-- Sennott (1999), Corollary 7.5.9, p. 148: the (CAV) assumptions for `z` and `d`:
* (CAV1) = (BOR1): `d` is a `z` standard policy with positive recurrent class `R_d`;
* (CAV2) for every `U > 0` the set `D_U = {i | C(i,a) ≤ U for some a}` is finite;
* (CAV3) for every `i ∈ S − R_d` there is a policy `θ_i ∈ ℜ*(z, i)`. -/
def CAVAssumptions (M : SennottDP.Discounted.MDC S Act) (z : S) (d : RandStationaryPolicy M) : Prop :=
  IsZStandard d.toPolicy z ∧
  (∀ U : ℝ, 0 < U → (lowCostSet M (ENNReal.ofReal U)).Finite) ∧
  ∀ i ∉ recClass M d z, ∃ θ : SennottDP.Discounted.Policy M, InRStar θ z {i}

end SennottDP.BOR


