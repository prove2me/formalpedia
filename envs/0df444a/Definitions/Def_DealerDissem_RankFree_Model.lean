-- Prove2me | Definitions.Def_DealerDissem_RankFree_Model
-- name    : DealerDissem_RankFree_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:37.101205+00:00
-- url     : https://prove2.me/theorems/47df6df3-f9da-471c-9bba-6b99834184c1
-- title:
--   §2–§3, Definition 1, (1)–(5), (9), (10), (14), (46), pp. 7–15 — dealer offer game, rank-free equilibrium, collected demand, Theorem 2 strategies
-- statement:
--   The model of Colliard and Demange: an asset is passed along a chain of dealers $D_1, D_2, \dots$ by take-it-or-leave-it offers.
--
--   1. **Parameters** (§2.1). The asset pays a sure return $\rho>0$ per unit; dealers borrow at the funding spread $r>0$; each dealer is available with probability $q\in(0,1)$.
--   2. **Customer demand.** Each dealer's customer demand $\omega$ is drawn i.i.d. from a distribution $G$ on $\mathbb R_+$ with finite mean, and $H(\omega)=\Pr(\tilde\omega\ge\omega)$ (closed upper tail).
--   3. **Financing needs** (1). A dealer of type $\omega$ who accepts the offer $(p,v)$ (volume $v$ at unit price $p$) has financing needs $y=\max(pv-\omega,0)$.
--   4. **Acceptance probability** (Definition 1 (i)). For an acceptance rule $A(p,v,\omega)$, $\Phi(p,v)=\Pr(A(p,v,\tilde\omega)=1)$.
--   5. **Expected profit** (5). A dealer who accepted $(p',v')$, has type $\omega$ and financing needs $y$, and makes the new offer $(p,v)$, expects
--   $$\pi(p',v',\omega,p,v)=(\rho-p')v'-ry+q\,\Phi(p,v)\bigl[r\min(pv,y)-(\rho-p)v\bigr].$$
--   A new offer is **feasible** if $p\ge0$ and $0\le v\le v'$.
--   6. **Rank-free equilibrium** (Definition 1). A strategy $(A,P,V)$ is a rank-free equilibrium if acceptance events for feasible offers are measurable and for every $(p',v',\omega)\in\mathbb R_+^3$: (a) if $A(p',v',\omega)=1$, the offer $(P,V)(p',v',\omega)$ is feasible and maximizes $\pi$ over all feasible offers, with $\Phi$ computed from the same $A$; (b) $A(p',v',\omega)=1$ if and only if some feasible offer gives a non-negative profit.
--   7. **Collected demand.** The objective $qH(\omega)(\omega+\Omega(y-\omega))$ of (9)–(10); the operator $\Psi(\beta)(y)=\sup_{0\le\omega\le y}qH(\omega)(\omega+\beta(y-\omega))$ of (46); the predicate "$\Omega$ solves (9)": $\Omega(0)=0$ and $\Omega(y)=\Psi(\Omega)(y)$ for $y>0$; the targeted values $\mathcal T(y)=\arg\max_{0\le\omega\le y}qH(\omega)(\omega+\Omega(y-\omega))$ of (10); a selection $T$ with $T(y)\in\mathcal T(y)$ for every $y\ge0$; and the class $\mathcal F_+$ of functions bounded and continuous on $\mathbb R_+$, non-negative there, with $\beta(0)=0$.
--   8. **Theorem 2 strategies.** $\pi^*(p,v,y)=(\rho-p)v-ry+r\Omega(y)$; accept $(p,v)$ iff $\pi^*(p,v,\max(pv-\omega,0))\ge0$; on acceptance offer $(P(y),V(y))$ solving (14), that is
--   $$\rho V(y)=(1+r)y-r\bigl[T(y)+\Omega(y-T(y))\bigr],\qquad P(y)=y/V(y).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Functions of $y$ are `ℝ → ℝ`; only their values on $[0,\infty)$ are ever constrained or used. The acceptance rule is a `Prop`-valued predicate, and $\Phi$ is the measure of its acceptance set, so it is never a free parameter. The equilibrium predicate requires feasible-offer acceptance events to be measurable so that $\Phi$ is a probability, as Definition 1 (i) says. Definition 1 (ii) is read as clauses (a)–(b): optimality is required after acceptance only, since the strategy's offer after a rejection is never made; (b) is an equivalence, which with (a) says "accept iff the maximal profit is non-negative". $V(y)$ is (14) solved for $V$, i.e. the paper's (16); at $y=0$ it equals $0$ ("no further offer"), and $P(0)=0/0$ is Lean's junk value $0$, which is harmless because the volume is $0$. For $y<0$, $\Psi(\beta)(y)$ is a supremum over the empty set (junk value $0$), never used.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), pp. 7–15 (PDF 9–17), §2.1, §2.2, Definition 1, (1)–(5), (9), (10), (14), (16); p. 39 (PDF 41), (46)

import Mathlib

namespace DealerDissem.RankFree

open MeasureTheory

/-- Standing parameters of §2.1 (p. 7): the sure asset return `ρ > 0`, the funding spread
`r > 0` and the availability probability `q ∈ (0, 1)`. -/
structure Params where
  ρ : ℝ
  r : ℝ
  q : ℝ
  hρ : 0 < ρ
  hr : 0 < r
  hq0 : 0 < q
  hq1 : q < 1

/-- `H(ω) = Pr(ω̃ ≥ ω)` (p. 7), the closed upper tail of the customer-demand law `μ`. -/
noncomputable def survival (μ : Measure ℝ) (ω : ℝ) : ℝ := (μ (Set.Ici ω)).toReal

/-- The customer-demand distribution `G` of §2.1: a probability distribution over `ℝ₊`
with finite mean. -/
structure IsDemandDist (μ : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  nonneg : μ (Set.Iio 0) = 0
  mean : Integrable id μ

/-- The objective of (9)/(10)/(46): `q H(ω) (ω + Ω(y − ω))`. -/
noncomputable def objective (P : Params) (μ : Measure ℝ) (Ω : ℝ → ℝ) (y ω : ℝ) : ℝ :=
  P.q * survival μ ω * (ω + Ω (y - ω))

/-- The mapping `Ψ` of (46): `Ψ(β)(y) = sup_{0 ≤ ω ≤ y} q H(ω)(ω + β(y − ω))`.
(For `y < 0` the interval is empty and the value is Lean's junk `sSup ∅ = 0`.) -/
noncomputable def Psi (P : Params) (μ : Measure ℝ) (β : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup (objective P μ β y '' Set.Icc 0 y)

/-- `Ω` solves the functional equation (9): `Ω(0) = 0` and, for every `y > 0`,
`Ω(y) = sup_{0 ≤ ω ≤ y} q H(ω)(ω + Ω(y − ω))`. -/
def SolvesCollected (P : Params) (μ : Measure ℝ) (Ω : ℝ → ℝ) : Prop :=
  Ω 0 = 0 ∧ ∀ y, 0 < y → Ω y = sSup (objective P μ Ω y '' Set.Icc 0 y)

/-- `f` is bounded on `ℝ₊`. -/
def BoundedOnNonneg (f : ℝ → ℝ) : Prop := ∃ C, ∀ y, 0 ≤ y → |f y| ≤ C

/-- Membership in `𝓕₊`: the non-negative members of the space `𝓕` of the proof of
Theorem 1 (p. 39), i.e. `β` bounded and continuous on `ℝ₊`, `β(0) = 0` and `β ≥ 0` on `ℝ₊`. -/
def InFPlus (β : ℝ → ℝ) : Prop :=
  BoundedOnNonneg β ∧ ContinuousOn β (Set.Ici 0) ∧ β 0 = 0 ∧ ∀ y, 0 ≤ y → 0 ≤ β y

/-- The targeted values (10): the maximizers of the objective of (9) over `0 ≤ ω ≤ y`. -/
def targets (P : Params) (μ : Measure ℝ) (Ω : ℝ → ℝ) (y : ℝ) : Set ℝ :=
  {ω ∈ Set.Icc 0 y | ∀ ω' ∈ Set.Icc 0 y, objective P μ Ω y ω' ≤ objective P μ Ω y ω}

/-- A selection of `𝒯` (p. 15): `T(y) ∈ 𝒯(y)` for every `y ≥ 0`. -/
def IsSelection (P : Params) (μ : Measure ℝ) (Ω T : ℝ → ℝ) : Prop :=
  ∀ y, 0 ≤ y → T y ∈ targets P μ Ω y

/-- Financing needs (1): `y = max(p v − ω, 0)` for a received offer `(p, v)` and type `ω`. -/
def finNeeds (p v ω : ℝ) : ℝ := max (p * v - ω) 0

/-- Acceptance probability of Definition 1 (i): `Φ(p, v) = Pr(A(p, v, ω̃) = 1)`,
computed from the acceptance rule `A` itself. -/
noncomputable def accProb (μ : Measure ℝ) (A : ℝ → ℝ → ℝ → Prop) (p v : ℝ) : ℝ :=
  (μ {ω | A p v ω}).toReal

/-- The expected profit (5) of a dealer who accepted `(p', v')`, has type `ω` and makes the
offer `(p, v)`, when the next dealer follows the acceptance rule `A`:
`(ρ − p')v' − r y + q Φ(p, v) [r min(p v, y) − (ρ − p) v]`, `y = max(p'v' − ω, 0)`. -/
noncomputable def profit (P : Params) (μ : Measure ℝ) (A : ℝ → ℝ → ℝ → Prop)
    (p' v' ω p v : ℝ) : ℝ :=
  (P.ρ - p') * v' - P.r * finNeeds p' v' ω
    + P.q * accProb μ A p v * (P.r * min (p * v) (finNeeds p' v' ω) - (P.ρ - p) * v)

/-- A feasible new offer `(p, v) ∈ ℝ₊²` after accepting a volume `v'`: `v ≤ v'`. -/
def Feasible (v' p v : ℝ) : Prop := 0 ≤ p ∧ 0 ≤ v ∧ v ≤ v'

/-- Definition 1 (p. 10): the rank-free strategy `(A, P, V)` is a rank-free equilibrium.
For every received offer `(p', v')` and type `ω` in `ℝ₊`:
(a) if the dealer accepts, her new offer `(P, V)(p', v', ω)` is feasible and maximizes the
profit (5) over all feasible offers, where `Φ` is computed from the same `A`
(Definition 1 (i));
(b) she accepts iff some feasible offer gives a non-negative profit (5).
Acceptance events for feasible offers are measurable, so their measures are probabilities. -/
def IsRankFreeEquilibrium (P : Params) (μ : Measure ℝ) (A : ℝ → ℝ → ℝ → Prop)
    (Pf Vf : ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ p v, 0 ≤ p → 0 ≤ v → MeasurableSet {ω : ℝ | A p v ω}) ∧
  ∀ p' v' ω, 0 ≤ p' → 0 ≤ v' → 0 ≤ ω →
    (A p' v' ω →
        Feasible v' (Pf p' v' ω) (Vf p' v' ω) ∧
        ∀ p v, Feasible v' p v →
          profit P μ A p' v' ω p v ≤ profit P μ A p' v' ω (Pf p' v' ω) (Vf p' v' ω)) ∧
    (A p' v' ω ↔ ∃ p v, Feasible v' p v ∧ 0 ≤ profit P μ A p' v' ω p v)

/-- `π*(p, v, y) = (ρ − p) v − r y + r Ω(y)` (Theorem 2). -/
noncomputable def piStar (P : Params) (Ω : ℝ → ℝ) (p v y : ℝ) : ℝ :=
  (P.ρ - p) * v - P.r * y + P.r * Ω y

/-- The acceptance rule of Theorem 2: accept `(p, v)` with type `ω` iff `π*(p, v, y) ≥ 0`,
`y = max(p v − ω, 0)`. -/
def thmAccept (P : Params) (Ω : ℝ → ℝ) (p v ω : ℝ) : Prop :=
  0 ≤ piStar P Ω p v (finNeeds p v ω)

/-- The volume `V(y)` of Theorem 2, (14) solved for `V` (this is (16)):
`ρ V(y) = (1 + r) y − r [T(y) + Ω(y − T(y))]`. -/
noncomputable def offerV (P : Params) (Ω T : ℝ → ℝ) (y : ℝ) : ℝ :=
  ((1 + P.r) * y - P.r * (T y + Ω (y - T y))) / P.ρ

/-- The price `P(y) = y / V(y)` of Theorem 2, from `P(y) V(y) = y` in (14).
(At `y = 0`, `V(0) = 0` and Lean's `0 / 0 = 0` is a harmless junk value.) -/
noncomputable def offerP (P : Params) (Ω T : ℝ → ℝ) (y : ℝ) : ℝ :=
  y / offerV P Ω T y

end DealerDissem.RankFree


