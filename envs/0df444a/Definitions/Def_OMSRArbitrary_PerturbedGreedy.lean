-- Prove2me | Definitions.Def_OMSRArbitrary_PerturbedGreedy
-- name    : OMSRArbitrary_PerturbedGreedy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:29.619193+00:00
-- url     : https://prove2.me/theorems/bc1d5dec-15c0-4435-8ca6-2307533fea03
-- title:
--   Perturbed Greedy with an arbitrary perturbation function, its runs from $(S,s)$, and the correlated model
-- statement:
--   Fix an instance with resources $U$, arrivals $t$ in order, edges $E$ with success probabilities $p_{it}$ and weights $r_i$, a perturbation function $g$, and seeds $u=(u_k)_{k\in U}$.
--
--   1. The **reduced price** of $k$ at $t$ is $r_kp_{kt}(1-g(u_k))$.
--   2. **Perturbed Greedy** (PG), on the arrival of $t$, probes the available resource with an edge to $t$ of maximum reduced price, breaking ties in a fixed order of the resources; it probes nothing if there is none.
--   3. A **run from $(S,s)$** starts at arrival $s$ with available set $S$; at each arrival $t\ge s$ it probes PG's choice from the current available set, and a successful probe consumes the resource. PG$(u)$ is the run from all resources at the first arrival, PG$^{-i}$ the run from $U\setminus\{i\}$ with the same seeds. The run records its available set before each arrival, its probe, the reduced price $P_t$ of its probe ($0$ if none) and the outcome.
--   4. The **best alternative** $J_\tau$ of a run at $\tau$ is the resource it would probe at $\tau$ if $i$ were removed from its current available set (Definition 12).
--   5. In the **correlated model** thresholds $z=(z_t)$ are i.i.d. uniform on $[0,1]$ and edge $(k,t)$ succeeds iff $z_t\le p_{kt}$.
--   6. $\mathbb E[\mathrm{PG}]$ is the expected total reward of PG$(u)$, $u_k$ i.i.d. uniform on $[0,1]$, either in the independent model (edges succeed independently) or in the correlated model; $\Pr[\mathrm{PG}(u)\text{ matches }i]$ is over $z$ with $u$ fixed.
--
--   **Formalization Note** Resources are `Fin n`, arrivals `Fin m` (0-based). The fixed tie order is the index order (the published `bestOf` keeps the earlier element on ties), which has the deterministic tie-breaking property of p.12. The instance, independent-model average `edgeAverage`, seed law `seedLaw` (uniform on $[0,1]^n$) and `bestOf` are the published `StochasticRewardMatching.Decomposable` definitions; its fixed $g=e^{x-1}$ is not used. PG$^{-i}$ never reads $u_i$.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §2 (Perturbed Greedy, Independent and Correlated Models, Deterministic Tie Breaking), pp.10–12; Definition 12, p.18; §3.1 (Coupling), p.13

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Instance
import Definitions.Def_StochasticRewardMatching_Decomposable_EdgeLaw
import Definitions.Def_StochasticRewardMatching_Decomposable_FiniteChoice
import Definitions.Def_StochasticRewardMatching_Decomposable_Seeds

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Outcome bit edgeAverage Seeds seedLaw seedAverage bestOf)
noncomputable section

namespace OMSRArbitrary

variable {n m : ℕ}

/-- **Reduced price** `r_k p_{kt}(1 − g(u_k))` of resource `k` at arrival `t` under seeds `u`,
arXiv:2611.03598, §2 ("Perturbed Greedy"), p.11.

**Formalization Note.** Resources are `Fin n`, arrivals `Fin m` (0-based); the instance is the
published `StochasticRewardMatching.Decomposable.Instance`. -/
def reducedPrice (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (k : Fin n) (t : Fin m) : ℝ :=
  D.reward k * D.probability (k, t) * (1 - g (u k))

/-- **The choice of Perturbed Greedy** from an available set `S` at arrival `t`,
arXiv:2611.03598, §2, p.11: among the resources of `S` with an edge to `t`, the one with the
maximum reduced price, "breaking ties in a fixed order of the resources"; `none` when there is
no such resource (`A_t = ∅`).

**Formalization Note.** The fixed order is the index order: the candidates are listed in
increasing index and the published `bestOf` keeps the earlier element on ties. This has the
deterministic tie-breaking property of p.12 (if `k` is selected from `A` and `k ∈ B ⊆ A`, `k` is
selected from `B`). Resources may be relabelled freely, so every fixed order is of this form. -/
def pgChoice (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (t : Fin m) :
    Option (Fin n) :=
  bestOf (fun k => reducedPrice D g u k t)
    ((List.finRange n).filter (fun k => decide (k ∈ S ∧ (k, t) ∈ D.edges)))

/-- **The available set of a run of PG from `(S, s)`**: `pgAvail D g u S s ω t` is the set of
available resources just before arrival `t` (0-based) of the run of Perturbed Greedy with seeds
`u` that starts at arrival `s` with available set `S`, under the edge outcomes `ω`
(arXiv:2611.03598, §2, p.11; runs from an arbitrary arrival and set are used in Lemma 13, p.18,
and in the definition of `Q_t(A)`, p.25). Before arrival `s` the set is `S`; at each arrival
`t ≥ s` PG probes `pgChoice` and, if the probe succeeds, the probed resource is consumed. -/
def pgAvail (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (ω : Outcome D) : ℕ → Finset (Fin n)
  | 0 => S
  | t + 1 =>
    if h : s ≤ t ∧ t < m then
      match pgChoice D g u (pgAvail D g u S s ω t) ⟨t, h.2⟩ with
      | some k => if bit D ω (k, ⟨t, h.2⟩) then (pgAvail D g u S s ω t).erase k
          else pgAvail D g u S s ω t
      | none => pgAvail D g u S s ω t
    else pgAvail D g u S s ω t

/-- **The probe of the run from `(S, s)` at arrival `t`** (`none` = no probe; arrivals before `s`
are not processed by this run). -/
def pgProbe (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (ω : Outcome D) (t : Fin m) : Option (Fin n) :=
  if s ≤ t.val then pgChoice D g u (pgAvail D g u S s ω t.val) t else none

/-- **The reduced price of the probe at `t`** (`P_t`, or `P_t^{−i}` for the run without `i`),
`0` if the run probes nothing, arXiv:2611.03598, §2, p.11 ("We set P_t = 0 when A_t = ∅") and
§4, p.15. -/
def pgPrice (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (ω : Outcome D) (t : Fin m) : ℝ :=
  match pgProbe D g u S s ω t with
  | some k => reducedPrice D g u k t
  | none => 0

/-- The observed outcome of the probe at `t` (`false` if the run probes nothing). -/
def pgOutcome (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (ω : Outcome D) (t : Fin m) : Bool :=
  match pgProbe D g u S s ω t with
  | some k => bit D ω (k, t)
  | none => false

/-- The run from `(S, s)` **matches `i` at `t`**: it probes `i` at `t` and the probe succeeds. -/
def pgMatchesAt (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (ω : Outcome D) (i : Fin n) (t : Fin m) : Prop :=
  pgProbe D g u S s ω t = some i ∧ bit D ω (i, t) = true

/-- The run from `(S, s)` **matches `i`** at some arrival. -/
def pgMatches (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (ω : Outcome D) (i : Fin n) : Prop :=
  ∃ t, pgMatchesAt D g u S s ω i t

/-- **Total reward of PG(u)**: the run from all resources at the first arrival; each successful
probe of `k` yields `r_k` (arXiv:2611.03598, §2, p.10). -/
def pgReward (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (ω : Outcome D) : ℝ :=
  ∑ t : Fin m,
    match pgProbe D g u Finset.univ 0 ω t with
    | some k => if bit D ω (k, t) then D.reward k else 0
    | none => 0

/-- **The best alternative** `J_τ` of the run from `(S, s)` at `τ`: the resource PG would probe at
`τ` if `i` were removed from its current available set, arXiv:2611.03598, Definition 12, p.18
(restated p.40). `none` when there is none. -/
def bestAlt (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (S : Finset (Fin n)) (s : ℕ)
    (ω : Outcome D) (i : Fin n) (τ : Fin m) : Option (Fin n) :=
  pgChoice D g u ((pgAvail D g u S s ω τ.val).erase i) τ

/-- **The correlated model**, arXiv:2611.03598, §2, p.11: thresholds `z = (z_t)` (i.i.d. uniform on
`[0,1]` under `seedLaw m`), and edge `(k, t)` succeeds iff `z_t ≤ p_{kt}`. -/
def corrOutcome (D : Instance n m) (z : Seeds m) : Outcome D :=
  fun e => decide (z e.1.2 ≤ D.probability e.1)

/-- **E[PG] in the independent model**: the expected total reward of Perturbed Greedy, edges
succeeding independently (`edgeAverage`) and seeds `u ∼ U[0,1]^n` (`seedAverage`),
arXiv:2611.03598, §2, pp.10–11. -/
def pgValue (D : Instance n m) (g : ℝ → ℝ) : ℝ :=
  edgeAverage D (fun ω => seedAverage (fun u => pgReward D g u ω))

/-- **E[PG] in the correlated model**: seeds `u ∼ seedLaw n`, thresholds `z ∼ seedLaw m`
(arXiv:2611.03598, §3.1, p.13). -/
def pgValueCorr (D : Instance n m) (g : ℝ → ℝ) : ℝ :=
  ∫ u, (∫ z, pgReward D g u (corrOutcome D z) ∂seedLaw m) ∂seedLaw n

open Classical in
/-- `Pr[PG(u) matches i]` over the thresholds `z`, seeds fixed (arXiv:2611.03598, §4, p.15:
"every expectation E and probability Pr in this section is over the thresholds z only"). -/
def matchProb (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) : ℝ :=
  ∫ z, (if pgMatches D g u Finset.univ 0 (corrOutcome D z) i then (1 : ℝ) else 0) ∂seedLaw m

end OMSRArbitrary


