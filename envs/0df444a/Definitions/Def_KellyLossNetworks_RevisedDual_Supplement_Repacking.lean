-- Prove2me | Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Repacking
-- name    : KellyLossNetworks_RevisedDual_Supplement_Repacking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:57:33.6504+00:00
-- url     : https://prove2.me/theorems/4433fb06-4b83-4a13-a529-3c8a00e231e9
-- title:
--   Full repacking policy class, optimal loss and canonical threshold strategy
-- statement:
--   On the complete graph with $K$ nodes, every edge has capacity $C$; calls between each pair arrive at rate $\nu$ and have independent unit-mean exponential holding periods. Feasibility allows a call to be divided among all simple paths between its endpoints and allows instantaneous rerouting. Stationary randomized admission rules may depend on the entire vector of numbers of calls between pairs. Their loss probability is the stationary fraction of offered calls rejected; $L_\nu(K)$ is the infimum over all such rules.
--
--   For a single link the weights of (4.51) are $\nu^n/n!$ up to $n=C+s$, with weight $\alpha\nu^n/n!$ at $C+s+1$, normalized to sum to one. Set $G_\nu(s,\alpha)=\mathbb E(n-C)^+$, $H_\nu(s,\alpha)=\mathbb E(C-n)^+$, and $L_\nu(s,\alpha)=1-\mathbb E n/\nu$. The canonical threshold satisfies
--   $$\bar s+\bar\alpha=\sup\{s+\alpha:s\in\mathbb N,\ 0\le\alpha<1,\ H_\nu(s,\alpha)>2G_\nu(s,\alpha)\}.$$
--   The supremum is extended nonnegative real. If it is infinite the provisional rule admits every call and $\bar L_\nu=0$; otherwise the canonical integer and fractional parts define $\bar L_\nu=L_\nu(\bar s,\bar\alpha)$. This includes the critical load. A provisionally accepted call is actually accepted exactly when the routing aim can be met: $\min(n_e,C)$ direct calls per pair, with the excess divided among two-edge paths using spare capacity.
--
--   The finite controlled generator and its normalized stationary balance equations determine each strategy's loss. No optimality condition is assumed. For $K\ge2$ the value sets are nonempty and lie in $[0,1]$, so their real infima do not encounter an empty or unbounded default.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp.360–362, (4.51)–(4.55)

import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_NetworkChains
import Definitions.Def_KellyLossNetworks_Routing_Model

open scoped NNReal ENNReal

open MeasureTheory
open scoped Classical

namespace KellyLossNetworks.RevisedDual.Supplement

/-- Simple paths in the complete K-node graph. Kelly (1991), §4.6, pp.360–361.
**Formalization Note.** All simple path lengths are allowed for repacking. Removing cycles
loses no feasible nonnegative flow. -/
def RepackRoute (K : ℕ) :=
  (l : Fin (K+1)) × {f : Fin l.val → Fin K // Function.Injective f ∧ 2 ≤ l.val}
noncomputable instance (K : ℕ) : Fintype (RepackRoute K) := by
  classical
  unfold RepackRoute
  infer_instance

/-- Endpoints of a route, and its undirected edges. -/
def RouteFor {K : ℕ} (p : RepackRoute K) (e : KellyLossNetworks.Routing.Edge K) : Prop :=
  ∃ i j : Fin p.1.val, i.val = 0 ∧ j.val + 1 = p.1.val ∧ e.1 = s(p.2.1 i, p.2.1 j)

def RouteUses {K : ℕ} (p : RepackRoute K) (e : KellyLossNetworks.Routing.Edge K) : Prop :=
  ∃ i j : Fin p.1.val, j.val = i.val + 1 ∧ e.1 = s(p.2.1 i, p.2.1 j)

/-- Full divisible repacking feasibility: arbitrary fractional flows over all simple paths,
with capacity C on every edge. Kelly (1991), p.360, §4.6. -/
def RepackFeasible {K : ℕ} (C : ℕ) (n : KellyLossNetworks.Routing.Edge K → ℕ) : Prop :=
  ∃ f : RepackRoute K → ℝ, (∀ p, 0 ≤ f p) ∧
    (∀ e, (∑ p, if RouteFor p e then f p else 0) = (n e : ℝ)) ∧
    ∀ e, (∑ p, if RouteUses p e then f p else 0) ≤ (C : ℝ)

/-- The finite state space for unrestricted repacking. Every call consumes at least one
edge unit, so the capacity of the whole network bounds each count. Kelly (1991), p.361.
This bound removes no feasible network state. -/
def RepackState (K C : ℕ) :=
  {n : KellyLossNetworks.Routing.Edge K →
      Fin (C * Fintype.card (KellyLossNetworks.Routing.Edge K) + 1) //
    RepackFeasible C (fun e => (n e).val)}
noncomputable instance (K C : ℕ) : Fintype (RepackState K C) := by
  classical
  unfold RepackState
  infer_instance
noncomputable instance (K C : ℕ) : DecidableEq (RepackState K C) := Classical.decEq _

/-- Addition/removal of one entire call between the endpoints of e. -/
def RepackBirth {K C : ℕ} (x y : RepackState K C)
    (e : KellyLossNetworks.Routing.Edge K) : Prop :=
  ∀ g, (y.1 g).val = (x.1 g).val + if g = e then 1 else 0

def RepackDeath {K C : ℕ} (x y : RepackState K C)
    (e : KellyLossNetworks.Routing.Edge K) : Prop :=
  0 < (x.1 e).val ∧ ∀ g, (y.1 g).val = (x.1 g).val - if g = e then 1 else 0

/-- Stationary randomized admission probabilities. Arbitrary functions of the full call
count vector are allowed. With instantaneous divisible repacking, no routing-state memory
is needed. Kelly (1991), p.361, definition of L_ν(K).
**Formalization Note.** This class encodes admissibility only, never optimality. -/
def IsRepackPolicy {K C : ℕ} (a : RepackState K C → KellyLossNetworks.Routing.Edge K → ℝ) : Prop :=
  (∀ x e, 0 ≤ a x e ∧ a x e ≤ 1) ∧
  ∀ x e, (¬ ∃ y, RepackBirth x y e) → a x e = 0

/-- The controlled generator: independent Poisson rate ν on every pair and independent
unit exponential holding times. Kelly (1991), pp.360–361. -/
noncomputable def repackGenerator {K C : ℕ} (nu : ℝ)
    (a : RepackState K C → KellyLossNetworks.Routing.Edge K → ℝ) :
    Matrix (RepackState K C) (RepackState K C) ℝ :=
  let q := fun x y : RepackState K C => ∑ e : KellyLossNetworks.Routing.Edge K, (
    (if RepackBirth x y e then nu * a x e else 0) +
    (if RepackDeath x y e then ((x.1 e).val : ℝ) else 0))
  fun x y => if x = y then -(∑ z, if z = x then 0 else q x z) else q x y

/-- Stationarity πQ=0, with an actual normalized finite-state probability distribution.
Kelly (1991), p.361. -/
def RepackStationary {K C : ℕ} (nu : ℝ)
    (a : RepackState K C → KellyLossNetworks.Routing.Edge K → ℝ)
    (pi : RepackState K C → ℝ) : Prop :=
  (∀ x, 0 ≤ pi x) ∧ (∑ x, pi x) = 1 ∧
    ∀ y, (∑ x, pi x * repackGenerator nu a x y) = 0

/-- Network loss probability under a stationary strategy (PASTA). Kelly (1991), p.361.
The normalization is the number of edges because all offered rates equal ν. -/
noncomputable def repackLoss {K C : ℕ}
    (a : RepackState K C → KellyLossNetworks.Routing.Edge K → ℝ)
    (pi : RepackState K C → ℝ) : ℝ :=
  (∑ x, pi x * ∑ e, (1 - a x e)) / Fintype.card (KellyLossNetworks.Routing.Edge K)

/-- The minimum loss over all nonanticipating stationary strategies, as in p.361.
**Formalization Note.** For ν>0,K≥2 the value set is nonempty (reject every call, empty
network) and bounded in [0,1]. The controlled chain has a unique recurrent class: every
state can empty through departures. Thus its stationary distribution is unique. The
infimum expresses the minimal loss; no single-link optimality assertion is assumed. -/
noncomputable def optimalRepackLoss (C : ℕ) (nu : ℝ) (K : ℕ) : ℝ :=
  sInf {l | ∃ (a : RepackState K C → KellyLossNetworks.Routing.Edge K → ℝ)
    (pi : RepackState K C → ℝ), IsRepackPolicy a ∧ RepackStationary nu a pi ∧ l = repackLoss a pi}

/-- The routing aim of the threshold strategy: min(n_e,C) direct calls and only the excess
on two-edge routes, using residual capacity. Kelly (1991), p.360.
This is stricter than the published Routing.Feasible event. -/
def RepackAim {K : ℕ} (C : ℕ) (n : KellyLossNetworks.Routing.Edge K → ℕ) : Prop :=
  ∃ f : KellyLossNetworks.Routing.Edge K → Fin K → ℝ,
    (∀ e k, 0 ≤ f e k) ∧ (∀ e k, k ∈ e.1 → f e k = 0) ∧
    (∀ e, (∑ k, f e k) = max ((n e : ℝ) - C) 0) ∧
    ∀ g, min (n g : ℝ) C + KellyLossNetworks.Routing.detourLoad f g ≤ C

/-- The single-link weights π_(s,α) of (4.51), including the partially admitted boundary
state C+s+1. Kelly (1991), p.360. -/
noncomputable def thresholdWeight (C s : ℕ) (nu alpha : ℝ) (n : ℕ) : ℝ :=
  (if n ≤ C+s then 1 else if n = C+s+1 then alpha else 0) * nu^n / Nat.factorial n

noncomputable def thresholdProb (C s : ℕ) (nu alpha : ℝ) (n : ℕ) : ℝ :=
  thresholdWeight C s nu alpha n /
    (∑ k ∈ Finset.range (C+s+2), thresholdWeight C s nu alpha k)

/-- Single-link G,H and L of (4.51)–(4.52), p.360. Finite sums include every nonzero mass. -/
noncomputable def thresholdExcess (C s : ℕ) (nu alpha : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (C+s+2), thresholdProb C s nu alpha n * max ((n : ℝ)-C) 0
noncomputable def thresholdSpare (C s : ℕ) (nu alpha : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (C+s+2), thresholdProb C s nu alpha n * max ((C : ℝ)-n) 0
noncomputable def thresholdLoss (C s : ℕ) (nu alpha : ℝ) : ℝ :=
  1 - (∑ n ∈ Finset.range (C+s+2), thresholdProb C s nu alpha n * n) / nu

/-- The extended supremum s̄+ᾱ in (4.52), including the unbounded case (p.361).
The strict inequality is H>2G, as printed in (4.52). -/
noncomputable def thresholdHeight (C : ℕ) (nu : ℝ) : ℝ≥0∞ :=
  ⨆ (s : ℕ) (alpha : ℝ) (_ : 0 ≤ alpha ∧ alpha < 1 ∧
    thresholdSpare C s nu alpha > 2 * thresholdExcess C s nu alpha),
      ENNReal.ofReal ((s : ℝ) + alpha)

/-- Canonical finite threshold pair, with 0≤ᾱ<1; for an infinite supremum use the
unbounded threshold and L̄=0. Kelly (1991), (4.52) and p.361. This also covers ν=ν*.
**Formalization Note.** No arbitrary real default for an unbounded supremum. -/
noncomputable def thresholdS (C : ℕ) (nu : ℝ) : ℕ := ⌊(thresholdHeight C nu).toReal⌋₊
noncomputable def thresholdAlpha (C : ℕ) (nu : ℝ) : ℝ :=
  (thresholdHeight C nu).toReal - thresholdS C nu
noncomputable def lowerRepackLoss (C : ℕ) (nu : ℝ) : ℝ :=
  if thresholdHeight C nu = ⊤ then 0
  else thresholdLoss C (thresholdS C nu) nu (thresholdAlpha C nu)

/-- The unbounded single-link threshold has the untruncated Poisson law. Kelly (1991),
p.361, H_ν(∞,0) and G_ν(∞,0). The supremum definition also decides ν=ν*. -/
noncomputable def unboundedThresholdProb (nu : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-nu) * nu^n / Nat.factorial n

/-- The canonical single-link distribution, with an explicit unbounded case. -/
noncomputable def canonicalThresholdProb (C : ℕ) (nu : ℝ) (n : ℕ) : ℝ :=
  if thresholdHeight C nu = ⊤ then unboundedThresholdProb nu n
  else thresholdProb C (thresholdS C nu) nu (thresholdAlpha C nu) n

/-- Provisional link admission for the canonical pair, extended to admit every call when
s̄=∞. Kelly (1991), p.360 and p.361. -/
noncomputable def provisionalAdmission (C : ℕ) (nu : ℝ) (n : ℕ) : ℝ :=
  if thresholdHeight C nu = ⊤ then 1
  else if n < C + thresholdS C nu then 1
  else if n = C + thresholdS C nu then thresholdAlpha C nu else 0

/-- The network threshold strategy accepts provisionally according to the single-link
rule and actually accepts exactly when its stated routing aim is possible. Kelly (1991),
p.360. A failed routing attempt leaves the network state unchanged. -/
noncomputable def canonicalRepackPolicy (K C : ℕ) (nu : ℝ)
    (x : RepackState K C) (e : KellyLossNetworks.Routing.Edge K) : ℝ :=
  if ∃ y : RepackState K C, RepackBirth x y e ∧ RepackAim C (fun g => (y.1 g).val)
    then provisionalAdmission C nu (x.1 e).val else 0

/-- Stationary loss of the specified threshold policy; the finite chain has a unique
stationary distribution. Kelly (1991), Theorem 4.53, p.361. -/
noncomputable def canonicalRepackLoss (C : ℕ) (nu : ℝ) (K : ℕ) : ℝ :=
  sInf {l | ∃ pi, RepackStationary nu (canonicalRepackPolicy K C nu) pi ∧
    l = repackLoss (canonicalRepackPolicy K C nu) pi}

end KellyLossNetworks.RevisedDual.Supplement


