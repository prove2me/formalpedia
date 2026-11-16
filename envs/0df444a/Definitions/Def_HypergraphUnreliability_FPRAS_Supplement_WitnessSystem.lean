-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_Supplement_WitnessSystem
-- name    : HypergraphUnreliability_FPRAS_Supplement_WitnessSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:45.213012+00:00
-- url     : https://prove2.me/theorems/febc8698-06cc-41e3-9480-2140ef42cf47
-- title:
--   Finite surviving-witness systems, witness suppression, and the estimator (10.1)
-- statement:
--   Let $S$ be a finite state space and $q(x,y)\ge0$ ($x\ne y$) the off-diagonal jump rates of a continuous-time Markov chain $P$ on $S$, observed until a time $T$. Let $\mathcal W$ be a finite set of $M=|\mathcal W|$ **witnesses**, and let $\mathcal W(x)\subseteq\mathcal W$ be the set of witnesses **alive** at state $x$. Let $\mu$ be an initial distribution on $S$.
--
--   A **finite surviving-witness system** $(q,\mathcal W(\cdot),\mu)$ is **valid** when
--
--   1. every off-diagonal rate is nonnegative (rates are finite reals, hence bounded on the finite set $S$);
--   2. no witness revives: whenever $q(x,y)>0$ with $x\ne y$, $\mathcal W(y)\subseteq\mathcal W(x)$;
--   3. $\mu$ is a probability distribution on $S$;
--   4. every state of positive initial probability has all witnesses alive, $\mathcal W(x)=\mathcal W$.
--
--   A jump $x\to y$ **destroys** $w$ if $w\in\mathcal W(x)$ and $w\notin\mathcal W(y)$. The **suppressed chain** $Q_w$ has rates
--   $$q_w(x,y)=\begin{cases}0,& x\to y\text{ destroys }w,\\ q(x,y),&\text{otherwise,}\end{cases}$$
--   and the **total suppressed rate** is $k_w(x)=\sum_{y\ne x,\ x\to y\text{ destroys }w}q(x,y)$. On a path $X$ of $Q_w$, the **estimator** (10.1) is
--   $$W=\frac{M}{|\mathcal W(X_T)|}\exp\Bigl(-\int_0^T k_w(X_t)\,dt\Bigr),$$
--   set to $0$ if no witness survives at time $T$ (this never happens on a path of $Q_w$ started where all witnesses are alive). The moments $\mathbb E W$ and $\mathbb E W^2$ are taken for $w$ uniform on $\mathcal W$ and $X\sim Q_w$ started from $\mu$:
--   $$\mathbb E W=\frac1M\sum_{w\in\mathcal W}\sum_{x}\mu(x)\,\mathbb E^{x}_{Q_w}[W],\qquad \mathbb E W^2=\frac1M\sum_{w\in\mathcal W}\sum_{x}\mu(x)\,\mathbb E^{x}_{Q_w}[W^2].$$
--   Finally $\mathbb P_P(\mathcal E)=\sum_x\mu(x)\,\mathbb P^x_P(\mathcal W(X_T)\ne\emptyset)$.
--
--   This is the general setting of §10: it adds only the witness data and the initial law to the published finite-state chain interface, with no hypergraph structure.
--
--   **Formalization Note** Path expectations, path integrals $\int_0^T f(X_t)\,dt$ (the last holding interval included) and path validity are those of the published definition `HypergraphUnreliability_FPRAS_JumpChain` (fixed start), mixed over $\mu$. Diagonal rates are ignored through its `jumpRate`. The validity conditions are a separate predicate `IsValid`, used as a hypothesis; no analytic conclusion is assumed.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §10, Theorem 10.1 and (10.1), p. 16

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS.Supplement

/-- A finite surviving-witness system (§10, p. 16): a continuous-time Markov chain on a finite state
space `S` with off-diagonal rates `rate x y`, a finite witness set `𝒲`, the map `alive x ⊆ 𝒲`
recording the surviving witnesses of a state, and an initial distribution `init` on `S`.
The assumptions of Theorem 10.1 are the separate predicate `WitnessSystem.IsValid`. -/
structure WitnessSystem (S : Type) (𝒲 : Type) where
  rate : S → S → ℝ
  alive : S → Finset 𝒲
  init : S → ℝ

namespace WitnessSystem

variable {S 𝒲 : Type} [Fintype S] [Fintype 𝒲]

/-- The standing assumptions of Theorem 10.1: nonnegative (finite, hence bounded) off-diagonal rates;
no witness revives along a positive-rate jump (`alive y ⊆ alive x`); `init` is a probability
distribution on `S`; and every initial state of positive probability has all witnesses alive. -/
def IsValid (sys : WitnessSystem S 𝒲) : Prop :=
  (∀ x y, x ≠ y → 0 ≤ sys.rate x y) ∧
    (∀ x y, 0 < jumpRate sys.rate x y → sys.alive y ⊆ sys.alive x) ∧
    (∀ x, 0 ≤ sys.init x) ∧ (∑ x, sys.init x = 1) ∧
    (∀ x, 0 < sys.init x → sys.alive x = Finset.univ)

/-- The jump `x → y` destroys the witness `w`: `w` is alive at `x` and dead at `y`. -/
def Destroys (sys : WitnessSystem S 𝒲) (w : 𝒲) (x y : S) : Prop :=
  w ∈ sys.alive x ∧ w ∉ sys.alive y

/-- The rates of the suppressed chain `Q_w`: exactly the transitions destroying `w` get rate `0`,
all other rates are those of the original chain. -/
def suppressedRate (sys : WitnessSystem S 𝒲) (w : 𝒲) (x y : S) : ℝ :=
  if sys.Destroys w x y then 0 else sys.rate x y

/-- The total suppressed rate `k_w(x) = Σ_{y ≠ x, x → y destroys w} q(x, y)`. -/
def killRate (sys : WitnessSystem S 𝒲) (w : 𝒲) (x : S) : ℝ :=
  ∑ y, if sys.Destroys w x y then jumpRate sys.rate x y else 0

/-- The expectation of a path functional under a chain with rates `q` started from the initial
distribution `init`, observed to time `T`: the `init`-mixture of the fixed-start expectations. -/
def initExpect (sys : WitnessSystem S 𝒲) (q : S → S → ℝ) (T : ℝ) (F : JumpPath S → ℝ) : ℝ :=
  ∑ x, sys.init x * chainExpect q x T F

/-- The estimator (10.1) for the selected witness `w` on a path `π` of `Q_w`:
`W = M / |𝒲(X_T)| · exp(-∫₀^T k_w(X_t) dt)`, with `M = |𝒲|`. It is set to `0` when no witness
survives at time `T`, which does not happen on a path of `Q_w`. -/
def estimator (sys : WitnessSystem S 𝒲) (T : ℝ) (w : 𝒲) (π : JumpPath S) : ℝ :=
  if (sys.alive π.last).Nonempty then
    (Fintype.card 𝒲 : ℝ) / ((sys.alive π.last).card : ℝ) *
      Real.exp (-JumpPath.pathIntegral (sys.killRate w) T π)
  else 0

/-- `E[W]`: choose `w` uniformly from `𝒲`, run `Q_w` from the initial distribution to time `T`. -/
def estimatorMean (sys : WitnessSystem S 𝒲) (T : ℝ) : ℝ :=
  (Fintype.card 𝒲 : ℝ)⁻¹ * ∑ w, sys.initExpect (sys.suppressedRate w) T (sys.estimator T w)

/-- `E[W²]` under the same sampling scheme. -/
def estimatorSecondMoment (sys : WitnessSystem S 𝒲) (T : ℝ) : ℝ :=
  (Fintype.card 𝒲 : ℝ)⁻¹ *
    ∑ w, sys.initExpect (sys.suppressedRate w) T (fun π => sys.estimator T w π ^ 2)

/-- `P_P(𝓔)`, `𝓔 = {𝒲(X_T) ≠ ∅}`, under the original chain started from the initial distribution. -/
def survivalProb (sys : WitnessSystem S 𝒲) (T : ℝ) : ℝ :=
  sys.initExpect sys.rate T (fun π => if (sys.alive π.last).Nonempty then 1 else 0)

end WitnessSystem

end HypergraphUnreliability.FPRAS.Supplement


