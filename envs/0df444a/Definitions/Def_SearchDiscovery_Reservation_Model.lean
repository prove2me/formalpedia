-- Prove2me | Definitions.Def_SearchDiscovery_Reservation_Model
-- name    : SearchDiscovery_Reservation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:01.664715+00:00
-- url     : https://prove2.me/theorems/9e6c4bc5-db79-42bf-8da4-89cac51a901e
-- title:
--   §3–§4, (1)–(10), pp. 6–13 — the search and discovery problem: states, actions, policies, payoff, value; Q_s (5), Q_d (9), the three rules of Theorem 1
-- statement:
--   This file sets up the **search and discovery (SD) problem** of Greminger (§3, pp. 6–11) and the quantities in terms of which its optimal policy is stated (§4, pp. 11–13).
--
--   **Primitives.** A model consists of
--
--   1. a probability law $G$ on $\mathbb R$, the law of the partial valuation $X$ of a product;
--   2. a Markov kernel $x\mapsto F_{Y\mid X=x}$, written $\kappa(x)$, the conditional law of the remaining valuation $Y$; the joint law of $(X,Y)$ is $G\otimes\kappa$;
--   3. an inspection cost $c_s$ and a discovery cost $c_d$;
--   4. the number $n_d$ of products revealed by each discovery;
--   5. the belief $q\in[0,1]$ that the next discovery is the last.
--
--   The **standing assumptions** are $c_s>0$, $c_d>0$, $n_d\ge 1$, finite mean and variance of $G$ and of every $F_{Y\mid X=x}$, and a finite unconditional mean of $Y$.
--
--   **States and actions.** An information state lists the purchase values $x_j+y_j$ of the consideration set $C_t$, the partial valuations $x_j$ of the awareness set $S_t$, and whether discovery is still available. The outside option $u_0$ is an entry of the consideration set. The available actions are: buy a product of $C_t$ (which ends search, without cost), inspect a product of $S_t$ (cost $c_s$, which reveals $y_j$ and moves the product to $C_t$ with purchase value $x_j+y_j$), and, while available, discover (cost $c_d$, which adds $n_d$ new products with i.i.d. pairs $(x,y)\sim G\otimes\kappa$ to $S_t$; independently, with probability $q$ this discovery is the last one).
--
--   **Policies, payoff and value.** A policy maps information states to actions. Its payoff on a realisation is the purchase value of the product bought minus all costs paid before (no discounting). A policy is **feasible** from an initial state if, almost surely, it takes available actions and buys after finitely many periods, and its payoff is integrable. Its value $V(\Omega_0,A_0;\pi)$ is the expected payoff, and the optimal value is the supremum over feasible policies, (2).
--
--   **Reservation values.** For a partial valuation $x$ and a hypothetical outside option $z$,
--   $$Q_s(x,c_s,z)=\mathbb E_Y\big[\max\{0,\,x+Y-z\}\big]-c_s,\qquad Y\sim F_{Y\mid X=x},$$
--   which is (5), and
--   $$Q_d(c_d,c_s,z)=\mathbb E_{\boldsymbol X}\Big[V\big(\langle\bar\Omega,\omega(\boldsymbol X,z)\rangle,\{b0,s1,\dots,sn_d\};\tilde\pi\big)\Big]-z-c_d,$$
--   which is (9): $V(\cdots;\tilde\pi)$ is the optimal value of the reduced problem whose only products are an outside option $z$ and $n_d$ products with partial valuations $\boldsymbol X=(X_1,\dots,X_{n_d})$ i.i.d. $G$, with no discovery. A search value $z^s(x)$ is a root of $Q_s(x,c_s,\cdot)$, (6), and a discovery value $z^d$ a root of $Q_d$, (10).
--
--   **The three rules of Theorem 1.** With $\tilde z^b=\max_{k\in C_t}(x_k+y_k)$ and $\tilde z^s=\max_{k\in S_t}z^s(x_k)$ ($-\infty$ if $S_t=\emptyset$), a policy follows the rules if at every information state it buys a product with $z^b_j=\tilde z^b\ge\tilde z^s$, inspects a product with $z^s_j=\tilde z^s\ge\tilde z^b$, or discovers with $z^d\ge\max\{\tilde z^b,\tilde z^s\}$; while discovery is available, buying and inspecting additionally require the chosen value to be at least $z^d$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** `cs`, `cd`, `nd` stand for $c_s,c_d,n_d$; `κ x` for $F_{Y\mid X=x}$; `q` is an element of the unit interval. The finite unconditional mean of $Y$ is footnote 36's "finite mean of X and Y" (per-$x$ moments do not imply it). The belief $q$ is read as an independent Bernoulli($q$) flag drawn with each discovery and observed at once (p. 9: "the consumer always knows whether he can reveal $n_d$ more alternatives"); every discovery reveals exactly $n_d$ products. Policies are deterministic functions of the information state (lists, so order and multiplicity are visible). Feasibility (a.s. purchase, integrable payoff) is what makes "expected total payoff" a real number; a policy failing it has value $-\infty$ or none, since each period costs at least $\min\{c_s,c_d\}>0$. An unavailable action leaves the state unchanged, so the run never buys. The randomness of a run is the sequence of hidden $y$'s of the initial awareness products and, for each discovery batch, its $n_d$ pairs and its flag. `optValue` is a real supremum; it is used only in $Q_d$, on reduced states with finitely many products and no discovery, where the feasible set is nonempty (buy the outside option at once) and bounded above. $\tilde z^s$ is computed in `WithBot ℝ`, and $z^d$ enters the buy and inspect rules only while discovery is available. $z^s$ and $z^d$ are not defined here: theorems take them as hypotheses satisfying (6) and (10).
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, §3 pp. 6–10, (1); §3.1 pp. 10–11, (2)–(4); §4 pp. 11–13, (5), (6), (8), (9), (10), Theorem 1; footnote 36 p. 37

import Mathlib

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

/-- The primitives of the search and discovery problem (§3, pp. 6–9): the law `G` of the partial
valuation `X`, the conditional law `κ x` of `Y` given `X = x` (`F_{Y|X=x}`), the inspection cost
`cs`, the discovery cost `cd`, the number `nd` of products revealed per discovery and the belief
`q ∈ [0,1]` that the next discovery is the last. -/
structure SDModel where
  G : Measure ℝ
  [isProb : IsProbabilityMeasure G]
  κ : Kernel ℝ ℝ
  [markov : IsMarkovKernel κ]
  cs : ℝ
  cd : ℝ
  nd : ℕ
  q : unitInterval

attribute [instance] SDModel.isProb SDModel.markov

/-- The standing assumptions of §3: `c_s > 0`, `c_d > 0` (p. 8), `n_d ≥ 1` (p. 7), finite mean
and variance of `G` and of every `F_{Y|X=x}` (p. 9), and a finite unconditional mean of `Y`
(footnote 36, p. 37). -/
structure SDModel.Standing (M : SDModel) : Prop where
  cs_pos : 0 < M.cs
  cd_pos : 0 < M.cd
  nd_pos : 1 ≤ M.nd
  memLp_G : MemLp id 2 M.G
  memLp_κ : ∀ x, MemLp id 2 (M.κ x)
  integrable_Y : Integrable (fun p : ℝ × ℝ => p.2) (M.G ⊗ₘ M.κ)

/-- The law of the flag "this discovery is the last one": `true` with probability `q`. -/
noncomputable def bernoulliBool (q : unitInterval) : Measure Bool :=
  ENNReal.ofReal (q : ℝ) • Measure.dirac true + ENNReal.ofReal (1 - (q : ℝ)) • Measure.dirac false

instance (q : unitInterval) : IsProbabilityMeasure (bernoulliBool q) := by
  constructor
  simp only [bernoulliBool, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add q.2.1 (by linarith [q.2.2]), add_sub_cancel, ENNReal.ofReal_one]

/-- The information state `Ω_t` together with `A_t` (pp. 7–9): the purchase values `x_j + y_j`
of the consideration set `C_t` (its entries include the outside option `u_0`, action `b0`), the
partial valuations `x_j` of the awareness set `S_t`, and whether discovery `d` is available. -/
structure InfoState where
  C : List ℝ
  S : List ℝ
  disc : Bool

/-- The actions of p. 8: buy the `i`-th product of `C_t`, inspect the `i`-th product of `S_t`,
or discover `n_d` more products. -/
inductive Act
  | buy (i : ℕ)
  | inspect (i : ℕ)
  | discover

/-- `A_t = C_t ∪ S_t ∪ {d}` (p. 8), the last only while discovery is available. -/
def Available (s : InfoState) : Act → Prop
  | .buy i => i < s.C.length
  | .inspect i => i < s.S.length
  | .discover => s.disc = true

/-- The internal state of a run: the information state with the hidden `y` of each awareness
product, the index of the next discovery batch, the costs paid so far, and the purchase value
once a product has been bought. -/
structure RunState where
  C : List ℝ
  S : List (ℝ × ℝ)
  disc : Bool
  batch : ℕ
  cost : ℝ
  bought : Option ℝ

/-- What the consumer observes of a run state. -/
def RunState.info (r : RunState) : InfoState :=
  ⟨r.C, r.S.map Prod.fst, r.disc⟩

namespace SDModel

variable (M : SDModel)

/-- The randomness of a run started from `s₀`: the hidden `y` of the `i`-th initial awareness
product (coordinates beyond `s₀.S.length` are never read), and for every discovery batch `b`
its `n_d` i.i.d. pairs `(x, y)` together with the flag "this discovery is the last". -/
abbrev Ω := (ℕ → ℝ) × (ℕ → (Fin M.nd → ℝ × ℝ) × Bool)

/-- The consumer's belief over the randomness, starting from `s₀`: the `y` of the `i`-th initial
awareness product is drawn from `F_{Y|X=x_i}`, each discovered pair from `G ⊗ F`, each flag from
Bernoulli(`q`), all independent. -/
noncomputable def P (s₀ : InfoState) : Measure M.Ω :=
  (Measure.infinitePi fun i : ℕ => M.κ (s₀.S.getD i 0)).prod
    (Measure.infinitePi fun _ : ℕ =>
      (Measure.pi fun _ : Fin M.nd => M.G ⊗ₘ M.κ).prod (bernoulliBool M.q))

/-- The initial run state of `s₀` under the realisation `ω`. -/
def initRun (s₀ : InfoState) (ω : M.Ω) : RunState :=
  ⟨s₀.C, s₀.S.mapIdx fun i x => (x, ω.1 i), s₀.disc, 0, 0, none⟩

/-- One period. Buying stops search with the product's purchase value; inspecting moves the
product to the consideration set with purchase value `x + y` and costs `c_s`; discovering adds
the next batch's `n_d` products to the awareness set, sets discovery availability according to
the batch's flag, and costs `c_d`. An unavailable action leaves the state unchanged (the run then
never buys). After a purchase the state is frozen. -/
def step (π : InfoState → Act) (ω : M.Ω) (r : RunState) : RunState :=
  match r.bought with
  | some _ => r
  | none =>
    match π r.info with
    | .buy i =>
      if h : i < r.C.length then { r with bought := some r.C[i] } else r
    | .inspect i =>
      if h : i < r.S.length then
        { r with C := r.C ++ [r.S[i].1 + r.S[i].2], S := r.S.eraseIdx i, cost := r.cost + M.cs }
      else r
    | .discover =>
      if r.disc then
        { r with S := r.S ++ List.ofFn (ω.2 r.batch).1, disc := !(ω.2 r.batch).2,
                 batch := r.batch + 1, cost := r.cost + M.cd }
      else r

/-- The state of the run in period `t`. -/
def run (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) (t : ℕ) : RunState :=
  (M.step π ω)^[t] (M.initRun s₀ ω)

open Classical in
/-- The total payoff: the purchase value of the product bought minus all inspection and discovery
costs paid before; `0` on runs that never buy (excluded by `Feasible`). -/
noncomputable def payoff (π : InfoState → Act) (s₀ : InfoState) (ω : M.Ω) : ℝ :=
  if h : ∃ t, (M.run π s₀ ω t).bought.isSome then
    (M.run π s₀ ω (Nat.find h)).bought.getD 0 - (M.run π s₀ ω (Nat.find h)).cost
  else 0

/-- A feasible policy from `s₀` (Π, p. 10): almost surely it takes an available action in every
period before the purchase and buys after finitely many periods, and its payoff is integrable. -/
def Feasible (π : InfoState → Act) (s₀ : InfoState) : Prop :=
  (∀ᵐ ω ∂M.P s₀, ∀ t, (M.run π s₀ ω t).bought = none →
      Available (M.run π s₀ ω t).info (π (M.run π s₀ ω t).info)) ∧
  (∀ᵐ ω ∂M.P s₀, ∃ t, (M.run π s₀ ω t).bought.isSome) ∧
  Integrable (M.payoff π s₀) (M.P s₀)

/-- `V(Ω_0, A_0; π)`: the expected total payoff of `π` from `s₀` (p. 11). -/
noncomputable def value (π : InfoState → Act) (s₀ : InfoState) : ℝ :=
  ∫ ω, M.payoff π s₀ ω ∂M.P s₀

/-- The optimal value `max_{π ∈ Π} V(Ω_0, A_0; π)` of (2). Used only on states without discovery
and with finitely many products, where the set is nonempty and bounded above. -/
noncomputable def optValue (s₀ : InfoState) : ℝ :=
  sSup {v | ∃ π, M.Feasible π s₀ ∧ M.value π s₀ = v}

/-- `Q_s(x, c_s, z) = E_Y[max{0, x + Y − z}] − c_s`, (5), with `Y ∼ F_{Y|X=x}`. -/
noncomputable def Qs (x z : ℝ) : ℝ :=
  ∫ y, max 0 (x + y - z) ∂M.κ x - M.cs

/-- `Q_d(c_d, c_s, z) = E_X[V(⟨Ω̄, ω(X, z)⟩, {b0, s1, …, sn_d}; π̃)] − z − c_d`, (9): the optimal
value of the reduced problem with outside option `z`, the `n_d` newly discovered products with
partial valuations `X = (X_1, …, X_{n_d})` i.i.d. `G`, and no discovery, averaged over `X`. -/
noncomputable def Qd (z : ℝ) : ℝ :=
  ∫ xs, M.optValue ⟨[z], List.ofFn xs, false⟩ ∂(Measure.pi fun _ : Fin M.nd => M.G) - z - M.cd

end SDModel

/-- The search, purchase and discovery rules of Theorem 1 (p. 13) for the action `a` at the
information state `s`, with search values `zs` and discovery value `zd`. Here
`z̃^b = max C` and `z̃^s = max_{k ∈ S} zs x_k` (`⊥ = −∞` when `S` is empty); `z^d` enters only
while discovery is available. -/
def RuleAction (zs : ℝ → ℝ) (zd : ℝ) (s : InfoState) : Act → Prop
  | .buy i => ∃ h : i < s.C.length,
      ((s.C[i] : ℝ) : WithBot ℝ) = s.C.maximum ∧
      (s.S.map zs).maximum ≤ s.C.maximum ∧
      (s.disc = true → ((zd : ℝ) : WithBot ℝ) ≤ s.C.maximum)
  | .inspect i => ∃ h : i < s.S.length,
      ((zs s.S[i] : ℝ) : WithBot ℝ) = (s.S.map zs).maximum ∧
      s.C.maximum ≤ ((zs s.S[i] : ℝ) : WithBot ℝ) ∧
      (s.disc = true → zd ≤ zs s.S[i])
  | .discover => s.disc = true ∧
      s.C.maximum ≤ ((zd : ℝ) : WithBot ℝ) ∧
      (s.S.map zs).maximum ≤ ((zd : ℝ) : WithBot ℝ)

/-- A policy follows the three rules of Theorem 1 at every information state with a nonempty
consideration set. -/
def FollowsRules (zs : ℝ → ℝ) (zd : ℝ) (π : InfoState → Act) : Prop :=
  ∀ s : InfoState, s.C ≠ [] → RuleAction zs zd s (π s)

end SearchDiscovery.Reservation


