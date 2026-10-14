-- Prove2me | Definitions.Def_OfflineStochMatch_InfinitePatience_Setting
-- name    : OfflineStochMatch_InfinitePatience_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:29.974878+00:00
-- url     : https://prove2.me/theorems/13fddc43-f3d7-442b-9685-625aa74ac380
-- title:
--   §2–§3.1, pp. 6–11 — LP (3), attenuation functions, effectiveness, Algorithm 1, Pr[e is free / probed / safe], E₁(r)
-- statement:
--   This file fixes the objects of offline stochastic matching with patience and of the attenuated random-order probing algorithm (Algorithm 1) of Brubach, Grammel, Ma, MacRury and Srinivasan.
--
--   **Instance.** A finite loopless graph $G=(V,E)$ (parallel edges allowed) has, for each edge $e$, a probability $p_e\in[0,1]$ of being *active*, and for each vertex $v$ a *patience* $t_v\in\mathbb N\cup\{\infty\}$: at most $t_v$ edges incident to $v$ may be probed. Write $\delta(v)$ for the set of edges incident to $v$.
--
--   **LP (3).** A vector $(y_e)_{e\in E}$ is *feasible* for LP (3) when
--   $$0\le y_e\le 1\ (e\in E),\qquad \sum_{e\in\delta(v)} y_e p_e\le 1,\qquad \sum_{e\in\delta(v)} y_e\le t_v\quad(v\in V),$$
--   the last constraint being void when $t_v=\infty$.
--
--   **Attenuation functions** (Definition 4). For a parameter $\alpha$ (the page allows $\alpha\ge 1/2$; only $\alpha=1/2$ is used): $\tilde a_{\exp}(z)=e^{-\alpha z}$, $\tilde a_{\rm lin}(z)=1-\alpha z$, and the third function
--   $$\tilde a(z)=\frac{1-z}{1-e^{-(1-z)}}\Bigl(1-\frac1e\Bigr)\quad(z\neq 1),\qquad \tilde a(1)=1-\frac1e .$$
--   A function $\tilde a$ is *effective* (Definition 3) when it maps $[0,1]$ into $[0,1]$, $\tilde a(0)=1$, and for every $x\in(0,1)$ the map $z\mapsto\ln(1-xz\tilde a(z))$ is convex on $[0,1]$. The attenuation of an edge is $a(e)=\tilde a(p_e y_e)$.
--
--   **Algorithm 1.** Draw independent coins $Y_e\sim\mathrm{Bernoulli}(y_e)$, $A_e\sim\mathrm{Bernoulli}(a(e))$ and $P_e\sim\mathrm{Bernoulli}(p_e)$ (the activeness of $e$), and a uniformly random order of $E$, independent of the coins. Process the edges in that order. An edge is *free* when both its endpoints are unmatched and have been probed fewer than their patience. The algorithm probes $e$ when $e$ is free, $Y_e=1$ and $A_e=1$; a probe uses one unit of patience at both endpoints, and if $P_e=1$ both endpoints become matched.
--
--   **Events and probabilities.** $\Pr[e\text{ is free}]$ and $\Pr[e\text{ is probed}]$ are the probabilities of these events of the run. The edge $e=\{u,v\}$ is *safe* when, before $e$ is processed, (1) at most $t_r-1$ probes were made to edges of $\delta(r)$ for each $r\in\{u,v\}$, and (2) every $f\in\delta(u)\cup\delta(v)\setminus\{e\}$ processed before $e$ has $A_fP_fY_f=0$. For an endpoint $r$ of $e$, $E_1(r)=\{f\in\delta(r)\setminus\{e\}: p_f=1\}$. Finally $\beta^*=\int_0^1(e^{-2x}+xe^{-2x})^2\,dx$ (5).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Probabilities are finite averages: $\Pr[\mathcal E]=\frac1{|E|!}\sum_\sigma\sum_{Y,A,P}w_Y w_A w_P\,\mathbf 1[\mathcal E]$ over the orders $\sigma:E\simeq\{0,\dots,|E|-1\}$ and the coin outcomes, with product weights $w_Y=\prod_f y_f^{Y_f}(1-y_f)^{1-Y_f}$ and likewise for $A$, $P$. The paper generates its order from independent uniform arrival times $\pi(e)\in[0,1]$ (p. 8); this induces exactly the uniform order, so the permutation model is Algorithm 1. The run is computed step by step (`stateBefore`), never from a product formula. All coins are drawn for every edge; the algorithm reads $P_e$ only after probing $e$, so this changes no probability. Patience is in `ℕ∞` ($\top=\infty$), and "at most $t_r-1$ probes" is written $n+1\le t_r$ to avoid truncated subtraction. The third attenuation function is given its limit $1-1/e$ at $z=1$, where the printed formula is $0/0$. The graph is the platform's `EdmondsMatching65.Polyhedron.Graph`, which allows parallel edges, a harmless generalization of the paper's graph. The page's $X_f$ in the safe event is $Y_f$. The page (p. 9) asserts that all three functions of Definition 4 are effective; that is true of $\tilde a_{\exp}$ and $\tilde a_{\rm lin}$ at $\alpha=1/2$, but false for the third function (condition 3 fails at $z=0$ for $x$ near $1$), so `IsEffective thirdAtt` is not a claim of this file. `betaStar` is not used by this mission's statements; it is kept so that this file has the same names as the companion mission on Theorem 1.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, pp. 6–11, §2 (LP (3), Eqs. (3a)–(3d)), §3.1 (Algorithm 1, Definitions 3–4), §3.2 (safe event p. 9, Eq. (5), E_b(r) p. 11)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace OfflineStochMatch.InfinitePatience



variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Coins as finite product weights -/

/-- The weight of the outcome `b` of a Bernoulli(`q`) coin: `q` if `b = true`, `1 - q` otherwise. -/
def bern (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

/-- The probability weight of a joint outcome `c` of independent Bernoulli coins with success
probabilities `q i`: the product `∏ i, bern (q i) (c i)`. -/
def coinWeight {ι : Type*} [Fintype ι] (q : ι → ℝ) (c : ι → Bool) : ℝ :=
  ∏ i, bern (q i) (c i)

/-! ### The instance and LP (3), §2, pp. 6–7 -/

/-- `δ(v)`: the set of edges incident to the vertex `v`. -/
def delta (G : EdmondsMatching65.Polyhedron.Graph V E) (v : V) : Finset E := Finset.univ.filter (fun f => v ∈ G.ends f)

/-- Feasibility of `(y_e)_{e ∈ E}` for LP (3) (p. 7), with `z_e = y_e p_e` (3d) substituted:
(3c) `0 ≤ y_e ≤ 1`; (3a) `∑_{e ∈ δ(v)} y_e p_e ≤ 1` for every vertex; (3b) `∑_{e ∈ δ(v)} y_e ≤ t_v`
for every vertex, which imposes nothing when `t_v = ∞`. -/
def LPFeasible (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞) (y : E → ℝ) : Prop :=
  (∀ f, 0 ≤ y f ∧ y f ≤ 1) ∧
  (∀ v, ∑ f ∈ delta G v, y f * p f ≤ 1) ∧
  (∀ v (n : ℕ), t v = n → ∑ f ∈ delta G v, y f ≤ n)

/-! ### Attenuation functions, Definitions 3–4, pp. 8–9 -/

/-- The exponential attenuation function `ã_exp(z) = e^{-α z}` (Definition 4). -/
noncomputable def expAtt (α : ℝ) (z : ℝ) : ℝ := Real.exp (-(α * z))

/-- The linear attenuation function `ã_lin(z) = 1 - α z` (Definition 4). -/
def linAtt (α : ℝ) (z : ℝ) : ℝ := 1 - α * z

/-- The third function of Definition 4, `ã(z) = (1 - z)/(1 - e^{-(1-z)}) · (1 - 1/e)`, given its
limiting value `1 - 1/e` at `z = 1`, where the printed formula is `0/0`. -/
noncomputable def thirdAtt (z : ℝ) : ℝ :=
  if z = 1 then 1 - Real.exp (-1)
  else (1 - z) / (1 - Real.exp (-(1 - z))) * (1 - Real.exp (-1))

/-- An *effective* attenuation function (Definition 3, p. 8), given as a function `ã` of
`z_e = p_e y_e` (condition 1): `ã` maps `[0,1]` into `[0,1]` (p. 9), `ã(0) = 1` (condition 2), and
`z ↦ ln(1 - x z ã(z))` is convex on `[0,1]` for every `x ∈ (0,1)` (condition 3). -/
def IsEffective (aT : ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1) ∧ aT 0 = 1 ∧
  ∀ x ∈ Set.Ioo (0 : ℝ) 1, ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun z => Real.log (1 - x * z * aT z))

/-! ### Algorithm 1, §3.1, p. 8 -/

/-- The state of a run of Algorithm 1: the matched vertices, and the number of probes made so far
to edges at each vertex. -/
structure RunState (V : Type) where
  matched : Finset V
  probes : V → ℕ

/-- The initial state: nothing matched, no probes made. -/
def initState : RunState V := ⟨∅, fun _ => 0⟩

/-- In state `st`, the edge `f` is *free*: both its endpoints are unmatched and have remaining
patience (fewer than `t_v` probes so far). -/
def CanProbe (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (st : RunState V) (f : E) : Prop :=
  ∀ v, v ∈ G.ends f → v ∉ st.matched ∧ ((st.probes v : ℕ∞) < t v)

open Classical in
/-- Algorithm 1 processes the edge `f`: if `f` is free, `Y_f = 1` and `A_f = 1`, it probes `f`
(one more probe at each endpoint), and if moreover `f` is active (`P_f = 1`) both endpoints become
matched; otherwise nothing changes. -/
noncomputable def step (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (Y A P : E → Bool) (st : RunState V) (f : E) :
    RunState V :=
  if CanProbe G t st f ∧ Y f = true ∧ A f = true then
    { matched := if P f = true then st.matched ∪ Finset.univ.filter (fun v => v ∈ G.ends f)
        else st.matched
      probes := fun v => if v ∈ G.ends f then st.probes v + 1 else st.probes v }
  else st

/-- The state of the run of Algorithm 1 just before edge `e` is processed, when the edges are
processed in the order `σ` (edge `f` comes `σ f`-th): `step` folded over the edges `f` with
`σ f < σ e`, in increasing `σ`. -/
noncomputable def stateBefore (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E))
    (Y A P : E → Bool) (e : E) : RunState V :=
  (((List.finRange (Fintype.card E)).filter (fun i => decide (i < σ e))).map σ.symm).foldl
    (step G t Y A P) initState

/-- The event "`e` is free" when Algorithm 1 reaches `e`. -/
def IsFree (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool)
    (e : E) : Prop :=
  CanProbe G t (stateBefore G t σ Y A P e) e

/-- The event "Algorithm 1 probes `e`": `e` is free, `Y_e = 1` and `A_e = 1`. -/
def IsProbed (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool)
    (e : E) : Prop :=
  IsFree G t σ Y A P e ∧ Y e = true ∧ A e = true

/-- The event "`e` is safe" (p. 9): before `e` is processed, (1) at most `t_r - 1` probes were made to
edges of `δ(r)` for each endpoint `r` of `e`, and (2) every edge `f ≠ e` sharing an endpoint with `e`
and processed before `e` has `A_f P_f Y_f = 0` (the page's `X_f` is `Y_f`). -/
def IsSafe (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool)
    (e : E) : Prop :=
  (∀ r, r ∈ G.ends e → ((stateBefore G t σ Y A P e).probes r : ℕ∞) + 1 ≤ t r) ∧
  (∀ f, f ≠ e → (∃ r, r ∈ G.ends e ∧ r ∈ G.ends f) → σ f < σ e →
    ¬ (A f = true ∧ P f = true ∧ Y f = true))

open Classical in
/-- The probability of an event of a run of Algorithm 1: the average over the uniformly random
order `σ` of `E` and over the independent coins `Y_f ~ Bernoulli(y_f)`,
`A_f ~ Bernoulli(ã(p_f y_f))` and `P_f ~ Bernoulli(p_f)`. -/
noncomputable def prob (p y : E → ℝ) (aT : ℝ → ℝ)
    (ev : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop) : ℝ :=
  (1 / ((Fintype.card E).factorial : ℝ)) *
    ∑ σ : E ≃ Fin (Fintype.card E), ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
      coinWeight y Y * coinWeight (fun f => aT (p f * y f)) A * coinWeight p P *
        (if ev σ Y A P then 1 else 0)

/-- `Pr[e is free]` under Algorithm 1. -/
noncomputable def probFree (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞) (y : E → ℝ) (aT : ℝ → ℝ)
    (e : E) : ℝ :=
  prob p y aT (fun σ Y A P => IsFree G t σ Y A P e)

/-- `Pr[Algorithm 1 probes e]`. -/
noncomputable def probProbed (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞) (y : E → ℝ) (aT : ℝ → ℝ)
    (e : E) : ℝ :=
  prob p y aT (fun σ Y A P => IsProbed G t σ Y A P e)

/-- `Pr[e is safe]` under Algorithm 1. -/
noncomputable def probSafe (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞) (y : E → ℝ) (aT : ℝ → ℝ)
    (e : E) : ℝ :=
  prob p y aT (fun σ Y A P => IsSafe G t σ Y A P e)

/-- `E_1(r) = {f ∈ δ(r) \ {e} | p_f = 1}` (p. 11), for an endpoint `r` of the edge `e`. -/
noncomputable def E1 (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (e : E) (r : V) : Finset E :=
  (delta G r).filter (fun f => f ≠ e ∧ p f = 1)

/-- `β* = ∫_0^1 (e^{-2x} + x e^{-2x})^2 dx` (5), p. 9. -/
noncomputable def betaStar : ℝ :=
  ∫ x in (0 : ℝ)..1, (Real.exp (-2 * x) + x * Real.exp (-2 * x)) ^ 2

end OfflineStochMatch.InfinitePatience


