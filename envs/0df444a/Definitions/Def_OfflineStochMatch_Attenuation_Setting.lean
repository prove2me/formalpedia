-- Prove2me | Definitions.Def_OfflineStochMatch_Attenuation_Setting
-- name    : OfflineStochMatch_Attenuation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:28.189017+00:00
-- url     : https://prove2.me/theorems/2028dd76-de1d-404a-ba96-26e2e527beae
-- title:
--   §2–§3.2, pp. 7–9 — LP (3), attenuation functions, effectiveness, Algorithm 1, the events free and safe, β*
-- statement:
--   This file fixes the model of §2–§3.2 of Brubach, Grammel, Ma, MacRury and Srinivasan for the attenuation algorithm.
--
--   **Instance.** A finite graph $G = (V, E)$ (each edge $e$ has two distinct endpoints); each edge $e$ is *active* independently with probability $p_e \in [0,1]$; each vertex $v$ has a *patience* $t_v \in \{1, 2, \dots\} \cup \{\infty\}$, the maximum number of probes that may be made to edges incident to $v$. Write $\delta(v)$ for the set of edges incident to $v$.
--
--   **LP (3).** A vector $(y_e)_{e \in E}$ is *feasible* for LP (3) when, with $z_e = y_e p_e$,
--   $$0 \le y_e \le 1 \ (e \in E), \qquad \sum_{e \in \delta(v)} y_e p_e \le 1, \qquad \sum_{e \in \delta(v)} y_e \le t_v \ (v \in V);$$
--   the last constraint is void when $t_v = \infty$.
--
--   **Attenuation functions (Definitions 3–4).** An attenuation function $\tilde a : [0,1] \to [0,1]$ is *effective* if $\tilde a(0) = 1$ and $z \mapsto \ln(1 - x z \tilde a(z))$ is convex on $[0,1]$ for every $x \in (0,1)$. The attenuation of edge $e$ is $a(e) = \tilde a(p_e y_e)$. Definition 4 lists $\tilde a_{\exp}(z) = e^{-\alpha z}$, $\tilde a_{\mathrm{lin}}(z) = 1 - \alpha z$ and $\tilde a(z) = \frac{1-z}{1 - e^{-(1-z)}}(1 - 1/e)$ (given its limit $1 - 1/e$ at $z = 1$), with a parameter $\alpha$ (the page allows $\alpha \ge 1/2$; only $\alpha = 1/2$ is used). The page asserts all three are effective; this holds for the first two at $\alpha = 1/2$ but fails for the third, for which condition 3 is violated at $z = 0$ when $x$ is close to $1$.
--
--   **Algorithm 1.** Independent coins $Y_e \sim \mathrm{Bernoulli}(y_e)$, $A_e \sim \mathrm{Bernoulli}(a(e))$ and $P_e \sim \mathrm{Bernoulli}(p_e)$ (activeness) are drawn for every edge, and the edges are processed in a uniformly random order. When $e$ is processed it is *free* if both its endpoints are unmatched and have remaining patience (fewer than $t_v$ probes so far). If $e$ is free, $Y_e = 1$ and $A_e = 1$, then $e$ is probed: one probe is counted at each endpoint, and if $P_e = 1$ both endpoints become matched.
--
--   **Safe.** Edge $e = \{u, v\}$ is *safe* if, before $e$ is processed, (1) at most $t_r - 1$ probes were made to edges of $\delta(r)$ for each $r \in \{u, v\}$, and (2) no edge $f \in \delta(u) \cup \delta(v) \setminus \{e\}$ processed before $e$ has $A_f = P_f = Y_f = 1$.
--
--   **Probabilities and $\beta^*$.** $\Pr[e \text{ is free}]$ and $\Pr[e \text{ is safe}]$ are taken over the random order and all coins. Finally
--   $$\beta^* = \int_0^1 \left(e^{-2x} + x e^{-2x}\right)^2 dx \approx 0.38278.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The graph is the platform's `EdmondsMatching65.Polyhedron.Graph` (loopless; it allows parallel edges, and the goal theorem adds that `ends` is injective). Patience is `ℕ∞`, with `⊤` for $\infty$. The paper draws arrival times $\pi(e) \in [0,1]$; they induce exactly a uniform order, so a probability is written as the finite average over the $|E|!$ bijections $E \simeq \{0,\dots,|E|-1\}$ and over the three coin vectors, each weighted by its product of Bernoulli weights. Pr[e is free] is computed from the run of the algorithm (`stateBefore` folds one step per earlier edge), never from a product formula. The coin $P_f$ is drawn for every edge but read only after a probe, which changes no probability. "Before $e$" in item 1 of *safe* counts actual probes; "at most $t_r - 1$" is written $\text{probes}_r + 1 \le t_r$, so no `ℕ∞` subtraction occurs. The printed $X_f$ in item 2 of *safe* is $Y_f$ (no $X$ is defined). The type `ℕ∞` also admits patience $t_v = 0$, which the paper does not consider; statements that need positive patience say so.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, pp. 7–9, §2 (LP (3), Eqs. (3a)–(3d)), §3.1 (Algorithm 1, Definition 3), Definition 4, §3.2 (Eq. (5), the safe event, p. 9)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace OfflineStochMatch.Attenuation



/-- The weight of the outcome `b` of a Bernoulli coin with success probability `q`:
`q` if `b = true`, `1 - q` if `b = false`. -/
def bern (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

/-- The probability weight of a joint outcome `c` of independent Bernoulli coins with success
probabilities `q i`: the product `∏ i, bern (q i) (c i)`. -/
def coinWeight {ι : Type*} [Fintype ι] (q : ι → ℝ) (c : ι → Bool) : ℝ :=
  ∏ i, bern (q i) (c i)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `δ(v)`, the set of edges incident to the vertex `v` (§2, p. 7). -/
def incident (G : EdmondsMatching65.Polyhedron.Graph V E) (v : V) : Finset E :=
  Finset.univ.filter (fun f => v ∈ G.ends f)

/-- Feasibility of `y` for LP (3) (p. 7), with `z_e = y_e p_e` (3d) substituted:
(3c) `0 ≤ y_e ≤ 1`; (3a) `∑_{e ∈ δ(v)} y_e p_e ≤ 1`; (3b) `∑_{e ∈ δ(v)} y_e ≤ t_v`, which
imposes nothing when `t_v = ∞`. -/
def LPFeasible (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞) (y : E → ℝ) : Prop :=
  (∀ e, 0 ≤ y e ∧ y e ≤ 1) ∧
  (∀ v, ∑ e ∈ incident G v, y e * p e ≤ 1) ∧
  (∀ v (n : ℕ), t v = (n : ℕ∞) → ∑ e ∈ incident G v, y e ≤ (n : ℝ))

/-- The exponential attenuation function `ã_exp(z) = e^{-αz}` (Definition 4, p. 9). -/
noncomputable def expAtt (α z : ℝ) : ℝ := Real.exp (-(α * z))

/-- The linear attenuation function `ã_lin(z) = 1 - αz` (Definition 4, p. 9). -/
def linAtt (α z : ℝ) : ℝ := 1 - α * z

/-- The third function of Definition 4 (p. 9), `ã(z) = (1 - z)/(1 - e^{-(1-z)}) · (1 - 1/e)`,
given its limiting value `1 - 1/e` at `z = 1`, where the printed formula is `0/0`. -/
noncomputable def thirdAtt (z : ℝ) : ℝ :=
  if z = 1 then 1 - Real.exp (-1)
  else (1 - z) / (1 - Real.exp (-(1 - z))) * (1 - Real.exp (-1))

/-- An attenuation function `ã : [0,1] → [0,1]` is *effective* (Definition 3, p. 8, with the
range `[0,1]` of p. 9): `ã(0) = 1`, and `z ↦ ln(1 - x z ã(z))` is convex on `[0,1]` for every
`x ∈ (0,1)`. Condition 1 of Definition 3 (`a(e)` is a function `ã(z_e)` of `z_e = p_e y_e`) is
built into `attProb`. -/
def IsEffective (aT : ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1) ∧ aT 0 = 1 ∧
  ∀ x ∈ Set.Ioo (0 : ℝ) 1,
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun z => Real.log (1 - x * z * aT z))

/-- The attenuation probabilities `a(e) = ã(p_e y_e)` (p. 9). -/
def attProb (aT : ℝ → ℝ) (p y : E → ℝ) : E → ℝ := fun f => aT (p f * y f)

/-- The state of a run of Algorithm 1: the set of matched vertices and, for each vertex, the number
of probes made so far to edges incident to it. -/
structure RunState (V : Type) where
  /-- the vertices already matched -/
  matched : Finset V
  /-- the number of probes made so far to edges incident to each vertex -/
  probes : V → ℕ

/-- The initial state: nothing matched, no probes made. -/
def initState : RunState V := ⟨∅, fun _ => 0⟩

/-- In state `st`, the edge `f` is *free* (p. 8): both its endpoints are unmatched and have
remaining patience (fewer than `t_v` probes so far). -/
def CanProbe (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (st : RunState V) (f : E) : Prop :=
  ∀ v, v ∈ G.ends f → v ∉ st.matched ∧ ((st.probes v : ℕ∞) < t v)

open Classical in
/-- One step of Algorithm 1 (p. 8) at edge `f`, given the coins `Y`, `A` (decision) and `P`
(activeness): if `f` is free, `Y_f = 1` and `A_f = 1`, then `f` is probed (one probe is added at each
endpoint), and if moreover `P_f = 1` both endpoints become matched. Otherwise nothing changes. -/
noncomputable def step (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (Y A P : E → Bool) (st : RunState V)
    (f : E) : RunState V :=
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

/-- "`e` is free" when Algorithm 1 processes it (p. 8). -/
def IsFree (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool)
    (e : E) : Prop :=
  CanProbe G t (stateBefore G t σ Y A P e) e

/-- "`e` is probed" by Algorithm 1: `e` is free, `Y_e = 1` and `A_e = 1` (p. 8). -/
def IsProbed (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool)
    (e : E) : Prop :=
  IsFree G t σ Y A P e ∧ Y e = true ∧ A e = true

/-- "`e` is safe" (p. 9): before `e` is processed,
1. at most `t_r - 1` probes were made to edges of `δ(r)`, for each endpoint `r` of `e`
   (written `probes r + 1 ≤ t_r`);
2. no edge `f ≠ e` sharing an endpoint with `e` and preceding `e` in the order has
   `A_f = P_f = Y_f = 1`. -/
def IsSafe (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E)) (Y A P : E → Bool)
    (e : E) : Prop :=
  (∀ r, r ∈ G.ends e → ((stateBefore G t σ Y A P e).probes r : ℕ∞) + 1 ≤ t r) ∧
  ∀ f, f ≠ e → (∃ r, r ∈ G.ends e ∧ r ∈ G.ends f) → σ f < σ e →
    ¬ (A f = true ∧ P f = true ∧ Y f = true)

open Classical in
/-- The probability of an event of the run of Algorithm 1: the average over the uniformly random
order `σ` of the edges, and over the independent coins `Y_f ~ Bernoulli(y_f)`,
`A_f ~ Bernoulli(a_f)`, `P_f ~ Bernoulli(p_f)`, of the indicator of the event. -/
noncomputable def prob (p y a : E → ℝ)
    (ev : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop) : ℝ :=
  (1 / ((Fintype.card E).factorial : ℝ)) *
    ∑ σ : E ≃ Fin (Fintype.card E), ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
      coinWeight y Y * coinWeight a A * coinWeight p P * (if ev σ Y A P then 1 else 0)

/-- `Pr[e is free]` when Algorithm 1 runs on `G` with LP solution `y` and attenuation `ã`. -/
noncomputable def probFree (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞) (y : E → ℝ)
    (aT : ℝ → ℝ) (e : E) : ℝ :=
  prob p y (attProb aT p y) (fun σ Y A P => IsFree G t σ Y A P e)

/-- `Pr[e is safe]` when Algorithm 1 runs on `G` with LP solution `y` and attenuation `ã`. -/
noncomputable def probSafe (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞) (y : E → ℝ)
    (aT : ℝ → ℝ) (e : E) : ℝ :=
  prob p y (attProb aT p y) (fun σ Y A P => IsSafe G t σ Y A P e)

/-- `β* = ∫₀¹ (e^{-2x} + x e^{-2x})² dx ≈ 0.38278` (5), p. 9. -/
noncomputable def betaStar : ℝ :=
  ∫ x in (0 : ℝ)..1, (Real.exp (-2 * x) + x * Real.exp (-2 * x)) ^ 2

end OfflineStochMatch.Attenuation


