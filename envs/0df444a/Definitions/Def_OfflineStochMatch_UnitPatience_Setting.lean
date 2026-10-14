-- Prove2me | Definitions.Def_OfflineStochMatch_UnitPatience_Setting
-- name    : OfflineStochMatch_UnitPatience_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:11:50.155258+00:00
-- url     : https://prove2.me/theorems/2db30d49-690d-4b75-a0ce-3d0783105cc1
-- title:
--   §2 and §4, pp. 6–7, 16–18 — bipartite graph with a unit-patience side, LP (3), the rounding of Gandhi et al. with property (2), probing by weight, W(v), E[ALG]
-- statement:
--   This file sets up the model of §4: offline stochastic matching on a bipartite graph whose side $V_1$ has unit patience, solved by dependent rounding followed by probing each star in decreasing order of weight.
--
--   **Graph and instance.** $G=(V_1\cup V_2,E)$ is a bipartite graph: every edge $e\in E$ joins a vertex of $V_1$ to a vertex of $V_2$. For a vertex $x$, $\delta(x)$ is the set of edges incident to $x$. Each edge has a weight $w_e$ and a probability $p_e$ of being active; each $v\in V_2$ has a patience $t_v\in\mathbb N\cup\{\infty\}$, and every $u\in V_1$ has patience $t_u=1$.
--
--   **LP (3).** A vector $(y_e)_{e\in E}$ is feasible for LP (3), with $z_e=y_ep_e$, when
--   $$0\le y_e\le 1\ \ (e\in E),\qquad \sum_{e\in\delta(x)}y_ep_e\le 1\ \ (x\in V_1\cup V_2),\qquad \sum_{e\in\delta(x)}y_e\le t_x\ \ (x\in V_1\cup V_2),$$
--   where $t_u=1$ on $V_1$ and the patience constraint is void when $t_v=\infty$.
--
--   **Rounding.** The dependent rounding of Gandhi et al. turns $y$ into a random set $\hat E=\{e:Y_e=1\}$ of rounded edges, described by a probability distribution $\mu$ on subsets of $E$. A distribution $\mu$ is admissible for $y$ when
--   1. $\mu\ge 0$ and $\sum_Y\mu(Y)=1$;
--   2. it preserves the marginals: $\Pr[Y_e=1]=y_e$ for every $e$;
--   3. every $u\in V_1$ has at most one rounded edge: $\sum_{e\in\delta(u)}Y_e\le 1$ almost surely;
--   4. every $v\in V_2$ keeps its patience: $\sum_{e\in\delta(v)}Y_e\le t_v$ almost surely;
--   5. it has the negative correlation property (2): for every $v\in V_2$, every $S\subseteq\delta(v)$ and $b\in\{0,1\}$,
--   $$\Pr\Big[\bigcap_{e\in S}(Y_e=b)\Big]\le\prod_{e\in S}\Pr[Y_e=b].$$
--
--   **Probing.** Independently of the rounding, each edge is active with probability $p_e$ (indicator $P_e$, independent coins). An order $\mathrm{ord}(v)$ lists the edges of $\delta(v)$, each once, in decreasing order of weight (ties in any order). In the rounded graph each $v\in V_2$ is the centre of a star; $v$ probes its rounded edges in the order $\mathrm{ord}(v)$ and is matched to the first one that is active. $W(v)$ is the weight of the edge matched at $v$ (and $0$ if none), and
--   $$\mathbb E[\mathsf{ALG}]=\mathbb E\Big[\sum_{v\in V_2}W(v)\Big],\qquad \mathsf{OPT}(v)=\sum_{e\in\delta(v)}w_ez_e.$$
--   For the analysis of Lemma 8 the file also defines, for a sequence $z_1,z_2,\dots$, $F(i)=1-\prod_{j=1}^{i}(1-z_j)$ and $F^*(i)=\sum_{j=1}^{i}z_j$, so that $F(0)=F^*(0)=0$.
--
--   **Formalization Note** All randomness is finite: an expectation is an explicit sum over the rounded set $Y\subseteq E$, weighted by $\mu(Y)$, and over the activeness pattern $P:E\to\{0,1\}$, weighted by $\prod_e p_e^{P_e}(1-p_e)^{1-P_e}$; the two are independent. The rounding of Gandhi et al. is represented by the properties §1.2 and §4 use (marginals, at most one edge at each $u\in V_1$, patience at each $v\in V_2$, property (2) on the rounded indicators $Y$), not by the procedure itself. $W(v)$ is defined from the run (first active edge in the probe list), not by a formula. Parallel edges are allowed. Because each $u\in V_1$ has at most one rounded edge and patience $1$, and each $v$ probes at most $|\hat E\cap\delta(v)|\le t_v$ edges, the stars do not interact and $W(v)$ is exactly the weight the algorithm matches at $v$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 6 (Eq. (2)), p. 7 (LP (3)), p. 16 (§4, description and analysis of the algorithm), pp. 17–18 (F(i), F*(i), OPT(v))

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

/-- A bipartite graph with bipartition `V₁ ∪ V₂` and edge set `E`: every edge `e` joins
`left e ∈ V₁` to `right e ∈ V₂` (parallel edges are allowed). -/
structure BipGraph (V₁ V₂ E : Type) where
  left : E → V₁
  right : E → V₂

variable {V₁ V₂ E : Type}

/-- `δ(u)` for `u ∈ V₁`: the edges incident to `u`. -/
def deltaL [Fintype E] [DecidableEq V₁] (G : BipGraph V₁ V₂ E) (u : V₁) : Finset E :=
  univ.filter (fun e => G.left e = u)

/-- `δ(v)` for `v ∈ V₂`: the edges incident to `v`. -/
def deltaR [Fintype E] [DecidableEq V₂] (G : BipGraph V₁ V₂ E) (v : V₂) : Finset E :=
  univ.filter (fun e => G.right e = v)

/-- Feasibility for LP (3) on a bipartite graph whose side `V₁` has unit patience (`t_u = 1`) and
whose side `V₂` has patience `t : V₂ → ℕ∞` (`⊤` = ∞), with `z_e = y_e p_e` substituted. -/
structure LPFeasible [Fintype E] [DecidableEq V₁] [DecidableEq V₂]
    (G : BipGraph V₁ V₂ E) (p y : E → ℝ) (t : V₂ → ℕ∞) : Prop where
  /-- (3c) -/
  y_mem : ∀ e, 0 ≤ y e ∧ y e ≤ 1
  /-- (3a) at `u ∈ V₁` -/
  match_left : ∀ u, ∑ e ∈ deltaL G u, y e * p e ≤ 1
  /-- (3b) at `u ∈ V₁`, where `t_u = 1` -/
  patience_left : ∀ u, ∑ e ∈ deltaL G u, y e ≤ 1
  /-- (3a) at `v ∈ V₂` -/
  match_right : ∀ v, ∑ e ∈ deltaR G v, y e * p e ≤ 1
  /-- (3b) at `v ∈ V₂`; no constraint when `t v = ⊤` -/
  patience_right : ∀ v (n : ℕ), t v = n → ∑ e ∈ deltaR G v, y e ≤ n

/-- `Pr[∩_{e∈S} (Y_e = b)]` under the rounding distribution `μ` on rounded edge sets
(`Y_e = 1` iff `e ∈ Y`). -/
def PrAll [Fintype E] [DecidableEq E] (μ : Finset E → ℝ) (S : Finset E) (b : Bool) : ℝ :=
  ∑ Y ∈ univ.filter (fun Y : Finset E => ∀ e ∈ S, decide (e ∈ Y) = b), μ Y

/-- The properties of the dependent rounding of Gandhi et al. [25] that §4 uses: `μ` is a
probability distribution on rounded edge sets `Y = {e : Y_e = 1}` that preserves the marginals
`Pr[Y_e = 1] = y_e`, rounds at most one edge at each `u ∈ V₁`, respects the patience of each
`v ∈ V₂`, and has the negative correlation property (2) on the edges at each `v ∈ V₂`. -/
structure IsRounding [Fintype E] [DecidableEq E] [DecidableEq V₁] [DecidableEq V₂]
    (G : BipGraph V₁ V₂ E) (y : E → ℝ) (t : V₂ → ℕ∞) (μ : Finset E → ℝ) : Prop where
  nonneg : ∀ Y, 0 ≤ μ Y
  sum_one : ∑ Y, μ Y = 1
  marginal : ∀ e, ∑ Y ∈ univ.filter (fun Y : Finset E => e ∈ Y), μ Y = y e
  unit_left : ∀ Y, μ Y ≠ 0 → ∀ u, (Y ∩ deltaL G u).card ≤ 1
  patience_right : ∀ Y, μ Y ≠ 0 → ∀ v, (((Y ∩ deltaR G v).card : ℕ) : ℕ∞) ≤ t v
  /-- Property (2): `Pr[∩_{e∈S}(Y_e = b)] ≤ ∏_{e∈S} Pr[Y_e = b]` for `S ⊆ δ(v)`, `b ∈ {0,1}`. -/
  neg_corr : ∀ v (S : Finset E), S ⊆ deltaR G v → ∀ b : Bool,
    PrAll μ S b ≤ ∏ e ∈ S, PrAll μ {e} b

/-- `ord v` lists the edges of `δ(v)`, each once, in decreasing order of weight. -/
def IsWeightOrder [DecidableEq V₂] (G : BipGraph V₁ V₂ E) (w : E → ℝ) (ord : V₂ → List E) :
    Prop :=
  ∀ v, (ord v).Nodup ∧ (∀ e, e ∈ ord v ↔ G.right e = v) ∧
    (ord v).Pairwise (fun e f => w f ≤ w e)

/-- The edges `v` probes when the rounded set is `Y`: those `e ∈ δ(v)` with `Y_e = 1`, in the
order `ord v` (decreasing weight). -/
def probeList [DecidableEq E] (ord : V₂ → List E) (v : V₂) (Y : Finset E) : List E :=
  (ord v).filter (fun e => decide (e ∈ Y))

/-- `W(v)`: the weight of the edge matched at `v` by the algorithm, i.e. of the first active edge
in `v`'s probe list (probing stops when it succeeds), and `0` if no probed edge is active. -/
def W [DecidableEq E] (w : E → ℝ) (ord : V₂ → List E) (v : V₂) (Y : Finset E) (P : E → Bool) :
    ℝ :=
  match (probeList ord v Y).find? (fun e => P e) with
  | some e => w e
  | none => 0

/-- `E[W(v)]`: rounded set `Y ~ μ`, independent activeness coins `P_e ~ Bernoulli(p_e)`. -/
def EW [Fintype E] [DecidableEq E] (w p : E → ℝ) (ord : V₂ → List E) (v : V₂)
    (μ : Finset E → ℝ) : ℝ :=
  ∑ Y, μ Y * ∑ P : E → Bool, OfflineStochMatch.InfinitePatience.coinWeight p P * W w ord v Y P

/-- `E[ALG] = E[Σ_{v∈V₂} W(v)]`. -/
def EALG [Fintype V₂] [Fintype E] [DecidableEq E] (w p : E → ℝ) (ord : V₂ → List E)
    (μ : Finset E → ℝ) : ℝ :=
  ∑ Y, μ Y * ∑ P : E → Bool, OfflineStochMatch.InfinitePatience.coinWeight p P * ∑ v, W w ord v Y P

/-- The indicator `Y_e P_e` (edge `e` is rounded and active). -/
def YP [DecidableEq E] (Y : Finset E) (P : E → Bool) (e : E) : ℝ :=
  if e ∈ Y ∧ P e = true then 1 else 0

/-- `OPT(v) = Σ_{e∈δ(v)} w_e z_e` with `z_e = p_e y_e`. -/
def OPT [Fintype E] [DecidableEq V₂] (G : BipGraph V₁ V₂ E) (w p y : E → ℝ) (v : V₂) : ℝ :=
  ∑ e ∈ deltaR G v, w e * (p e * y e)

/-- `F(i) = 1 − ∏_{j=1}^{i} (1 − z_j)` (1-based indices; `F(0) = 0`). -/
def Fcum (z : ℕ → ℝ) (i : ℕ) : ℝ := 1 - ∏ j ∈ Icc 1 i, (1 - z j)

/-- `F*(i) = Σ_{j=1}^{i} z_j`. -/
def Fstar (z : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ Icc 1 i, z j

end OfflineStochMatch.UnitPatience


