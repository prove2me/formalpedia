-- Prove2me | Definitions.Def_ProphetMatchingEFGT_EdgeArrival
-- name    : ProphetMatchingEFGT_EdgeArrival
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:35.562418+00:00
-- url     : https://prove2.me/theorems/da60de74-d67d-4c30-b331-8f3daa7341b0
-- title:
--   §3, §5, §B.2 — edge arrival: online policies, their value, ex-ante rules, and OCRSs with independent edge realizations
-- statement:
--   Fix a finite simple graph $G=(V,E)$ and, for every edge $e$, a probability law $F_e$ on $\mathbb R$; the weights $w_e\sim F_e$ are independent (singleton batches).
--
--   1. **Arrival order** (p. 9). The edges arrive one at a time in an arbitrary order $\sigma$: $e_{\sigma(1)},\dots,e_{\sigma(|E|)}$, chosen by an oblivious adversary.
--   2. **Online policy.** A policy has internal randomness $\omega\sim\rho$. When an edge $e$ arrives with weight $w_e$, it decides whether to match $e$ from the earlier edges and their weights (in order), $e$, $w_e$ and $\omega$ only; it never sees $\sigma$ or a future weight. The edge is matched when the policy accepts it and both its ends are unmatched, so the output $I$ is a matching. The **value** of the policy under $\sigma$ is $\mathbb E_{w,\omega}[w(I)]$, with $\omega$ independent of $w$; the **prophet benchmark** is $\mathbb E_w[\max_{M\in\mathcal M}w(M)]$.
--   3. **Ex-ante rules** (§6, p. 18; §B.2, p. 25). An ex-ante rule assigns to every edge a measurable acceptance probability $q_e:\mathbb R\to[0,1]$ whose marginals $x_e=\mathbb E[q_e(w_e)]$ form a point of $\mathcal F_M$. Its value is
--   $$V(q)=\sum_e\mathbb E\big[w_e\,q_e(w_e)\big].$$
--   The paper's ex-ante solution $y\in\mathcal F_M$ corresponds to the threshold rule $q_e(t)=\mathbf 1[t\ge F_e^{-1}(1-y_e)]$, whose value is $\sum_e\mathbb E[w_e\mid w_e\ge F_e^{-1}(1-y_e)]\,y_e$.
--   4. **OCRS for edge arrival** (§5, p. 12). Each edge is realized ($R_e=\{e\}$) independently with probability $x_e$. An OCRS has internal randomness $\omega\sim\rho$; when a realized edge arrives, it decides from the earlier edges with their realization bits (in order), the edge, and $\omega$ whether to select it; it is selected when both its ends are unmatched. It is **$c$-selectable** for $x$ if for every order $\sigma$ and every edge $e$,
--   $$\Pr[e\in I,\ e\in R_e]\ \ge\ c\,x_e,$$
--   the product form of $\Pr[e\in I\mid e\in R_e]\ge c$.
--
--   These are the objects of Theorem 5.3, §B.2 and the mission's goal.
--
--   **Formalization Note** An order is a bijection `Fin |E| ≃ E`. Policies and OCRSs are structures carrying their randomness space; their decision is required to be measurable (jointly in the observed weights and $\omega$ for a policy, in $\omega$ for an OCRS), so that all probabilities are those of measurable events. The weight law is `Measure.pi F`. Realization probabilities are finite sums of $\prod_e(x_e$ or $1-x_e)$.
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §3 p. 9 (edge arrival model), §5 p. 12 (sampling scheme from x), §6 p. 18 and §B.2 p. 25 (ex-ante optimum), Definitions 2.1–2.2 pp. 7–8

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_MatchingModel

open MeasureTheory

namespace ProphetMatchingEFGT

/-! # Edge arrival (§3, p. 9; §5, p. 12; §B.2, p. 25, Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2)

Arrival orders, online policies for the prophet problem with edge arrivals, their expected weight,
the prophet benchmark `E_w[w(OPT(w))]`, ex-ante rules (the benchmark of §B.2), and OCRSs for the
edge-arrival sampling scheme with independent realizations `R_e = {e}` with probability `x_e` (§5).

**Formalization Note.** An arrival order is a bijection `σ : Fin |E| ≃ E`; edge `σ i` arrives at
time `i`. A policy never receives `σ`: at each arrival it sees only the edges that have already
arrived with their weights (in order), the current edge, its weight, and its own randomness `ω`.
The run adds the current edge exactly when the policy accepts it and both its ends are unmatched,
so every run is a matching. The weights are independent across edges (singleton batches), with law
`Measure.pi F`, and `ω ∼ ρ` is independent of the weights. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both ends of `e` are unmatched by the edges of `M`. -/
def endsFree {G : SimpleGraph V} (M : Finset (Edge G)) (e : Edge G) : Prop :=
  ∀ f ∈ M, ∀ v : V, v ∈ (e : Sym2 V) → v ∉ (f : Sym2 V)

/-- An arrival order `σ : e_{σ(1)}, …, e_{σ(|E|)}` of the edges (p. 9), as a bijection from times
`Fin |E|` to edges. -/
abbrev EdgeOrder (G : SimpleGraph V) [DecidableRel G.Adj] : Type _ :=
  Fin (Fintype.card (Edge G)) ≃ Edge G

/-- The list `e_{σ(1)}, …, e_{σ(|E|)}` of all edges in arrival order. -/
def EdgeOrder.toList {G : SimpleGraph V} [DecidableRel G.Adj] (σ : EdgeOrder G) : List (Edge G) :=
  List.ofFn σ

/-- An online policy for the prophet problem with edge arrivals (§3, p. 9). Its internal randomness
`ω ∈ Ω` has law `ρ`. On the arrival of edge `e` with weight `w_e` it decides, from the history (the
earlier edges and their weights, in arrival order), `e`, `w_e` and `ω` alone, whether to match `e`.
For every fixed list of earlier edges and every current edge, the decision is jointly measurable
in the observed weights and `ω`. -/
structure OnlinePolicy (G : SimpleGraph V) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  ρ : Measure Ω
  [isProb : IsProbabilityMeasure ρ]
  decide : List (Edge G × ℝ) → Edge G → ℝ → Ω → Bool
  measurable : ∀ (hist : List (Edge G)) (e : Edge G),
    Measurable (fun p : (Fin hist.length → ℝ) × ℝ × Ω =>
      decide (List.ofFn fun i => (hist.get i, p.1 i)) e p.2.1 p.2.2)

attribute [instance] OnlinePolicy.mΩ OnlinePolicy.isProb

open Classical in
/-- The matching produced by an online policy on the edges `es`, arriving in this order, with
weights `w` and randomness `ω`: the current edge is added exactly when the policy accepts it and
both its ends are still unmatched. -/
noncomputable def OnlinePolicy.runList {G : SimpleGraph V} (P : OnlinePolicy G)
    (es : List (Edge G)) (w : Edge G → ℝ) (ω : P.Ω) : Finset (Edge G) :=
  (es.foldl (fun (st : List (Edge G × ℝ) × Finset (Edge G)) e =>
      (st.1 ++ [(e, w e)],
        if P.decide st.1 e (w e) ω = true ∧ endsFree st.2 e then insert e st.2 else st.2))
    ([], ∅)).2

/-- The matching `I` produced by the policy under the arrival order `σ`. -/
noncomputable def OnlinePolicy.run {G : SimpleGraph V} [DecidableRel G.Adj] (P : OnlinePolicy G)
    (σ : EdgeOrder G) (w : Edge G → ℝ) (ω : P.Ω) : Finset (Edge G) :=
  P.runList σ.toList w ω

/-- `E_{w,I}[w(I)]` for the policy under the order `σ`, with `w ∼ ∏_e F_e` and `ω ∼ ρ`
independent of `w`. -/
noncomputable def algValue {G : SimpleGraph V} [DecidableRel G.Adj] (F : Edge G → Measure ℝ)
    (P : OnlinePolicy G) (σ : EdgeOrder G) : ℝ :=
  ∫ p : (Edge G → ℝ) × P.Ω, weightOf p.1 (P.run σ p.1 p.2) ∂((Measure.pi F).prod P.ρ)

/-- The prophet benchmark `E_w[w(OPT(w))] = E_w[max_{M ∈ 𝓜} w(M)]` with `w ∼ ∏_e F_e`. -/
noncomputable def optValue (G : SimpleGraph V) [DecidableRel G.Adj] (F : Edge G → Measure ℝ) : ℝ :=
  ∫ w, optWeight G w ∂(Measure.pi F)

/-- An ex-ante rule (the benchmark of §6, p. 18 and §B.2, p. 25): for every edge `e` a measurable
acceptance probability `q_e(t) ∈ [0, 1]` as a function of the weight `t = w_e`, whose marginals
`x_e = E[q_e(w_e)]` form a point of `FM`. The paper's ex-ante solution is the threshold rule
`q_e(t) = 1[t ≥ F_e^{-1}(1 - y_e)]` with `y ∈ FM`. -/
structure ExAnteRule (G : SimpleGraph V) [DecidableRel G.Adj] (F : Edge G → Measure ℝ) where
  q : Edge G → ℝ → ℝ
  measurable : ∀ e, Measurable (q e)
  nonneg : ∀ e t, 0 ≤ q e t
  le_one : ∀ e t, q e t ≤ 1
  marginal_mem : InFM G (fun e => ∫ t, q e t ∂(F e))

/-- The marginals `x_e = ∫ q_e dF_e` of an ex-ante rule. -/
noncomputable def ExAnteRule.marginal {G : SimpleGraph V} [DecidableRel G.Adj]
    {F : Edge G → Measure ℝ} (r : ExAnteRule G F) (e : Edge G) : ℝ :=
  ∫ t, r.q e t ∂(F e)

/-- The value `Σ_e E[w_e · q_e(w_e)]` of an ex-ante rule; for the threshold rule of a point `y` it is
`Σ_e E[w_e | w_e ≥ F_e^{-1}(1 - y_e)] · y_e` (p. 18, p. 25). -/
noncomputable def ExAnteRule.value {G : SimpleGraph V} [DecidableRel G.Adj]
    {F : Edge G → Measure ℝ} (r : ExAnteRule G F) : ℝ :=
  ∑ e, ∫ t, t * r.q e t ∂(F e)

/-- An online contention resolution scheme for matchings with edge arrivals (Definition 2.1 with
singleton batches, §5, p. 12). Its internal randomness `ω` has law `ρ`. When edge `e` arrives and is
realized (`e ∈ R_e`), it decides from the history (the earlier edges with their realization bits, in
arrival order), `e` and `ω` alone whether to select `e`; the decision is measurable in `ω`. -/
structure EdgeOCRS (G : SimpleGraph V) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  ρ : Measure Ω
  [isProb : IsProbabilityMeasure ρ]
  select : List (Edge G × Bool) → Edge G → Ω → Bool
  measurable : ∀ hist e, Measurable (select hist e)

attribute [instance] EdgeOCRS.mΩ EdgeOCRS.isProb

open Classical in
/-- The selected matching `I` of an OCRS under the order `σ`, realization `r` (`r e = true` iff
`e ∈ R_e`) and randomness `ω`: an arriving edge is added exactly when it is realized, the scheme
selects it, and both its ends are unmatched. -/
noncomputable def EdgeOCRS.run {G : SimpleGraph V} [DecidableRel G.Adj] (A : EdgeOCRS G)
    (σ : EdgeOrder G) (r : Edge G → Bool) (ω : A.Ω) : Finset (Edge G) :=
  (σ.toList.foldl (fun (st : List (Edge G × Bool) × Finset (Edge G)) e =>
      (st.1 ++ [(e, r e)],
        if r e = true ∧ A.select st.1 e ω = true ∧ endsFree st.2 e then insert e st.2 else st.2))
    ([], ∅)).2

/-- The probability `∏_e (x_e if e ∈ R else 1 - x_e)` of the realization `r` when each `R_e = {e}`
independently with probability `x_e` (§5, p. 12). -/
def realWeight {G : SimpleGraph V} [DecidableRel G.Adj] (x : Edge G → ℝ) (r : Edge G → Bool) : ℝ :=
  ∏ e, if r e then x e else 1 - x e

/-- `Pr[e ∈ I]` (equivalently `Pr[e ∈ I, e ∈ R_e]`) for the OCRS `A` under the order `σ` with
independent realizations of marginals `x`, the realization being independent of `ω`. -/
noncomputable def EdgeOCRS.selectProb {G : SimpleGraph V} [DecidableRel G.Adj] (A : EdgeOCRS G)
    (x : Edge G → ℝ) (σ : EdgeOrder G) (e : Edge G) : ℝ :=
  ∑ r : Edge G → Bool, realWeight x r * A.ρ.real {ω | e ∈ A.run σ r ω}

/-- `A` is a `c`-selectable OCRS for marginals `x` (Definition 2.1 with singleton batches, p. 7,
p. 12): for every arrival order `σ` and every edge `e`, `Pr[e ∈ I, e ∈ R_e] ≥ c · x_e`, the product
form of `Pr[e ∈ I | e ∈ R_e] ≥ c`. -/
def EdgeOCRS.IsSelectable {G : SimpleGraph V} [DecidableRel G.Adj] (A : EdgeOCRS G)
    (x : Edge G → ℝ) (c : ℝ) : Prop :=
  ∀ (σ : EdgeOrder G) (e : Edge G), c * x e ≤ A.selectProb x σ e

end ProphetMatchingEFGT


