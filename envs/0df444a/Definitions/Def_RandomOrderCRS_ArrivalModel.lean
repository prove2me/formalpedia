-- Prove2me | Definitions.Def_RandomOrderCRS_ArrivalModel
-- name    : RandomOrderCRS_ArrivalModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:03.898859+00:00
-- url     : https://prove2.me/theorems/dcdd16e6-3209-48df-ac2d-3d330c056ec6
-- title:
--   The arrival-time model, the greedy run and relevant edges
-- statement:
--   For the analysis of Algorithm 2, each edge $e$ of $G=(V,E)$ has an **arrival time** $Y_e$, drawn independently and uniformly from $[0,1]$, and edges arrive in increasing order of arrival times. With $S_e:=X_e\cdot A_e$, each edge **survives** ($S_e=1$) independently with probability $s(x_e)$. The matching $\mathcal M$ is obtained by processing the edges in arrival order and selecting a surviving edge whenever it is not blocked.
--
--   For an edge $e=(u,v)$, let $\partial(e):=\partial(u)\cup\partial(v)\setminus\{e\}$. An edge $f\in\partial(e)$ is **relevant** for $e$ if $Y_f<Y_e$ and $f$ survives; $\mathcal R_e$ denotes the set of edges relevant for $e$.
--
--   **Formalization Note** The sample space is the pair of vectors $(Y,S)$, with the product of uniform laws on $[0,1]$ and the product of $\mathrm{Ber}(s(x_e))$ laws. `arrivalOrder Y` sorts by $Y$; `Tuple.sort` is stable, so ties are broken by a fixed enumeration, and ties have probability 0. Since $\{Y_e=y\}$ is a null event, conditioning on it is expressed by `atTime`: the coordinate $Y_e$ is set to the parameter $y$, and the event is integrated over the other coordinates.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Definition 4, p.16 (arrival times); pp.17–18 (survival, relevant, R_e); §1.1, p.3 (∂(e))

import Mathlib
import Definitions.Def_RandomOrderCRS_Policy
import Definitions.Def_RandomOrderCRS_Attenuation

open MeasureTheory Finset

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The law of the arrival times: "we will treat each edge e as having an arrival time Y_e drawn
independently and uniformly from [0, 1]", arXiv:2209.07520v2, Definition 4, p.16. -/
noncomputable def arrivalTimeLaw (G : SimpleGraph V) [DecidableRel G.Adj] :
    Measure (G.edgeSet → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The Bernoulli law on `Bool` with mean `p`. -/
noncomputable def survivalLaw (p : ℝ) : Measure Bool :=
  p.toNNReal • Measure.dirac true + (1 - p).toNNReal • Measure.dirac false

/-- The sample space of the arrival-time model: arrival times `Y` and survival states `S`. -/
abbrev Sample (G : SimpleGraph V) : Type := (G.edgeSet → ℝ) × (G.edgeSet → Bool)

/-- The joint law of `(Y, S)` in Algorithm 2 run with attenuation function `a`: the `Y_e` are
independent uniform on `[0, 1]`, and "each edge e survives independently with probability
s(x_e) := x_e a(x_e)", arXiv:2209.07520v2, pp.16–17.

**Formalization Note.** `S_e = X_e · A_e` is the survival state itself, and it is independent of
`Y`. `definition_4_order` connects this model with the policy model. -/
noncomputable def arrivalMeasure (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (a : ℝ → ℝ) : Measure (Sample G) :=
  (arrivalTimeLaw G).prod (Measure.pi fun e : G.edgeSet => survivalLaw (survival a (x e)))

/-- The probability of an event of `(Y, S)` under `arrivalMeasure`. -/
noncomputable def arrivalProb (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (a : ℝ → ℝ) (A : (G.edgeSet → ℝ) → (G.edgeSet → Bool) → Prop) : ℝ :=
  (arrivalMeasure G x a).real {ω | A ω.1 ω.2}

/-- The event `A` with `Y_e` fixed to the value `y`: integrating it over the remaining coordinates
is the paper's conditioning on `Y_e = y`.

**Formalization Note.** `{Y_e = y}` is a null event, so `y` is a parameter of the event rather than
a conditioning. Since the `Y_g` are independent, this is the regular conditional probability. -/
def atTime (G : SimpleGraph V) (e : G.edgeSet) (y : ℝ)
    (A : (G.edgeSet → ℝ) → (G.edgeSet → Bool) → Prop) :
    (G.edgeSet → ℝ) → (G.edgeSet → Bool) → Prop :=
  fun Y S => A (Function.update Y e y) S

/-- "Edges then arrive in increasing order of arrival times", arXiv:2209.07520v2, Definition 4,
p.16.

**Formalization Note.** `Tuple.sort` is stable, so ties are broken by a fixed enumeration of the
edges. Ties have probability 0 (`definition_4_order`). -/
noncomputable def arrivalOrder (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ) :
    ArrivalOrder G :=
  (Tuple.sort (Y ∘ (Fintype.equivFin G.edgeSet).symm)).trans (Fintype.equivFin G.edgeSet).symm

open Classical in
/-- One arrival of Algorithm 2 in terms of the survival states: a surviving unblocked edge is
selected. -/
noncomputable def greedyStep (G : SimpleGraph V) (S : G.edgeSet → Bool) (M : Finset G.edgeSet)
    (e : G.edgeSet) : Finset G.edgeSet :=
  if S e = true ∧ ¬ Blocked G M e then insert e M else M

/-- The matching `ℳ` returned by Algorithm 2 (arXiv:2209.07520v2, p.17) on the order `σ` and the
survival states `S`. -/
noncomputable def greedy (G : SimpleGraph V) [DecidableRel G.Adj] (σ : ArrivalOrder G)
    (S : G.edgeSet → Bool) : Finset G.edgeSet :=
  (List.ofFn σ).foldl (greedyStep G S) ∅

/-- `∂(e)`: for `e = (u, v)`, "∂(e) := ∂(u) ∪ ∂(v) \ {e}", arXiv:2209.07520v2, §1.1, p.3.

**Formalization Note.** A finset of edges of `G`: the edges other than `e` that share a vertex
with `e`. -/
noncomputable def edgeNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet) :
    Finset G.edgeSet := by
  classical
  exact univ.filter fun f => f ≠ e ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)

/-- `f` is relevant for `e`: "f ∈ ∂(e) is relevant (for e), provided Y_f < Y_e and f survives",
arXiv:2209.07520v2, pp.17–18. -/
def IsRelevant (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ) (S : G.edgeSet → Bool)
    (e f : G.edgeSet) : Prop :=
  f ∈ edgeNbrs G e ∧ Y f < Y e ∧ S f = true

open Classical in
/-- The set `ℛ_e` of edges relevant for `e`, arXiv:2209.07520v2, p.18. -/
noncomputable def relevantSet (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ)
    (S : G.edgeSet → Bool) (e : G.edgeSet) : Finset G.edgeSet :=
  univ.filter fun f => IsRelevant G Y S e f

end RandomOrderCRS


