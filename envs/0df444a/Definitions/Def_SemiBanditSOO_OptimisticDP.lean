-- Prove2me | Definitions.Def_SemiBanditSOO_OptimisticDP
-- name    : SemiBanditSOO_OptimisticDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:49.850362+00:00
-- url     : https://prove2.me/theorems/114b159b-dd4b-41c6-85ac-3113676fa0ac
-- title:
--   The optimistic DP $\bar g_u$, $\bar h_{(u,v)}$ (3.3)–(3.4), the choice rule (3.5), and the stage gap and variance
-- statement:
--   Let $\mathcal P_1,\dots,\mathcal P_n$ be sets of distributions on the domains. The **optimistic DP** is defined by backward induction: $\bar g_\ell=f_\ell$ at a leaf, and at a non-leaf node
--   $$\bar g_u(x_{\mathrm{obs}(u)})=\max_{v\in\mathcal A_u(x_{\mathrm{obs}(u)})}\bar h_{(u,v)}(x_{\mathrm{obs}(u)}),\qquad (3.3)$$
--   $$\bar h_{(u,v)}(x_{\mathrm{obs}(u)})=\begin{cases}\sup_{Q\in\mathcal P_i}\mathbb E_{X_i\sim Q}[\bar g_v(X_i,x_{\mathrm{obs}(u)})],&\mathrm{obs}(v)\setminus\mathrm{obs}(u)=\{i\},\\ f_v(x_{\mathrm{obs}(u)}),&\mathrm{obs}(v)=\mathrm{obs}(u).\end{cases}\qquad (3.4)$$
--   With $\mathcal P_i=\{D_i\}$ this is the DP (2.1)–(2.2) for known distributions, whose values $g_u$ are the optimal continuation values. The **choice rule** (3.5) chooses at node $u$ a maximizer of $\bar h_{(u,v)}(x_{\mathrm{obs}(u)})$ over $v\in\mathcal A_u(x_{\mathrm{obs}(u)})$, breaking ties in a fixed order.
--
--   For an edge $(u,v)$ revealing $i$, the **stage gap** and **stage variance** are
--   $$d=\sup_{Q\in\mathcal P_i}\mathbb E_{X_i\sim Q}[\bar g_v(X_i,x_{\mathrm{obs}(u)})]-\mathbb E_{X_i\sim D_i}[\bar g_v(X_i,x_{\mathrm{obs}(u)})],\qquad w=\mathrm{Var}_{X_i\sim D_i}\bigl(\bar g_v(X_i,x_{\mathrm{obs}(u)})\bigr),$$
--   and $d=w=0$ on a stopping edge; they are summed along the path that a policy follows. The optimistic DP is **measurable** when every $\bar g_u$ and every $\bar h_{(u,v)}$ on an edge is a measurable function of the observations.
--
--   **Formalization Note.** The DP is defined by well-founded recursion on the height, for an arbitrary family; maxima over the finite feasible sets and suprema over the families are real suprema (bounded, since rewards lie in $[0,1]$). Ties are broken by the least maximizer in a linear order on the nodes.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, (2.1)–(2.2), p.8; (3.3)–(3.5), p.10; proof of Theorem 3.2, pp.24–25 (d_{t,h}, w_{t,h})

import Mathlib
import Definitions.Def_SemiBanditSOO_Model

open MeasureTheory

namespace SemiBanditSOO

namespace Problem

variable {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V)

/-- The value of moving along the edge `u → v`, given the continuation value `gv` at `v`
((2.2), p.8, and (3.4), p.10): for a stopping edge it is the leaf reward `f_v(x_obs(u))`; for an
edge revealing coordinate `i` it is `sup_{Q ∈ 𝒫_i} 𝔼_{X_i ∼ Q}[gv(X_i, x_obs(u))]`.

**Formalization Note.** `(X_i, x_obs(u))` is `Function.update x i X_i`. `sSup` is the real
supremum; it is only used on families of probability measures and on `[0, 1]`-valued functions,
where the set is bounded. -/
noncomputable def edgeValOf (P : ∀ i, Set (ProbabilityMeasure (dom i))) (u v : V)
    (gv : Obs dom → ℝ) (x : Obs dom) : ℝ :=
  match Pb.edgeCoord u v with
  | none => Pb.reward v x
  | some i => sSup ((fun Q : ProbabilityMeasure (dom i) =>
      ∫ z, gv (Function.update x i z) ∂(Q : Measure (dom i))) '' P i)

open Classical in
/-- **The optimistic DP** (3.3)–(3.4), p.10, for an arbitrary family `𝒫 = (𝒫_i)` of sets of
distributions on the domains (as in Assumption 3.1, pp.10–11). Harada, Kawase, Sumita,
*Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback*,
arXiv:2611.02739v1, (3.3)–(3.4), p.10.

`ḡ_ℓ = f_ℓ` at a leaf, and at a non-leaf node
`ḡ_u(x_obs(u)) = max_{v ∈ 𝒜_u(x_obs(u))} h̄_(u,v)(x_obs(u))`, with
`h̄_(u,v) = sup_{Q ∈ 𝒫_i} 𝔼_{X_i∼Q}[ḡ_v(X_i, x_obs(u))]` on an edge revealing `i` and
`h̄_(u,v) = f_v` on a stopping edge. With `𝒫_i = 𝒞_{i,t}` this is the optimistic continuation value
`ḡ^t` of round `t`; with `𝒫_i = {D_i}` it is the DP (2.1)–(2.2) for known distributions.

**Formalization Note.** Defined by well-founded recursion on the height. The maximum over the
finite nonempty set `𝒜_u(x)` is a real `sSup` of a finite set. -/
noncomputable def optVal (P : ∀ i, Set (ProbabilityMeasure (dom i))) (u : V) (x : Obs dom) : ℝ :=
  if Pb.children u = ∅ then Pb.reward u x
  else sSup ((fun v : Pb.children u => Pb.edgeValOf P u v (optVal P v) x) ''
    {v | (v : V) ∈ Pb.feasible u x})
termination_by Pb.height u
decreasing_by exact Pb.height_lt u v v.2

/-- `h̄_(u,v)(x_obs(u))` of (3.4) (and `h_(u,v)` of (2.2) for `𝒫_i = {D_i}`). -/
noncomputable def edgeVal (P : ∀ i, Set (ProbabilityMeasure (dom i))) (u v : V) (x : Obs dom) :
    ℝ :=
  Pb.edgeValOf P u v (Pb.optVal P v) x

/-- **The DP for known distributions** (2.1)–(2.2), p.8: the optimal continuation value `g_u`,
which is the optimistic DP with `𝒫_i = {D_i}`. -/
noncomputable def trueVal (D : ∀ i, ProbabilityMeasure (dom i)) (u : V) (x : Obs dom) : ℝ :=
  Pb.optVal (fun i => {D i}) u x

/-- **Measurability of the optimistic values** (p.10: "we assume that the optimistic values are
measurable … in the observations"): every `ḡ_u` and every `h̄_(u,v)` on an edge is a measurable
function of the observation vector. -/
def MeasurableDP (P : ∀ i, Set (ProbabilityMeasure (dom i))) : Prop :=
  ∀ u, Measurable (Pb.optVal P u) ∧ ∀ v ∈ Pb.children u, Measurable (Pb.edgeVal P u v)

open Classical in
/-- **The choice rule** (3.5), p.10: at node `u` with observations `x`, choose
`v ∈ argmax_{v ∈ 𝒜_u(x)} h̄_(u,v)(x)`, breaking ties in a fixed order (the least maximizer in the
linear order of `V`). -/
noncomputable def greedy [LinearOrder V] (P : ∀ i, Set (ProbabilityMeasure (dom i))) (u : V)
    (x : Obs dom) : V :=
  let S := (Pb.feasible u x).filter fun v => ∀ w ∈ Pb.feasible u x, Pb.edgeVal P u w x ≤ Pb.edgeVal P u v x
  if h : S.Nonempty then S.min' h else u

/-- **The gap of a stage** (proof of Theorem 3.2, p.25): on an edge `u → v` revealing `i`,
`d = sup_{Q ∈ 𝒫_i} 𝔼_{X_i∼Q}[ḡ_v(X_i, x_obs(u))] − 𝔼_{X_i∼D_i}[ḡ_v(X_i, x_obs(u))]`; on a stopping
edge, `d = 0`. -/
noncomputable def stageGap (D : ∀ i, ProbabilityMeasure (dom i))
    (P : ∀ i, Set (ProbabilityMeasure (dom i))) (u v : V) (x : Obs dom) : ℝ :=
  match Pb.edgeCoord u v with
  | none => 0
  | some i => Pb.edgeVal P u v x -
      ∫ z, Pb.optVal P v (Function.update x i z) ∂(D i : Measure (dom i))

/-- **The conditional variance of a stage** (proof of Theorem 3.2, p.25): on an edge `u → v`
revealing `i`, `w = Var_{X_i∼D_i}(ḡ_v(X_i, x_obs(u)))`; on a stopping edge, `w = 0`. -/
noncomputable def stageVar (D : ∀ i, ProbabilityMeasure (dom i))
    (P : ∀ i, Set (ProbabilityMeasure (dom i))) (u v : V) (x : Obs dom) : ℝ :=
  match Pb.edgeCoord u v with
  | none => 0
  | some i => ProbabilityTheory.variance (fun z => Pb.optVal P v (Function.update x i z))
      (D i : Measure (dom i))

open Classical in
/-- The sum of a stage quantity `F u v x` over the edges `(u_h, u_{h+1})` of the path followed by
`σ` on `x` (stages after the leaf contribute `0`, as `d_{t,h} = w_{t,h} = 0` there, p.25). -/
noncomputable def pathSum (σ : V → Obs dom → V) (F : V → V → Obs dom → ℝ) (x : Obs dom) : ℝ :=
  ∑ k ∈ Finset.range (Pb.height Pb.root),
    if Pb.children (Pb.reach σ x k) = ∅ then 0
    else F (Pb.reach σ x k) (Pb.reach σ x (k + 1)) x

end Problem

end SemiBanditSOO


