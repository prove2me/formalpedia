-- Prove2me | Definitions.Def_PlanningProphet_FocalAlgorithm
-- name    : PlanningProphet_FocalAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:35.648041+00:00
-- url     : https://prove2.me/theorems/682e1015-63a2-465e-bc7d-b7847a7faa33
-- title:
--   §3.2 — the single-focal-path algorithm with labels: tentative edges, $p(e)$ and $x_e$
-- statement:
--   This module defines the algorithm of §3.2 (pp.9–10) on a graph with an unlabelled $s,t$-path $P$ through all nodes.
--
--   1. **$OPT$'s path and $x_e$.** A measurable selector $\mathrm{sel}$ returns, for each value vector, a feasible $s,t$-path of value $OPT$. Then $x_e=\Pr[e\in \mathrm{sel}(W)]$ is the probability that $OPT$ takes $e$.
--   2. **The seed.** For each node $u$, an independent copy $\omega'_u$ of the sample and an independent uniform coin $c_u\in[0,1]$.
--   3. **The step at node $u$.** The algorithm forms the vector equal to the true values on the edges leaving $u$ and to $W(\omega'_u)$ elsewhere, and lets $OPT(u)$ be its selected path. Because the values are independent across source nodes, this samples $OPT$ conditional on the values of the edges leaving $u$. If $OPT(u)$ uses an edge $e$ leaving $u$, then $e$ is the **tentative** edge. The algorithm takes $e$ when it still has capacity for every label of $e$ and $c_u<q(e)$; in every other case it takes the edge of $P$ leaving $u$.
--   4. **$p(e)$ and the acceptance rule.** For an acceptance rule $q$, $p_q(e)$ is the probability that the algorithm visits $\mathrm{tail}(e)$ and at that point has capacity for every label of $e$. The paper's rule is
--   $$q(e)=\min\Big\{1,\ \frac{1}{(d+2)\,p_q(e)}\Big\}\qquad\text{for every edge } e .$$
--   Since $p_q(e)$ depends on $q$ only at nodes visited before $\mathrm{tail}(e)$, this is the paper's recursive definition along $P$.
--   5. **Selection probability.** The probability that $e$ is marked as tentative and selected is the probability that, when the run is at $\mathrm{tail}(e)$, the tentative edge is $e$ and the next edge of the run is $e$.
--
--   These are the objects of Lemma 2, the core of Theorem 3.
--
--   **Formalization Note** The paper's "$ALG$ takes $e$ with probability $\frac1{d+2}\cdot\frac1{p(e)}$, independently of everything else" is the coin comparison $c_u<q(e)$. The $\min\{1,\cdot\}$ only keeps $q$ a probability; Lemma 2 shows that it never binds. Probabilities are taken under the product of the seed law and $\mu$.
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §3.2 Width 1 Graphs with Edge Labels, pp.9–10: x_e and P p.9, Algorithm pp.9–10

import Mathlib
import Definitions.Def_PlanningProphet_OnlinePolicy

open scoped NNReal ENNReal
open MeasureTheory

namespace PlanningProphet

/-! # The single-focal-path algorithm with labels (arXiv:2406.13911v1, §3.2, pp.9–10)

"For each edge `e` in `E`, let `x_e` be the probability that `OPT` takes edge `e`. Let `P` denote
an unlabeled path that visits all nodes. […] at any node `i`, the algorithm observes the values of
all edges that leave `i`. Then, it samples `OPT` conditional on the given values of the edges that
leave `i`. Call this `OPT(i)`. If `OPT(i)` uses one of the edges that leave `i`, `ALG` tentatively
selects that edge. Otherwise, `ALG` takes the edge in `P` that leaves `i`. Let `e` be the
tentatively selected edge, and denote by `p(e)` the probability that it is feasible to take `e`,
i.e., the probability that `ALG` visits node `i`, and at that point it has available capacity for
each of the labels in `L_e`. Given that `e ∈ OPT(i)` and that it is feasible to take it, `ALG`
takes `e` with probability `1/(d+2) · 1/p(e)`, independently of everything else. Otherwise, `ALG`
takes the next edge in `P`."

**Formalization Note.**
1. `OPT`'s path is `sel w`, for a measurable choice `sel` of a label-feasible `s,t`-path of
   value `OPT` (`IsOptSelector`; the paper fixes no tie-breaking, and Lemma 2 is stated for every
   such choice). `x_e = μ{e ∈ sel W}` (`optProb`). The same `sel` is used for `OPT(i)`.
2. The seed is one independent copy `ω′` of the sample and one uniform coin `c ∈ [0,1]` per node
   (`Seed`, `seedMeasure`). At node `u`, `OPT(u)` is `sel` of the hybrid vector equal to the
   true values on the edges leaving `u` and to `W ω′` elsewhere, i.e. `sel` of that vector. Since the values are independent
   across source nodes, this vector has the law of the values conditional on the values of the
   edges leaving `u`; and it is independent of everything else.
3. The tentative edge is the edge of `OPT(u)` leaving `u`, if any. "The edge in `P` that leaves
   `u`" is `pathEdge P u`. The tentative edge is taken when `ALG` has capacity for its labels and
   the coin satisfies `c < q e`, where `q e` is the acceptance probability; otherwise `pathEdge P u`.
4. The acceptance rule is the paper's when `q e = min 1 (1 / ((d+2) · p_q(e)))` for every edge
   (`IsFocalRule`), where `p_q(e)` (`feasProb`) is the probability, for the algorithm run with `q`,
   that it visits `tail e` and has capacity for every label of `e` at that point. `p_q(e)` depends
   on `q` only at nodes visited before `tail e`, so this is the paper's recursive definition along
   `P`. The `min 1` only makes the rule a probability; Lemma 2 says it never cuts.
5. "`e` is marked as tentative and selected by `ALG`" (`selProb`) is the event that, at the point
   where the run is at `tail e`, the tentative edge is `e` and the run's next edge is `e`. -/

variable {V E L : Type}

namespace Graph

variable (G : Graph V E L)

/-- `sel` is a measurable choice of `OPT`'s path: for every value vector `w`, `sel w` is a
label-feasible `s,t`-path of value `OPT`, and each event `{w | sel w = p}` is measurable. -/
def IsOptSelector [DecidableEq L] (sel : (E → ℝ≥0) → List E) : Prop :=
  (∀ w, G.IsSTPath (sel w) ∧ G.LabelFeasible (sel w) ∧ pathValue w (sel w) = G.opt w) ∧
    ∀ p : List E, MeasurableSet {w : E → ℝ≥0 | sel w = p}

/-- `x_e`: the probability that `OPT` (chosen by `sel`) takes the edge `e` (p.9). -/
noncomputable def optProb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → E → ℝ≥0)
    (sel : (E → ℝ≥0) → List E) (e : E) : ℝ≥0∞ :=
  μ {ω | e ∈ sel (W ω)}

/-- The values seen when sampling `OPT(u)`: `w` on the edges leaving `u`, the copy `W ω′`
elsewhere. -/
noncomputable def hybrid [DecidableEq V] {Ω : Type*} (W : Ω → E → ℝ≥0) (u : V) (ω' : Ω)
    (w : E → ℝ≥0) : E → ℝ≥0 :=
  fun e => if G.tail e = u then w e else W ω' e

/-- The tentative edge at `u`: the edge of `OPT(u) = sel (hybrid …)` that leaves `u`, if any. -/
noncomputable def tentative [DecidableEq V] {Ω : Type*} (sel : (E → ℝ≥0) → List E)
    (W : Ω → E → ℝ≥0) (u : V) (ω' : Ω) (w : E → ℝ≥0) : Option E :=
  (sel (G.hybrid W u ω' w)).find? fun e => decide (G.tail e = u)

/-- The edge of `P` that leaves `u`. -/
def pathEdge [DecidableEq V] (P : List E) (u : V) : Option E :=
  P.find? fun e => decide (G.tail e = u)

/-- After the edges `h`, there is available capacity for each label of `e`. -/
def HasCapacity [DecidableEq L] (h : List E) (e : E) : Prop :=
  ∀ ℓ ∈ G.labels e, G.labelCount h ℓ < G.cap ℓ

/-- The seed of the algorithm: for each node, a copy of the sample and a coin in `[0,1]`. -/
abbrev Seed (V : Type) (Ω : Type*) := V → Ω × unitInterval

/-- The law of the seed: independent copies of `μ` and independent uniform coins. -/
noncomputable def seedMeasure [Fintype V] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Measure (Seed V Ω) :=
  Measure.pi fun _ => μ.prod volume

open Classical in
/-- One step of the algorithm with acceptance rule `q`, after the edges `h`. -/
noncomputable def focalStep [DecidableEq V] [DecidableEq L] {Ω : Type*}
    (sel : (E → ℝ≥0) → List E) (P : List E) (W : Ω → E → ℝ≥0) (q : E → ℝ≥0∞)
    (ξ : Seed V Ω) (w : E → ℝ≥0) (h : List E) : Option E :=
  let u := G.current h
  match G.tentative sel W u (ξ u).1 w with
  | some e =>
    if G.HasCapacity h e ∧ ENNReal.ofReal ((ξ u).2 : ℝ) < q e then some e else G.pathEdge P u
  | none => G.pathEdge P u

/-- The path selected by the algorithm with acceptance rule `q`, seed `ξ` and values `w`. -/
noncomputable def focalPath [Fintype V] [DecidableEq V] [DecidableEq L] {Ω : Type*}
    (sel : (E → ℝ≥0) → List E) (P : List E) (W : Ω → E → ℝ≥0) (q : E → ℝ≥0∞)
    (ξ : Seed V Ω) (w : E → ℝ≥0) : List E :=
  G.runWith (G.focalStep sel P W q ξ w) (Fintype.card V)

/-- `p(e)`: the probability that the algorithm with rule `q` visits `tail e` and at that point
has available capacity for each label of `e`. -/
noncomputable def feasProb [Fintype V] [DecidableEq V] [DecidableEq L] {Ω : Type*}
    [MeasurableSpace Ω] (sel : (E → ℝ≥0) → List E) (P : List E) (W : Ω → E → ℝ≥0)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : E → ℝ≥0∞) (e : E) : ℝ≥0∞ :=
  ((seedMeasure μ).prod μ) {z : Seed V Ω × Ω |
    ∃ h, h <+: G.focalPath sel P W q z.1 (W z.2) ∧ G.current h = G.tail e ∧ G.HasCapacity h e}

/-- The probability that `e` is marked as tentative and selected by the algorithm with rule `q`:
at the point where the run is at `tail e`, the tentative edge is `e` and the next edge is `e`. -/
noncomputable def selProb [Fintype V] [DecidableEq V] [DecidableEq L] {Ω : Type*}
    [MeasurableSpace Ω] (sel : (E → ℝ≥0) → List E) (P : List E) (W : Ω → E → ℝ≥0)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : E → ℝ≥0∞) (e : E) : ℝ≥0∞ :=
  ((seedMeasure μ).prod μ) {z : Seed V Ω × Ω |
    ∃ h, h ++ [e] <+: G.focalPath sel P W q z.1 (W z.2) ∧ G.current h = G.tail e ∧
      G.tentative sel W (G.tail e) (z.1 (G.tail e)).1 (W z.2) = some e}

/-- `q` is the acceptance rule of §3.2: `q e = min 1 (1 / ((d+2) · p_q(e)))` for every edge. -/
def IsFocalRule [Fintype V] [DecidableEq V] [DecidableEq L]
    {Ω : Type*} [MeasurableSpace Ω] (sel : (E → ℝ≥0) → List E) (P : List E) (W : Ω → E → ℝ≥0)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (q : E → ℝ≥0∞) : Prop :=
  ∀ e, q e = min 1 (((d : ℝ≥0∞) + 2) * G.feasProb sel P W μ q e)⁻¹

end Graph

end PlanningProphet


