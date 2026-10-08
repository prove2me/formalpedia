-- Prove2me | Definitions.Def_KellyLossNetworks_Routing_Model
-- name    : KellyLossNetworks_Routing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:55:26.486992+00:00
-- url     : https://prove2.me/theorems/f4ddaa0b-8e7e-4934-935a-be1925f1ac47
-- title:
--   §4.6 — the complete graph, the routing event, P(K), and the reservation scheme of the proof of Theorem 4.45
-- statement:
--   This file sets up the static routing problem of §4.6 of Kelly's *Loss networks* (1991) and the objects used in the proof of Theorem 4.45.
--
--   **The network.** The nodes are $\{0,1,\dots,K-1\}$ and every pair of distinct nodes is joined by an edge; there are $\tfrac12 K(K-1)$ edges. Each edge has capacity $C$. The **offered load** between the end points of an edge $e$ is a real number $x_e$.
--
--   **Two-edge routes.** The load of the pair $e=\{a,b\}$ may be carried on its direct edge, or on the two-edge route $a\!-\!k\!-\!b$ through a third (tandem) node $k\notin e$, which occupies both edges $\{a,k\}$ and $\{b,k\}$.
--
--   **The routing event.** The loads $x$ are **feasible** with capacity $C$ if there are flows $f_{e,k}\ge 0$ (the part of the load of the pair $e$ sent through the tandem node $k$, with $f_{e,k}=0$ when $k\in e$) such that $\sum_k f_{e,k}\le x_e$ for every pair $e$, and, for every edge $g$,
--   $$
--   \Big(x_g-\sum_k f_{g,k}\Big)+\sum_{e}\ \sum_{k:\ g\text{ lies on the route of } e \text{ via } k} f_{e,k}\ \le\ C .
--   $$
--   The first term is the part of the load of $g$ carried directly; the second is all two-edge flow passing through $g$. Loads are divisible, so a pair may split its load arbitrarily over its direct edge and all its $K-2$ two-edge routes.
--
--   **The probability $P(K)$.** If the loads on the edges are independent, each with law $\mu$ (the law of a random variable $X$), then $P(K)$ is the probability, under the product measure $\mu^{\otimes \frac12 K(K-1)}$, that the loads are feasible.
--
--   **The reservation scheme.** Write $\mathbb E(X-C)^+=\int (t-C)^+\,\mu(dt)$ and $\mathbb E(C-X)^+=\int (C-t)^+\,\mu(dt)$. For a scale $D>0$ (in the proof, $D=[\mathbb E(C-X)^+]^2-\varepsilon$), the pair $e=\{a,b\}$ reserves through the tandem node $k\notin e$ the flow
--   $$
--   r_{e,k}=\frac{(x_e-C)^+\,(C-x_{ak})^+\,(C-x_{bk})^+}{(K-2)\,D},
--   $$
--   and $r_{e,k}=0$ for $k\in e$. Finally, as functions of a pair $(X_1,X_2)$,
--   $$
--   Y=\frac{(C-X_1)^+(C-X_2)^+}{[\mathbb E(C-X)^+]^2-\varepsilon},\qquad
--   Z=\frac{(X_1-C)^+(C-X_2)^+ + (X_2-C)^+(C-X_1)^+}{[\mathbb E(C-X)^+]^2-\varepsilon},
--   $$
--   and, for $n\ge 1$ independent copies $Y_1,\dots,Y_n$ of $Y$ (respectively $Z_1,\dots,Z_n$ of $Z$), with $(X_1,X_2)$ independent copies of $X$,
--   $$
--   P_1(n)=\mathbb P\Big\{\sum_{i=1}^{n} n^{-1}Y_i<1\Big\},\qquad P_2(n)=\mathbb P\Big\{\sum_{i=1}^{n} n^{-1}Z_i>1\Big\}.
--   $$
--   In the proof of Theorem 4.45, $n=K-2$.
--
--   These objects carry the statement of Theorem 4.45 and of each step of its proof.
--
--   **Formalization Note.** Edges are elements of `Sym2 (Fin K)` that are not loops. "Independent and identically distributed" is the product measure `Measure.pi`; $P(K)$ is the outer measure of the routing event, so no measurability of the event is presupposed. $P_1$ and $P_2$ are realised on $n$ independent copies of the pair $(X_1,X_2)$, i.e. under the product of $n$ copies of $\mu\otimes\mu$. The expectations are Bochner integrals; $K-2$ in $r_{e,k}$ is computed in $\mathbb R$ (it is only used for $K\ge 3$, when some $k\notin e$ exists).
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 358–359, §4.6 (the setting of Theorem 4.45, (4.46), and the proof of Theorem 4.45)

import Mathlib

open MeasureTheory

namespace KellyLossNetworks.Routing

/-- The edges of the complete graph on the `K` nodes `Fin K`: unordered pairs of distinct nodes.
There are `K(K - 1)/2` of them.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, p. 358 ("the offered load between a pair of nodes").

**Formalization Note.** An edge is an element of `Sym2 (Fin K)` that is not a loop. -/
abbrev Edge (K : ℕ) : Type := {e : Sym2 (Fin K) // ¬ e.IsDiag}

/-- `OnDetour e k g`: the edge `g` is one of the two edges of the two-edge route of the pair `e`
through the tandem node `k`. For `e = {a, b}` and a third node `k ∉ e`, the route `a – k – b`
occupies the edges `{a, k}` and `{b, k}`.

Kelly (1991), §4.6, p. 358 ("direct and two-edge routes"). -/
def OnDetour {K : ℕ} (e : Edge K) (k : Fin K) (g : Edge K) : Prop :=
  k ∉ e.1 ∧ ∃ v ∈ e.1, g.1 = s(v, k)

open Classical in
/-- The load that the two-edge flows `f` place on the edge `g`: the sum, over all pairs `e` and
tandem nodes `k` whose route `e` via `k` passes through `g`, of the flow `f e k`. -/
noncomputable def detourLoad {K : ℕ} (f : Edge K → Fin K → ℝ) (g : Edge K) : ℝ :=
  ∑ e, ∑ k, if OnDetour e k g then f e k else 0

/-- **The routing event of Theorem 4.45.** The offered loads `x : Edge K → ℝ` "can be carried over
direct and two-edge routes, with no edge in the network required to carry more than its capacity"
`C`: there are two-edge flows `f e k ≥ 0` (the part of the load of the pair `e` sent through the
tandem node `k`, zero when `k` is an end point of `e`) with `∑ k, f e k ≤ x e`, such that on every
edge `g` the direct part `x g - ∑ k, f g k` of its own load plus all two-edge flow routed through
`g` is at most `C`.

Kelly (1991), §4.6, p. 358.

**Formalization Note.** Loads are divisible: flows are real numbers, and the load of a pair may
be split arbitrarily over its direct edge and its `K - 2` two-edge routes. Every edge's capacity
constraint is imposed, including edges whose own load exceeds `C`. -/
def Feasible {K : ℕ} (C : ℝ) (x : Edge K → ℝ) : Prop :=
  ∃ f : Edge K → Fin K → ℝ,
    (∀ e k, 0 ≤ f e k) ∧ (∀ e k, k ∈ e.1 → f e k = 0) ∧ (∀ e, ∑ k, f e k ≤ x e) ∧
    ∀ g, (x g - ∑ k, f g k) + detourLoad f g ≤ C

/-- **P(K)**: the probability that i.i.d. loads with law `μ` on the `K(K - 1)/2` edges of the
complete graph on `K` nodes are routable in the sense of `Feasible`.

Kelly (1991), §4.6, p. 358.

**Formalization Note.** "Independent and identically distributed" across pairs of nodes is the
product measure `Measure.pi (fun _ : Edge K => μ)`. The value is the (outer) measure of the
routing event; no measurability of the event is presupposed. -/
noncomputable def routingProb (μ : Measure ℝ) (C : ℝ) (K : ℕ) : ENNReal :=
  Measure.pi (fun _ : Edge K => μ) {x | Feasible C x}

/-- `𝔼(X - C)⁺` for `X` with law `μ` (Bochner integral). Kelly (1991), (4.46), p. 358. -/
noncomputable def excessMean (μ : Measure ℝ) (C : ℝ) : ℝ := ∫ t, max (t - C) 0 ∂μ

/-- `𝔼(C - X)⁺` for `X` with law `μ` (Bochner integral). Kelly (1991), (4.46), p. 358. -/
noncomputable def spareMean (μ : Measure ℝ) (C : ℝ) : ℝ := ∫ t, max (C - t) 0 ∂μ

open Classical in
/-- **The reservation of the proof of Theorem 4.45** (p. 359). For loads `x`, a pair `e = {a, b}`
and a tandem node `k ∉ e`, the capacity reserved for `e` through each of the edges `{a, k}`,
`{b, k}` is
`(x_e - C)⁺ (C - x_{ak})⁺ (C - x_{bk})⁺ / ((K - 2) D)`, where `D` is the scale
`[𝔼(C - X)⁺]² - ε` of the paper. It is `0` when `k ∈ e`.

**Formalization Note.** The product `(C - x_{ak})⁺ (C - x_{bk})⁺` is written as the product of
`(C - x_g)⁺` over the edges `g` with `OnDetour e k g`, which are exactly `{a, k}` and `{b, k}`.
`K - 2` is computed in `ℝ`. -/
noncomputable def reserve {K : ℕ} (C D : ℝ) (x : Edge K → ℝ) (e : Edge K) (k : Fin K) : ℝ :=
  if k ∈ e.1 then 0
  else max (x e - C) 0 * (∏ g ∈ Finset.univ.filter (OnDetour e k), max (C - x g) 0) /
    (((K : ℝ) - 2) * D)

/-- The random variable `Y = (C - X₂)⁺ (C - X₃)⁺ / ([𝔼(C - X)⁺]² - ε)` of the proof of
Theorem 4.45 (p. 359), as a function of the pair `(X₂, X₃)`. -/
noncomputable def Yv (μ : Measure ℝ) (C ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  max (C - p.1) 0 * max (C - p.2) 0 / (spareMean μ C ^ 2 - ε)

/-- The random variable
`Z = ((X₁ - C)⁺ (C - X₂)⁺ + (X₂ - C)⁺ (C - X₁)⁺) / ([𝔼(C - X)⁺]² - ε)` of the proof of
Theorem 4.45 (p. 359), as a function of the pair `(X₁, X₂)`. -/
noncomputable def Zv (μ : Measure ℝ) (C ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (max (p.1 - C) 0 * max (C - p.2) 0 + max (p.2 - C) 0 * max (C - p.1) 0) /
    (spareMean μ C ^ 2 - ε)

/-- `P₁` of the proof of Theorem 4.45 (p. 359) with `n = K - 2`:
`ℙ{∑_{i=1}^{n} n⁻¹ Y_i < 1}` for `Y_1, …, Y_n` independent, each distributed as `Y`. The `Y_i`
are realised on `n` independent copies of the pair `(X₂, X₃)`, i.e. under
`Measure.pi (fun _ : Fin n => μ.prod μ)`. -/
noncomputable def P1 (μ : Measure ℝ) (C ε : ℝ) (n : ℕ) : ENNReal :=
  Measure.pi (fun _ : Fin n => μ.prod μ) {w | ∑ i, (n : ℝ)⁻¹ * Yv μ C ε (w i) < 1}

/-- `P₂` of the proof of Theorem 4.45 (p. 359) with `n = K - 2`:
`ℙ{∑_{i=1}^{n} n⁻¹ Z_i > 1}` for `Z_1, …, Z_n` independent, each distributed as `Z`. -/
noncomputable def P2 (μ : Measure ℝ) (C ε : ℝ) (n : ℕ) : ENNReal :=
  Measure.pi (fun _ : Fin n => μ.prod μ) {w | 1 < ∑ i, (n : ℝ)⁻¹ * Zv μ C ε (w i)}

end KellyLossNetworks.Routing


