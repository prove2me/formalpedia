-- Prove2me | Definitions.Def_RobustShattering_Supermartingale_Shatterable
-- name    : RobustShattering_Supermartingale_Shatterable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:42:52.499558+00:00
-- url     : https://prove2.me/theorems/18da2592-c99d-4699-935f-014d37313a20
-- title:
--   Definition 4.7 — (c, X, Y)-shatterable processes: independent per-node per-step randomness, post-shattering set, local supermartingale cost functions
-- statement:
--   **Process model (§4.2).** A process runs on a finite graph $G=(V,E)$ in $T$ sequential steps $1,\dots,T$. For every node $u\in V$ and step $i\in[T]$ there is an independent (possibly trivial) source of randomness $R_i(u)$, taking values in a probability space $(\Omega_{u,i},\mu_{u,i})$. Write $R_{\le i}$ for all randomness of all nodes in steps $1,\dots,i$, and $R_i(S)=(R_i(u))_{u\in S}$. The process produces a **post-shattering set** $B\subseteq V$, which may be an arbitrary function of all the randomness $R_{\le T}$: no measurability, locality or independence of the events $[v\in B]$ is assumed.
--
--   **Cost functions.** For $v\in V$ and $i\in\{0,\dots,T\}$ a cost function $\gamma_{v,i}(R_{\le i-1},R_i(B^c(v)))\in\mathbb R_{\ge 0}$ may depend on all randomness of all nodes in steps $1,\dots,i-1$, and on the step-$i$ randomness of the nodes in the $c$-ball $B^c(v)=\{u:\mathrm{dist}_G(u,v)\le c\}$ only; it does not depend on anything later. For $i=0$ both arguments are empty, so $\gamma_{v,0}$ is a constant.
--
--   **Definition 4.7.** Let $X\in\mathbb R_{\ge 0}$, $Y\in\mathbb R_{>0}$ and $c\in\mathbb N$. The process is **$(c,X,Y)$-shatterable** if there are cost functions $\gamma_{v,i}$ ($v\in V$, $i\in\{0,\dots,T\}$) with
--   - *low initial cost:* $\gamma_{v,0}\le X$;
--   - *local supermartingale:* for every $i\in\{0,\dots,T-1\}$ and every fixed $R_{\le i}$,
--   $$\mathop{\mathbb E}_{R_{i+1}}\big[\gamma_{v,i+1}(R_{\le i},R_{i+1}(B^c(v)))\big]\le\gamma_{v,i}(R_{\le i-1},R_i(B^c(v)));$$
--   - *high post-shattering cost:* if $v\in B$ then $\gamma_{v,T}(R_{\le T-1},R_T(B^c(v)))\ge Y$.
--
--   **Formalization Note.** `Randomness Ω` is `∀ k : Fin T, ∀ u : V, Ω u k`: Lean step `k` (0-based) is the paper's step `k+1`. `processMeasure μ` is the product of all the probability measures `μ u k` (a product over steps of products over nodes), i.e. all sources are independent. A cost family is `γ : V → ℕ → Randomness Ω → ℝ≥0`; only `i ≤ T` is constrained. Locality (`CostLocal`) says: if $\omega,\omega'$ agree on every coordinate $(k,u)$ with $k+1<i$, and on every $(k,u)$ with $k+1=i$ and $u\in B^c(v)$, then $\gamma_{v,i}(\omega)=\gamma_{v,i}(\omega')$; for $i=0$ this forces $\gamma_{v,0}$ to be constant. Each $\gamma_{v,i}$ ($i\le T$) is measurable, the standing convention behind the paper's expectations. The local supermartingale property is pointwise in the history: for every $\omega$, the lower Lebesgue integral $\int^-$ of $\gamma_{v,i+1}$ over fresh step-$(i+1)$ randomness of all nodes (the coordinates of Lean step $i$ replaced by $\eta\sim\prod_u\mu_{u,i}$, all others kept) is at most $\gamma_{v,i}(\omega)$; no Bochner integral is used, so the condition never holds through a junk value. `IsShatteringCost` names the five properties of a given family $\gamma$, and `Shatterable` asserts that one exists. $B$ is an arbitrary function `Randomness Ω → Set V`. The domain $Y>0$ is a hypothesis of every theorem that uses the definition.
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 14, §4.2 (process model, cost functions); p. 15, Definition 4.7

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace RobustShattering.Supermartingale

/-!
# T-step processes with independent per-node randomness, and (c, X, Y)-shatterable processes

Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, *Robust Shattering Arguments*,
arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 14 (§4.2, the process model and
the cost functions γ_{v,i}) and p. 15, Definition 4.7.

Conventions.
* The graph is `G : SimpleGraph V` on a finite vertex type `V`.
* For each node `u` and each step there is an independent source of randomness: a probability
  space `(Ω u k, μ u k)`. Steps are indexed by `k : Fin T`, so Lean step `k` is the paper's
  step `k + 1` (the paper's steps are `1, …, T`). An empty source of randomness is a one-point
  probability space.
* The full randomness is `ω : Randomness Ω`, with `ω k u` the randomness of node `u` in Lean
  step `k`. Its law is `processMeasure μ`, the product of all the `μ u k` (step by step, each step
  the product over all nodes).
* Cost functions are `γ v i : Randomness Ω → ℝ≥0` for `i ∈ {0, …, T}` (values for `i > T` are
  never used). The paper's `γ_{v,i}(R_{≤ i-1}, R_i(B^c(v)))` reads all randomness of the paper's
  steps `≤ i - 1` and the paper's step-`i` randomness of the nodes in the `c`-ball `B^c(v)`;
  this is encoded as: `γ v i ω` depends only on the coordinates `ω k u` with `k + 1 < i`, or with
  `k + 1 = i` and `u ∈ B^c(v)`. For `i = 0` there are no such coordinates, so `γ v 0` is constant.
* Expectations are lower Lebesgue integrals `∫⁻` of the `ℝ≥0∞`-coerced costs, each cost being
  measurable.
* The post-shattering set `B : Randomness Ω → Set V` is an arbitrary function of all the
  randomness: no measurability and no independence is assumed.
-/

variable {V : Type} {T : ℕ}

/-- The full randomness of a `T`-step process: `ω k u` is the randomness `R_{k+1}(u)` of node `u`
in the paper's step `k + 1`. -/
abbrev Randomness (Ω : V → Fin T → Type) : Type :=
  ∀ k : Fin T, ∀ u : V, Ω u k

/-- The joint law of all the randomness: the product over steps of the product over nodes of the
probability measures `μ u k` (all sources independent). -/
def processMeasure [Fintype V] {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)] :
    Measure (Randomness Ω) :=
  Measure.pi (fun k : Fin T => Measure.pi (fun u : V => μ u k))

/-- Locality of the cost function `f = γ_{v,i}`: if `ω` and `ω'` agree on all randomness of the
paper's steps `1, …, i - 1` (Lean steps `k` with `k + 1 < i`) and on the paper's step-`i`
randomness (Lean step `k` with `k + 1 = i`) of every node of the `c`-ball `B^c(v)`, then
`f ω = f ω'`. -/
def CostLocal (G : SimpleGraph V) (c : ℕ) {Ω : V → Fin T → Type} (v : V) (i : ℕ)
    (f : Randomness Ω → ℝ≥0) : Prop :=
  ∀ ω ω' : Randomness Ω,
    (∀ (k : Fin T) (u : V),
        (k.val + 1 < i ∨ (k.val + 1 = i ∧ u ∈ LocalLLL.Main.ball G v c)) → ω k u = ω' k u) →
      f ω = f ω'

/-- The family `γ v i` (`v ∈ V`, `i ∈ {0, …, T}`) witnesses that the process with randomness
`(Ω, μ)` and post-shattering set `B` is `(c, X, Y)`-shatterable (Definition 4.7):
* each `γ v i` is a measurable function of the randomness with the locality of `CostLocal`;
* low initial cost: `γ_{v,0} ≤ X`;
* local supermartingale: for every `i ∈ {0, …, T - 1}` and every fixed history `ω`, the integral
  of `γ_{v,i+1}` over fresh randomness `η` of all nodes in the paper's step `i + 1` (Lean step
  `i`), all other coordinates of `ω` kept, is at most `γ_{v,i}(ω)`;
* high post-shattering cost: if `v ∈ B ω` then `γ_{v,T}(ω) ≥ Y`. -/
structure IsShatteringCost [Fintype V] (G : SimpleGraph V) (c : ℕ) (X Y : ℝ≥0)
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (B : Randomness Ω → Set V) (γ : V → ℕ → Randomness Ω → ℝ≥0) : Prop where
  measurable : ∀ v i, i ≤ T → Measurable (γ v i)
  local_dep : ∀ v i, i ≤ T → CostLocal G c v i (γ v i)
  low_initial_cost : ∀ v ω, γ v 0 ω ≤ X
  local_supermartingale : ∀ (v : V) (i : ℕ) (hi : i < T) (ω : Randomness Ω),
    ∫⁻ η, (γ v (i + 1) (Function.update ω ⟨i, hi⟩ η) : ℝ≥0∞)
        ∂(Measure.pi (fun u : V => μ u ⟨i, hi⟩)) ≤ (γ v i ω : ℝ≥0∞)
  high_post_shattering_cost : ∀ v ω, v ∈ B ω → Y ≤ γ v T ω

/-- Definition 4.7: the process with independent randomness `(Ω u k, μ u k)` (`u ∈ V`,
`k ∈ Fin T`) and post-shattering set `B` is `(c, X, Y)`-shatterable if some family of cost
functions `γ` satisfies `IsShatteringCost`. -/
def Shatterable [Fintype V] (G : SimpleGraph V) (c : ℕ) (X Y : ℝ≥0)
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (B : Randomness Ω → Set V) : Prop :=
  ∃ γ : V → ℕ → Randomness Ω → ℝ≥0, IsShatteringCost G c X Y μ B γ

end RobustShattering.Supermartingale


