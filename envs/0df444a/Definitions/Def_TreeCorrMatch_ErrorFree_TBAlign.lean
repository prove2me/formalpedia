-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_TBAlign
-- name    : TreeCorrMatch_ErrorFree_TBAlign
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:25:41.992933+00:00
-- url     : https://prove2.me/theorems/70d7132a-b54b-4976-b56d-a71a3f66060e
-- title:
--   TBAlign: parameters (1), the matrix $\hat L$, GreedyMatching, the 5-dangling-tree test and the seeded completion, as an execution relation
-- statement:
--   **Parameters (1).** $d=\lceil(\log n)^{1/3}\rceil$, $\tau=\lceil\max\{\sqrt{\log n},\lambda(1+1/\log\log n)\}\rceil$, $\xi=n^{-11}$, $\theta^*=e^{1/16}n^{(\log\log n)/2}$ (natural logarithms).
--
--   **Step 1.** For ordered pairs of adjacent nodes $(w,u)$ of $G$ and $(\tilde x,\tilde v)$ of $\tilde G$, $\hat L(T_{w\setminus u},\tilde T_{\tilde x\setminus\tilde v})$ is the output of ApproxLR on the two depth-$d$ local trees with cutoff $\tau$ (parameters $\lambda,s,\xi,d$), and $0$ if either local tree is empty. Each such execution uses its own family of independent seeds, independent of the graphs.
--
--   **Step 2.** For $(u,\tilde v)$, the witness graph $W(u,\tilde v)$ is the bipartite graph between $N(u)$ and $\tilde N(\tilde v)$ whose edge $(w,\tilde x)$ has weight $\hat L(T_{w\setminus u},\tilde T_{\tilde x\setminus\tilde v})$, and $M_{TB}(u,\tilde v)=\mathrm{GreedyMatching}(W(u,\tilde v),\theta^*,5)$: starting from the empty matching, the edges are examined in an arbitrary order and an edge is added if it shares no endpoint with an added edge and its weight is **strictly** greater than $\theta^*$; the output is $1$ as soon as the matching has $5$ edges, and $0$ otherwise.
--
--   **Step 3.** $V'=\{u:\exists\tilde v,\ M_{TB}(u,\tilde v)=1\}$, and $\pi'(u)$ is an arbitrary $\tilde v$ with $M_{TB}(u,\tilde v)=1$.
--
--   **Step 4.** Starting from $\hat\pi=\pi'$, repeatedly set $\hat\pi(u)=\tilde v$ for a currently unmatched pair ($u$ unmatched, $\tilde v$ not in the image) maximizing $W(u,\tilde v)=|\{i \text{ matched in }\hat\pi: u\in N(i),\ \tilde v\in\tilde N(\hat\pi(i))\}|$, ties broken arbitrarily, until $\hat\pi$ is defined on all of $[n]$. The output is $(\pi',\hat\pi)$.
--
--   Because of the arbitrary choices (edge orders, Step 3, ties), TBAlign is formalized as a relation: `IsTBPartial … π′` says that $\pi'$ is a possible result of Steps 1–3 for some admissible edge order of every witness graph, and `IsTBOutput … π′ π̂` that $(\pi',\hat\pi)$ is a possible output of Steps 1–4. Statements quantify over **all** possible outputs.
--
--   **Formalization Note** The cutoff $\tau$ is a parameter in $\mathbb N\cup\{\infty\}$ so that the analysis without cutoff ($M^\infty_{TB}$, $W^\infty$) uses the same definitions. A partial map is `Fin n → Option (Fin n)`. ApproxLR receives the ordered trees $r(\ell(T))$: children by increasing vertex index, then a fixed map $r$ that the statements require to preserve unlabeled classes. Seeds are indexed by $((w,u),(\tilde x,\tilde v))$ and the call index of ApproxLR, i.i.d. with law $\mu_0$ (`Measure.infinitePi`).
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 7, §3.1, eqs. (1)–(5) (PDF p. 9); p. 14, Algorithm 1 (PDF p. 16)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_ApproxLR
import Definitions.Def_TreeCorrMatch_ErrorFree_LocalTree

/-!
The global parameters (1), the matrix `L̂` of Step 1, `GreedyMatching`, the matching matrix `M_TB`
of Step 2, and the execution relation of `TBAlign` (Steps 1–4, Algorithm 1), with the cutoff
`τ ∈ ℕ ∪ {∞}` as a parameter.

Cheng, Wang, Ying, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), §3.1, (1)–(5), p. 7;
Algorithm 1, p. 14.
-/

namespace TreeCorrMatch.ErrorFree

open MeasureTheory
open scoped Classical

/-- `d = ⌈(log n)^{1/3}⌉` of (1). -/
noncomputable def dParam (n : ℕ) : ℕ := ⌈Real.log n ^ ((1 : ℝ) / 3)⌉₊

/-- `τ = ⌈max{√(log n), λ(1 + 1/log log n)}⌉` of (1). -/
noncomputable def tauParam (n : ℕ) (lam : ℝ) : ℕ :=
  ⌈max (Real.sqrt (Real.log n)) (lam * (1 + 1 / Real.log (Real.log n)))⌉₊

/-- `ξ = n^{-11}` of (1). -/
noncomputable def xiParam (n : ℕ) : ℝ := (n : ℝ) ^ (-11 : ℝ)

/-- `θ* = e^{1/16} n^{(log log n)/2}` of (1). -/
noncomputable def thetaParam (n : ℕ) : ℝ :=
  Real.exp (1 / 16) * (n : ℝ) ^ (Real.log (Real.log n) / 2)

/-- Seeds of one run of `TBAlign`: the `ApproxLR` execution for the local-tree pair
`(T_{w∖u}, T̃_{x̃∖ṽ})` is indexed by `((w, u), (x̃, ṽ))`, and its `ApproxPer` calls by `SeedIdx`.
Distinct pairs and distinct calls get distinct, independent seeds (Remark 1). -/
abbrev TBIdx (n : ℕ) : Type := (Fin n × Fin n) × (Fin n × Fin n) × SeedIdx

/-- The law of the seeds: i.i.d. with law `μ₀`, independent of the graphs. -/
noncomputable def tbSeedLaw {Ω₀ : Type} [MeasurableSpace Ω₀] (μ₀ : Measure Ω₀) (n : ℕ) :
    Measure (TBIdx n → Ω₀) :=
  Measure.infinitePi fun _ : TBIdx n => μ₀

/-- The entry `L̂(T_{w∖u}, T̃_{x̃∖ṽ})` of Step 1, (2): `ApproxLR` on the two local trees of depth
`d` with cutoff `τ`, fed as the ordered trees `r(ℓ(T))` (children by vertex index, then the fixed
class-preserving map `r`), with the seeds of the pair; `0` if either local tree is empty. -/
noncomputable def lhatEntry {Ω₀ : Type} (App : PermApprox Ω₀) (r : OTree → OTree) (lam s : ℝ)
    {n : ℕ} (τ : ℕ∞) (G G' : SimpleGraph (Fin n)) (ω : TBIdx n → Ω₀) (w u x v : Fin n) : ℝ :=
  match localTree G (some u) w (dParam n) τ, localTree G' (some v) x (dParam n) τ with
  | some T, some T' =>
      approxLR App lam s (xiParam n) (dParam n) (r T) (r T') fun i => ω ((w, u), (x, v), i)
  | _, _ => 0

/-- The greedy matching built by `GreedyMatching` from the edges `es`, examined in list order,
starting from the matching `M`: an edge is added iff the matching has fewer than `k` edges, the
edge's weight is strictly greater than `θ`, and it shares no endpoint with an edge already added. -/
noncomputable def greedyRun {α β : Type} (wt : α × β → ℝ) (θ : ℝ) (k : ℕ) :
    List (α × β) → List (α × β) → List (α × β)
  | M, [] => M
  | M, e :: es =>
    if M.length < k ∧ θ < wt e ∧ ∀ f ∈ M, f.1 ≠ e.1 ∧ f.2 ≠ e.2 then greedyRun wt θ k (M ++ [e]) es
    else greedyRun wt θ k M es

/-- `GreedyMatching(W, θ, k)` with edge order `order`: `true` (output 1) iff the greedy matching
reaches size `k`. -/
noncomputable def greedyMatching {α β : Type} (wt : α × β → ℝ) (θ : ℝ) (k : ℕ)
    (order : List (α × β)) : Bool :=
  decide (k ≤ (greedyRun wt θ k [] order).length)

/-- `order` lists every edge `(w, x̃) ∈ N(u) × Ñ(ṽ)` of the witness graph `W(u, ṽ)` exactly once:
an admissible order for `GreedyMatching`. -/
def IsWitnessOrder {n : ℕ} (G G' : SimpleGraph (Fin n)) (u v : Fin n)
    (order : List (Fin n × Fin n)) : Prop :=
  order.Nodup ∧ ∀ e : Fin n × Fin n, e ∈ order ↔ G.Adj u e.1 ∧ G'.Adj v e.2

/-- The entry `M_TB(u, ṽ) = GreedyMatching(W(u, ṽ), θ*, 5)` of Step 2, (3), with cutoff `τ` and edge
order `order`: the witness graph `W(u, ṽ)` has edge weights `L̂(T_{w∖u}, T̃_{x̃∖ṽ})`. -/
noncomputable def mTB {Ω₀ : Type} (App : PermApprox Ω₀) (r : OTree → OTree) (lam s : ℝ) {n : ℕ}
    (τ : ℕ∞) (G G' : SimpleGraph (Fin n)) (ω : TBIdx n → Ω₀) (u v : Fin n)
    (order : List (Fin n × Fin n)) : Bool :=
  greedyMatching (fun e => lhatEntry App r lam s τ G G' ω e.1 u e.2 v) (thetaParam n) 5 order

/-- `π′ : [n] → [n] ∪ {unmatched}` is a possible partial mapping of Steps 1–3 of `TBAlign` with
cutoff `τ` on the input `(G, G̃)` and seeds `ω`: for some admissible edge order of every witness
graph, `π′(u)` is unmatched iff `M_TB(u, ṽ) = 0` for all `ṽ` (the set `V′` of (4)), and otherwise
`π′(u)` is some `ṽ` with `M_TB(u, ṽ) = 1` (the arbitrary choice of Step 3). -/
def IsTBPartial {Ω₀ : Type} (App : PermApprox Ω₀) (r : OTree → OTree) (lam s : ℝ) {n : ℕ}
    (τ : ℕ∞) (G G' : SimpleGraph (Fin n)) (ω : TBIdx n → Ω₀) (π' : Fin n → Option (Fin n)) :
    Prop :=
  ∃ orders : Fin n → Fin n → List (Fin n × Fin n),
    (∀ u v, IsWitnessOrder G G' u v (orders u v)) ∧
    ∀ u, (π' u = none ↔ ∀ v, mTB App r lam s τ G G' ω u v (orders u v) = false) ∧
      ∀ v, π' u = some v → mTB App r lam s τ G G' ω u v (orders u v) = true

/-- The witness count (5): `W(u, ṽ) = |{i matched in π̂ : u ∈ N(i), ṽ ∈ Ñ(π̂(i))}|`. -/
noncomputable def witnessCount {n : ℕ} (G G' : SimpleGraph (Fin n)) (cur : Fin n → Option (Fin n))
    (u v : Fin n) : ℕ :=
  (Finset.univ.filter fun i => ∃ j, cur i = some j ∧ G.Adj i u ∧ G'.Adj j v).card

/-- `(u, ṽ)` is a currently unmatched pair: `u` is unmatched and `ṽ` is not in the image. -/
def UnmatchedPair {n : ℕ} (cur : Fin n → Option (Fin n)) (u v : Fin n) : Prop :=
  cur u = none ∧ ∀ i, cur i ≠ some v

/-- One iteration of Step 4: set `π̂(u) = ṽ` for a currently unmatched pair maximizing `W(u, ṽ)`
(ties broken arbitrarily). -/
def CompletionStep {n : ℕ} (G G' : SimpleGraph (Fin n)) (cur next : Fin n → Option (Fin n)) :
    Prop :=
  ∃ u v, UnmatchedPair cur u v ∧
    (∀ u' v', UnmatchedPair cur u' v' → witnessCount G G' cur u' v' ≤ witnessCount G G' cur u v) ∧
    next = Function.update cur u (some v)

/-- `π̂` (written `πc`) is a possible result of the seeded completion (Step 4) started from `π′`: reached by
iterations of `CompletionStep`, and defined on all of `V`. -/
def IsSeededCompletion {n : ℕ} (G G' : SimpleGraph (Fin n)) (π' πc : Fin n → Option (Fin n)) :
    Prop :=
  Relation.ReflTransGen (CompletionStep G G') π' πc ∧ ∀ u, πc u ≠ none

/-- `(π′, π̂)` is a possible output of `TBAlign` (Steps 1–4) with cutoff `τ` on `(G, G̃)` and seeds
`ω`. -/
def IsTBOutput {Ω₀ : Type} (App : PermApprox Ω₀) (r : OTree → OTree) (lam s : ℝ) {n : ℕ}
    (τ : ℕ∞) (G G' : SimpleGraph (Fin n)) (ω : TBIdx n → Ω₀) (π' πc : Fin n → Option (Fin n)) :
    Prop :=
  IsTBPartial App r lam s τ G G' ω π' ∧ IsSeededCompletion G G' π' πc

end TreeCorrMatch.ErrorFree


