-- Prove2me | Definitions.Def_APrioriTSP_Sampling_Setting
-- name    : APrioriTSP_Sampling_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:29.720821+00:00
-- url     : https://prove2.me/theorems/da839c85-031f-4924-99ad-511a0d4d6ae7
-- title:
--   §1, pp. 1–4, Definition 8 p. 6 — a priori TSP instances with a depot, tours, a priori cost, OPT, OPT_TSP, c(v, S), the sampling cost (2), ε-normalized instances
-- statement:
--   The model of Blauth, Neuwohner, Puhlmann and Vygen, *Improved guarantees for the a priori TSP* (§1, pp. 1–4; Definition 8, p. 6).
--
--   **Instances.** A finite set $V$ of customers carries a **semi-metric** $c : V \times V \to \mathbb R$: $c(v,v) = 0$, $c(u,v) = c(v,u)$ and $c(u,w) \le c(u,v) + c(v,w)$; distinct customers may be at distance $0$, and $c \ge 0$ follows. Every customer $v$ is **active** independently with probability $0 < p(v) \le 1$. An **instance with depot** has a customer $d$ with $p(d) = 1$.
--
--   **Tours and the a priori cost.** A tour $T$ lists every customer exactly once and is read cyclically: $T[0], T[1], \dots, T[n-1], T[0]$. For a list $l = (l_0, \dots, l_{m-1})$ write $c(l) = \sum_{i<m} c(l_i, l_{(i+1) \bmod m})$ for the length of the closed walk through it. Given the active set $A$, the tour is cut short to $T[A]$, the subsequence of active customers. With
--   $$\Pr_{q}[S = U] = \prod_{v \in U} q(v) \prod_{v \notin U} (1 - q(v))$$
--   the probability that independent inclusion with probabilities $q$ produces $U$, the **a priori cost** of $T$ is $\mathbb E_{A\sim p}[c(T[A])] = \sum_{A \subseteq V} \Pr_p[A]\, c(T[A])$, and
--   $$\mathrm{OPT} = \min_{T \text{ tour}} \mathbb E_{A \sim p}[c(T[A])].$$
--
--   **Master route quantities** (p. 3). $\mathrm{OPT}_{\mathrm{TSP}}(S, c)$ is the length of a shortest closed tour through exactly the customers of $S$ ($0$ for $S = \emptyset$ or a single customer), and $c(v, S) = \min\{c(v,s) : s \in S\}$.
--
--   **The sampling cost (2)** (p. 4). For $\alpha \ge 0$ and $f$, the sample $S$ includes every customer $v$ independently with probability $f(p(v))$, and
--   $$\mathbb E_{S\sim f\circ p}\Big[\alpha \cdot \mathrm{OPT}_{\mathrm{TSP}}(S, c) + 2 \sum_{v \in V} p(v)\, c(v, S)\Big]$$
--   is the expectation in (2). Two sampling functions are used: $f(x) = 1 - (1-x)^\sigma$, and $f(x) = \sigma x$ for $x \ne 1$ with $f(1) = 1$.
--
--   **Normalized instances** (Definition 8). For $\varepsilon > 0$, an instance is **$\varepsilon$-normalized** if it has a depot $d$ and $p(v) = \varepsilon$ for every $v \ne d$.
--
--   These objects carry every statement of the mission: the goal and Lemmas 9, 11, 15, Corollary 16 bound (2) by a multiple of OPT, and Proposition 10 and Lemma 33 concern the a priori cost.
--
--   **Formalization Note** `IsDepotInstance c p d` bundles the six hypotheses as named fields. Tours are duplicate-free lists containing every customer; `cycleCost` uses `l.zip (l.rotate 1)`, and cutting short is `List.filter`. Expectations are finite sums over `Finset V` with the product weights `subsetProb`; no measure theory is used. `aPrioriOpt`, `tspOpt` and `distToSet` are `sInf` of images of finite sets; the first two sets are nonempty and the values are minima. `distToSet c v ∅` is the junk value $0$, which never enters (2) on an instance with depot, since $d \in S$ with probability one. `linSampling σ` returns $1$ at $x = 1$ (the algorithm's standing $f(1) = 1$, p. 4; proof of Lemma 9, p. 34); `powerSampling σ 1 = 1` for $\sigma \ne 0$. The ratio (2) is never formed: statements bound the expectation by $\rho \cdot \mathrm{OPT}$.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, pp. 1–4 and 6, §1, Equation (2), Definition 8

import Mathlib

namespace APrioriTSP.Sampling

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An **instance of the a priori TSP with a depot** (§1, p. 1; p. 4): a finite set `V` of
customers, a semi-metric `c` on `V` (zero on the diagonal, symmetric, triangle inequality;
distinct customers may be at distance `0`), activation probabilities `0 < p v ≤ 1`, and a depot
`d` with `p d = 1`. Nonnegativity of `c` follows from the three metric axioms. -/
structure IsDepotInstance (c : V → V → ℝ) (p : V → ℝ) (d : V) : Prop where
  c_self : ∀ v, c v v = 0
  c_symm : ∀ u v, c u v = c v u
  c_triangle : ∀ u v w, c u w ≤ c u v + c v w
  p_pos : ∀ v, 0 < p v
  p_le_one : ∀ v, p v ≤ 1
  p_depot : p d = 1

/-- A **tour** of `V`: a list that visits every customer exactly once, read as a cyclic
order `T[0], T[1], …, T[n-1], T[0]`. -/
def IsTour (T : List V) : Prop :=
  T.Nodup ∧ ∀ v, v ∈ T

/-- The length of the closed walk through the list `l` in its order, returning to the first
element: `Σ_i c(l[i], l[i+1 mod n])`. The empty list costs `0`, a singleton `[a]` costs
`c a a`, and `[a, b]` costs `c a b + c b a`. -/
def cycleCost (c : V → V → ℝ) (l : List V) : ℝ :=
  ((l.zip (l.rotate 1)).map (fun e => c e.1 e.2)).sum

/-- The probability that the random set equals `U` when every customer `v` is included
independently with probability `q v`. -/
noncomputable def subsetProb (q : V → ℝ) (U : Finset V) : ℝ :=
  (∏ v ∈ U, q v) * ∏ v ∈ univ \ U, (1 - q v)

/-- The **a priori cost** `E_{A∼p}[c(T[A])]` of a tour `T`: the expected length of `T` cut
short to the random active set `A` (customers active independently with probability `p v`). -/
noncomputable def aPrioriCost (c : V → V → ℝ) (p : V → ℝ) (T : List V) : ℝ :=
  ∑ A : Finset V, subsetProb p A * cycleCost c (T.filter (· ∈ A))

/-- `OPT`: the minimum a priori cost over all tours (p. 2). The set of tours is finite and
nonempty and the costs are nonnegative on instances, so the infimum is attained. -/
noncomputable def aPrioriOpt (c : V → V → ℝ) (p : V → ℝ) : ℝ :=
  sInf (aPrioriCost c p '' {T : List V | IsTour T})

/-- `OPT_TSP(S, c)`: the length of a shortest closed tour through exactly the customers of `S`
(p. 3). The set of such orderings is finite and nonempty; for `S = ∅` it is `{[]}`, value `0`. -/
noncomputable def tspOpt (c : V → V → ℝ) (S : Finset V) : ℝ :=
  sInf (cycleCost c '' {l : List V | l.Nodup ∧ l.toFinset = S})

/-- `c(v, S) = min {c(v, s) : s ∈ S}` (p. 3). For `S = ∅` the value is the junk `0`; it never
matters, since the sampled set contains the depot with probability one. -/
noncomputable def distToSet (c : V → V → ℝ) (v : V) (S : Finset V) : ℝ :=
  sInf (c v '' (S : Set V))

/-- The expectation in the bound (2), p. 4:
`E_{S∼f∘p}[α · OPT_TSP(S, c) + 2 · Σ_{v∈V} p(v) · c(v, S)]`, where every customer `v` enters
the sample `S` independently with probability `f(p(v))`. -/
noncomputable def samplingCost (α : ℝ) (f : ℝ → ℝ) (c : V → V → ℝ) (p : V → ℝ) : ℝ :=
  ∑ S : Finset V, subsetProb (fun v => f (p v)) S *
    (α * tspOpt c S + 2 * ∑ v, p v * distToSet c v S)

/-- The sampling function `f(x) = 1 − (1 − x)^σ` (real power). For `σ ≠ 0`, `f(1) = 1`. -/
noncomputable def powerSampling (σ : ℝ) (x : ℝ) : ℝ :=
  1 - (1 - x) ^ σ

/-- The sampling function `f(x) = σ x` for `x ≠ 1`, with the algorithm's standing convention
`f(1) = 1` (p. 4; proof of Lemma 9, p. 34). -/
noncomputable def linSampling (σ : ℝ) (x : ℝ) : ℝ :=
  if x = 1 then 1 else σ * x

/-- Definition 8 (p. 6): an instance is **ε-normalized** if it is an instance with depot `d`
and every other customer has activation probability `ε`. -/
def IsNormalized (c : V → V → ℝ) (p : V → ℝ) (d : V) (ε : ℝ) : Prop :=
  IsDepotInstance c p d ∧ ∀ v, v ≠ d → p v = ε

end APrioriTSP.Sampling


