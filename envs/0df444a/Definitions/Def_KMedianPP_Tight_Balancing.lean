-- Prove2me | Definitions.Def_KMedianPP_Tight_Balancing
-- name    : KMedianPP_Tight_Balancing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:02:46.402233+00:00
-- url     : https://prove2.me/theorems/7a321cac-7eef-4ab8-855a-815ede0ce865
-- title:
--   §3–§4.1 — balancing constructions (P1)–(P3), the $\ell=1$ balanced mass, and the hit/miss process with $U$, $M$, $A$
-- statement:
--   Fix an instance with a reference clustering $P_1,\dots,P_k$, $c^*_1,\dots,c^*_k$ (see `Sampling`) and current centers $C$ (input indices $S$, nonempty).
--
--   **Balancing construction (p. 10).** Balanced masses $0\le b(x)\le D(x)^\ell$ for each input point; the imbalanced mass of $x$ is $D(x)^\ell-b(x)$, and $u_j=\sum_{x\in P_j}b(x)$ (`balMass`). With constant $\alpha$:
--   - (P1) Hit cost (`HitCostBound`): if $u_j>0$, $\sum_{x\in P_j}\frac{b(x)}{u_j}\,\mathrm{cost}(P_j,C\cup\{x\})\le\alpha\,\varphi(P_j)$;
--   - (P2) Imbalanced mass (`ImbalancedBound`): $\sum_{x\in P_j}(D(x)^\ell-b(x))\le\alpha\,\varphi(P_j)$;
--   - (P3) Monotonicity (`BalancedMonotone`): $u_j$ can only decrease as centers are added;
--
--   each for every center set $C$ and every cluster $P_j$ that can be unsettled at $C$ (`CanBeUnsettled`: some center of $C$ lies outside $P_j$; the first center settles its own cluster, so a cluster $P\supseteq C$ is never unsettled). `IsBalancingConstruction` is the conjunction. `FirstSampleBound` is the conclusion of Lemma 3.1 for $P_j$: $\sum_{z\in P_j}\sum_{x\in P_j}d(x,z)^\ell\le\alpha|P_j|\varphi(P_j)$, i.e. $\mathbb E[\mathrm{cost}(P_j,\{Z\})]\le\alpha\varphi(P_j)$ for $Z$ uniform in $P_j$. A `BalancingRule` gives balanced masses on every instance of every metric space; `IsOptimalClustering` says the reference clustering is an optimal solution (its cost is at most that of every set of $1$ to $k$ centers in $M$); `SatisfiesP1P2 F ℓ α` says the rule splits the masses and satisfies (P1), (P2) for the optimal clusterings of every instance.
--
--   **$\ell=1$ (p. 11).** `balancedMassL1`: $b(x)=\min\{D(w):w\in P,\ d^*_w\le d^*_x\}$ for $x$ in the cluster $P$.
--
--   **Hit/miss process.** A state is $(S,H)$: centers $S$ and settled clusters $H$; the others are unsettled, $r=|H^c|$ (`unsettledCount`). The next sample is $x_i$ with probability $D(x_i)^\ell/\mathrm{cost}(C)$; if $P_{\sigma(i)}$ is unsettled it is a hit with probability $b(x_i)/D(x_i)^\ell$, settling $P_{\sigma(i)}$; otherwise it is a miss. `hitProb`, `missProb` are the joint probabilities of (point, hit/miss). $U=\sum_{j\notin H}u_j$ (`balTotal`), $M=\sum_{j\in H}\mathrm{cost}(P_j,C)+\sum_{j\notin H}(\mathrm{cost}(P_j,C)-u_j)$ (`missMass`), $A=\sum_{j\in H}\mathrm{cost}(P_j,C)+\alpha\sum_{j\notin H}\varphi(P_j)$ (`missProxy`). For a state function $g$: `stepExp` $=\mathbb E[g_{\mathrm{new}}\mid S]$; `finalExp g s` $=\mathbb E[g_{\mathrm{final}}\mid S]$ after $s$ more samples; `hitExp` $=\mathbb E[g_{\mathrm{new}}\mid S,\text{hit}]$; `hitExpAt j` $=\mathbb E[g_{\mathrm{new}}\mid S,\text{hit of }P_j]$.
--
--   **Formalization Note.** If $\mathrm{cost}(C)=0$ the process has stopped (footnote 4) and `stepExp g` returns $g(S,H)$. `hitExp`, `hitExpAt` are ratios; the statements assume their denominators (the hit probabilities) are positive. The properties are required only for clusters that can be unsettled at the center set.
-- source:
--   Kaplan, Naori, Tight Bounds for k-Median++ and Improved Bounds for k-Means++, STOC 2027 submission (manuscript sha256 f017529e…), pp. 9–11 (PDF 11–13), §3 (balancing, (P1)–(P3), the case ℓ = 1); pp. 14–15 (PDF 16–17), §4.1 (U, M, A)

import Mathlib
import Definitions.Def_KMedianPP_Tight_Sampling

set_option autoImplicit false

universe u

namespace KMedianPP.Tight

open Finset

/-! Kaplan, Naori, *Tight Bounds for k-Median++ and Improved Bounds for k-Means++*, STOC 2027
submission (manuscript sha256 f017529e…), §3 (pp. 9–11) and §4.1 (pp. 14–15): balancing
constructions and their properties (P1)–(P3), the balanced mass for `ℓ = 1`, and the hit/miss
process with settled and unsettled clusters, the total balanced mass `U`, the miss mass `M` and
the miss proxy `A`.

Throughout, the instance is `X : Fin n → M` with a reference clustering `σ : Fin n → Fin k`,
`c : Fin k → M` (see `Def_KMedianPP_Tight_Sampling`), and the current centers are the input
points with indices in a nonempty `S : Finset (Fin n)`. A balancing construction is given by its
balanced masses `b S i` (the balanced part of the sampling mass `D(x_i)^ℓ` of input point `i`
when the centers are `S`); the balanced masses are only ever used for points of unsettled
clusters. -/

variable {M : Type*} [MetricSpace M] {n k : ℕ}

/-- The balanced mass `Σ_{x ∈ P_j} b(x)` of the cluster `P_j`. -/
noncomputable def balMass (σ : Fin n → Fin k) (b : Finset (Fin n) → Fin n → ℝ)
    (S : Finset (Fin n)) (j : Fin k) : ℝ :=
  ∑ i ∈ cluster σ j, b S i

/-- The cluster `P_j` can be unsettled when the current centers are `S`: some current center lies
outside `P_j`. The first center settles its own cluster (§3, p. 9), so a cluster is unsettled at a
state of the process exactly when the first center, and hence some current center, lies outside
it; a center set `S ⊆ P_j` only occurs with `P_j` settled. Properties (P1)–(P3) are stated for
unsettled clusters only, so they are required at such pairs `(S, j)` only. -/
def CanBeUnsettled (σ : Fin n → Fin k) (S : Finset (Fin n)) (j : Fin k) : Prop :=
  ∃ i ∈ S, σ i ≠ j

/-- The balanced masses split each sampling mass of a point of an unsettled cluster:
`0 ≤ b(x) ≤ D(x)^ℓ` (§3, p. 10: the sampling mass of each unsettled cluster is split into a
balanced and an imbalanced part, `D(x)^ℓ - b(x)`). -/
def SplitsMass (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ) (b : Finset (Fin n) → Fin n → ℝ) :
    Prop :=
  ∀ S : Finset (Fin n), ∀ i, CanBeUnsettled σ S (σ i) → 0 ≤ b S i ∧ b S i ≤ mass X ℓ S i

/-- (P1) Hit cost (p. 10): conditioned on a hit of the unsettled cluster `P_j` (the sampled point
is `x ∈ P_j` with probability `b(x)/Σ_{y ∈ P_j} b(y)`), its expected cost after the hit,
`cost(P_j, C ∪ {x})`, is at most `α ϕ(P_j)`. Required whenever the balanced mass of `P_j` is
positive (otherwise a hit of `P_j` has probability `0`). -/
def HitCostBound (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ α : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), ∀ j : Fin k, CanBeUnsettled σ S j → 0 < balMass σ b S j →
    (∑ i ∈ cluster σ j, b S i * clusterCost X σ ℓ (insert i S) j) / balMass σ b S j ≤
      α * phi X σ c ℓ j

/-- (P2) Imbalanced mass (p. 10): the imbalanced mass `Σ_{x ∈ P_j} (D(x)^ℓ - b(x))` of every
unsettled cluster `P_j` is at most `α ϕ(P_j)`. -/
def ImbalancedBound (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ α : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), ∀ j : Fin k, CanBeUnsettled σ S j →
    ∑ i ∈ cluster σ j, (mass X ℓ S i - b S i) ≤ α * phi X σ c ℓ j

/-- (P3) Monotonicity (p. 10): the balanced mass of an unsettled cluster can only decrease as
centers are added. -/
def BalancedMonotone (σ : Fin n → Fin k) (b : Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ S S' : Finset (Fin n), S ⊆ S' → ∀ j : Fin k, CanBeUnsettled σ S j →
    balMass σ b S' j ≤ balMass σ b S j

/-- A balancing construction on the instance with balancing constant `α`: balanced masses
splitting every sampling mass and satisfying (P1)–(P3) (§3, p. 10), for unsettled clusters. -/
def IsBalancingConstruction (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ α : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) : Prop :=
  SplitsMass X σ ℓ b ∧ HitCostBound X σ c ℓ α b ∧ ImbalancedBound X σ c ℓ α b ∧
    BalancedMonotone σ b

/-- The first-sample bound of Lemma 3.1 for the cluster `P_j`: for `Z` uniform in `P_j`,
`E[cost(P_j, {Z})] ≤ α ϕ(P_j)`, written multiplied by `|P_j|`:
`Σ_{z ∈ P_j} Σ_{x ∈ P_j} d(x, z)^ℓ ≤ α |P_j| ϕ(P_j)`. -/
def FirstSampleBound (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ α : ℝ)
    (j : Fin k) : Prop :=
  ∑ z ∈ cluster σ j, ∑ x ∈ cluster σ j, dist (X x) (X z) ^ ℓ ≤
    α * ((cluster σ j).card : ℝ) * phi X σ c ℓ j

/-- The reference clustering `(σ, c)` is an optimal solution (§2, p. 9): its cost
`Σ_i d(x_i, c*_{σ i})^ℓ` is at most the cost of every set of at least one and at most `k` centers
in `M`. (With `k ≥ 1` and `ℓ > 0` this forces every input point to be assigned to a nearest center
`c*_j`, ties broken arbitrarily, so the `P_j` are the optimal clusters.) -/
def IsOptimalClustering (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ : ℝ) : Prop :=
  ∀ C : Finset M, C.Nonempty → C.card ≤ k → refCost X σ c ℓ ≤ costOf X ℓ C

/-- A balancing construction as a rule: balanced masses for every instance (every metric space
`M`, every finite input `X : Fin n → M`, every reference clustering `σ`, `c`) and every set of
current centers (for metric spaces in a universe `u`). -/
def BalancingRule : Type (u + 1) :=
  ∀ {M : Type u} [MetricSpace M] {n k : ℕ}, (Fin n → M) → (Fin n → Fin k) → (Fin k → M) →
    Finset (Fin n) → Fin n → ℝ

/-- The rule `F` splits the sampling masses and satisfies (P1) and (P2) with constant `α` for the
optimal clusters of every instance (the hypothesis of Lemma 3.1). -/
def SatisfiesP1P2 (F : BalancingRule.{u}) (ℓ α : ℝ) : Prop :=
  ∀ (M : Type u) [MetricSpace M] (n k : ℕ) (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M),
    IsOptimalClustering X σ c ℓ →
    SplitsMass X σ ℓ (F X σ c) ∧ HitCostBound X σ c ℓ α (F X σ c) ∧
      ImbalancedBound X σ c ℓ α (F X σ c)

/-- The balanced mass for `ℓ = 1` (p. 11): for `x = x_i` in the cluster `P = P_{σ i}`,
`b(x) = min {D(w) : w ∈ P, d*_w ≤ d*_x}` (the minimum includes `w = x`, so `b(x) ≤ D(x)`). -/
noncomputable def balancedMassL1 (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  (univ.filter fun w => σ w = σ i ∧ dstar X σ c w ≤ dstar X σ c i).inf' ⟨i, by simp⟩
    (fun w => distTo X S (X w))

/-! ### The hit/miss process (§3 p. 10, §4.1 pp. 14–15)

A state of the process is the set `S` of current centers (input indices) and the set
`H : Finset (Fin k)` of settled clusters; the clusters outside `H` are unsettled and
`r = |Hᶜ|`. The next sample is input point `i` with probability `D(x_i)^ℓ / cost(C)`; if `P_{σ i}`
is unsettled it is a hit with probability `b(x_i)/D(x_i)^ℓ` (and then `P_{σ i}` becomes settled),
otherwise it is a miss; in both cases `x_i` is added to the centers. If `cost(C) = 0` the process
has stopped (footnote 4). -/

/-- The number `r` of unsettled clusters. -/
def unsettledCount (H : Finset (Fin k)) : ℕ := (univ \ H).card

/-- `U = Σ_{P_j unsettled} u_j`: the total balanced mass of the unsettled clusters (p. 14). -/
noncomputable def balTotal (σ : Fin n → Fin k) (b : Finset (Fin n) → Fin n → ℝ)
    (S : Finset (Fin n)) (H : Finset (Fin k)) : ℝ :=
  ∑ j ∈ univ \ H, balMass σ b S j

/-- The miss mass `M = Σ_{P_j settled} cost(P_j, C) + Σ_{P_j unsettled} (cost(P_j, C) - u_j)`
(p. 14). -/
noncomputable def missMass (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n)) (H : Finset (Fin k)) : ℝ :=
  ∑ j ∈ H, clusterCost X σ ℓ S j + ∑ j ∈ univ \ H, (clusterCost X σ ℓ S j - balMass σ b S j)

/-- The miss proxy `A = Σ_{P_j settled} cost(P_j, C) + α Σ_{P_j unsettled} ϕ(P_j)` (p. 15). -/
noncomputable def missProxy (X : Fin n → M) (σ : Fin n → Fin k) (c : Fin k → M) (ℓ α : ℝ)
    (S : Finset (Fin n)) (H : Finset (Fin k)) : ℝ :=
  ∑ j ∈ H, clusterCost X σ ℓ S j + α * ∑ j ∈ univ \ H, phi X σ c ℓ j

/-- The hit mass at input point `i`: `b(x_i)` if its cluster is unsettled, `0` if it is settled. -/
noncomputable def hitWeight (σ : Fin n → Fin k) (b : Finset (Fin n) → Fin n → ℝ)
    (S : Finset (Fin n)) (H : Finset (Fin k)) (i : Fin n) : ℝ :=
  if σ i ∈ H then 0 else b S i

/-- Probability that the next sample is input point `i` and is a hit (of `P_{σ i}`). -/
noncomputable def hitProb (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n)) (H : Finset (Fin k)) (i : Fin n) : ℝ :=
  hitWeight σ b S H i / totalCost X ℓ S

/-- Probability that the next sample is input point `i` and is a miss. -/
noncomputable def missProb (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n)) (H : Finset (Fin k)) (i : Fin n) : ℝ :=
  (mass X ℓ S i - hitWeight σ b S H i) / totalCost X ℓ S

/-- `E[g_new | S]`: the expectation of a state function `g` after the next sample of the hit/miss
process from the state `(S, H)` (a hit at `x_i` leads to `(S ∪ {i}, H ∪ {σ i})`, a miss at `x_i` to
`(S ∪ {i}, H)`); if `cost(C) = 0` the process has stopped and the value is `g(S, H)`. -/
noncomputable def stepExp (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) (g : Finset (Fin n) → Finset (Fin k) → ℝ)
    (S : Finset (Fin n)) (H : Finset (Fin k)) : ℝ :=
  if totalCost X ℓ S = 0 then g S H
  else ∑ i, (hitProb X σ ℓ b S H i * g (insert i S) (insert (σ i) H) +
    missProb X σ ℓ b S H i * g (insert i S) H)

/-- `E[g_final | S]` with `s` samples remaining: the expectation of `g` at the end of the hit/miss
process run for `s` more samples from the state `(S, H)`. -/
noncomputable def finalExp (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) (g : Finset (Fin n) → Finset (Fin k) → ℝ) :
    ℕ → Finset (Fin n) → Finset (Fin k) → ℝ
  | 0, S, H => g S H
  | s + 1, S, H => stepExp X σ ℓ b (finalExp X σ ℓ b g s) S H

/-- `E[g_new | S, hit]`: the expectation of `g` after the next sample, conditioned on that sample
being a hit (used when the hit probability `Σ_i hitProb i` is positive). -/
noncomputable def hitExp (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) (g : Finset (Fin n) → Finset (Fin k) → ℝ)
    (S : Finset (Fin n)) (H : Finset (Fin k)) : ℝ :=
  (∑ i, hitProb X σ ℓ b S H i * g (insert i S) (insert (σ i) H)) /
    ∑ i, hitProb X σ ℓ b S H i

/-- `E[g_new | S, hit of P_j]`: the expectation of `g` after the next sample, conditioned on that
sample being a hit of the cluster `P_j` (used when this event has positive probability). -/
noncomputable def hitExpAt (X : Fin n → M) (σ : Fin n → Fin k) (ℓ : ℝ)
    (b : Finset (Fin n) → Fin n → ℝ) (g : Finset (Fin n) → Finset (Fin k) → ℝ) (j : Fin k)
    (S : Finset (Fin n)) (H : Finset (Fin k)) : ℝ :=
  (∑ i ∈ cluster σ j, hitProb X σ ℓ b S H i * g (insert i S) (insert j H)) /
    ∑ i ∈ cluster σ j, hitProb X σ ℓ b S H i

end KMedianPP.Tight


