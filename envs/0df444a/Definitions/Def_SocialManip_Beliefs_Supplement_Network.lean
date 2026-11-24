-- Prove2me | Definitions.Def_SocialManip_Beliefs_Supplement_Network
-- name    : SocialManip_Beliefs_Supplement_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:10:11.466487+00:00
-- url     : https://prove2.me/theorems/fb952221-d473-406c-b0e9-58f8df09ebce
-- title:
--   §2–§5, App. B — model data, Assumption 1, DeGroot centrality (Def. 4), log-distance and density (Defs. 6, 9), preservation (Def. 5), G_η, symmetric networks (Defs. 7–8), Γ*
-- statement:
--   Network objects of Mostagir, Ozdaglar and Siderius used by the companion theorems. The published setting supplies the state $y\in\{S,R\}$, the influence matrix $W$ (zero Bayesian rows, DeGroot rows $\alpha_{ij}$), the vector $\theta=(\mathbf 1_B,\theta_D)$ and the belief recursion.
--
--   1. **Model data.** An instance consists of the Bayesian set $B$, the weights $\theta_i,\alpha_{ij}$, the signal qualities $p_i$, the prior $q=P(y=S)$, the intensities $\lambda,\lambda^*$, the influence cost $\varepsilon$ and the payoff asymmetry $b$. Its *standing constraints* are $p_i\in[1/2,1)$ and, for DeGroot agents, $\theta_i,\alpha_{ij}\ge0$ with $\theta_i+\sum_j\alpha_{ij}=1$; its *game domain* is $q\in(0,1)$, $\lambda,\lambda^*,\varepsilon>0$, $b\in(-1,1)$.
--   2. **Assumption 1** (pp. 10–11), for an unweighted network $G^*$ in which a DeGroot agent's links are her positive weights: (i) $p_i<(\lambda^*+\lambda)/(2\lambda)$ for all $i$; (ii) $G^*$ is strongly connected; (iii) for DeGroots, $\theta_i>0$ iff $p_i>1/2$; (iv) some $p_i>1/2$.
--   3. **DeGroot centrality** (Definition 4). A Bayesian-avoiding walk is a vertex sequence $v_0\to\dots\to v_\ell$ of DeGroot agents (repetitions allowed) along links of $G^*$, with weight $w_W=\prod_k w_{v_kv_{k+1}}$ (length $0$ has weight $1$). With $\mathcal W_{ij}$ the set of such walks from $i$ to $j$,
--   $$D_i(\gamma)=\sum_{j=1}^n\theta_j\gamma_j\sum_{W\in\mathcal W_{ij}}w_W .$$
--   The influence vector of a targeting $x$ is $\gamma_i=0$ for Bayesians and $\gamma_i=x_i$ for DeGroots.
--   4. **Log-distance and density** (§5.1, Definition 9). $d_{ij}=\min_W\sum_{(k\to l)\in W}-\log w_{kl}$ over walks from $i$ to $j$ whose steps are positive DeGroot weights (so all vertices but the last are DeGroot), $+\infty$ if there is none. $G$ is *$\delta$-dense* if $d_{ij}\le\log(n+\delta)$ for every DeGroot $i$ and every agent $j$; sets $I_1,\dots,I_k$ witness *$\delta$-local density* if they cover the agents and $d_{ij}\le\log(|I_\ell|+\delta)$ for DeGroot $i\in I_\ell$ and $j\in I_\ell$.
--   5. **Network preservation** (Definition 5): $w'_{ij}=w_{ij}(1-\theta'_i)/(1-\theta_i)$ in DeGroot rows; the homogeneous preservation $G_{\theta'}$ sets every $\theta'_i=\theta'$.
--   6. **Ring–complete mixture** $G_\eta$ (p. 25): $\theta_i=\eta/(n+1)+(1-\eta)/2$ and $\alpha_{ij}=\eta/(n+1)+(1-\eta)\tfrac12\mathbf 1\{j=i-1\}$ (cyclic), the mixture of the complete network ($\theta^c_i=\alpha^c_{ij}=1/(n+1)$) and the equal-influence ring ($\theta^r_i=\alpha^r_{i,i-1}=1/2$). A *continuous chain* of Bayesians is a cyclic arc of the ring.
--   7. **Symmetric networks** (Definitions 7–8): $G^*$ is symmetric if any vertex is mapped to any other by a graph automorphism; a degree-$k$ symmetric network has $|N(i)|=k$ and equal-influence weights $\theta_i=\alpha_{ij}=1/(1+k)$ on links ($0$ off links) for DeGroots; $B$ is a symmetric placement in an undirected $G^*$ if $G^*\setminus B$ is symmetric; $\varphi$ is the fraction of links into Bayesians that join a DeGroot and a Bayesian.
--   8. **The principal's program** (Appendix B): over $\gamma,r\in\{0,1\}^n$, maximize $\sum_{i\in D}(r_i-\varepsilon\gamma_i)$ subject to $r_i\le D_i(\gamma)+(1+b)/2$ for all $i$; $\Gamma^*$ is the set of all maximizers.
--
--   These objects carry the paper's characterization of manipulation: the limiting belief of the incorrect state equals the DeGroot centrality, and density, symmetry and the integer program bound it.
--
--   **Formalization Note** Walk sums are extended nonnegative reals, so a divergent sum is $+\infty$ rather than $0$; log-distances are extended reals with empty infimum $+\infty$; $\log(n+\delta)$ is used only when $n+\delta>0$. The terminal vertex of a log-distance walk may be Bayesian and only DeGroot agents start one, as an explicit correction to the all-start formula: zero Bayesian rows cannot reach other vertices, while Examples 3–4 on p. 37 give finite diameters with Bayesians. Bayesian starts are excluded and Bayesian terminal vertices are admitted; no Bayesian outgoing weights are invented. The program uses the real value of $D_i(\gamma)$, which is finite under Assumption 1 (Proposition 2).
--
--   For local density the distance is global, as Definition 9 states; the p. 56 proof additionally requires internal walks without deriving that stronger property. The single-set refutation is unaffected. Bayesian targeting coordinates in the binary program are zero, as the influence vector on p. 12 requires.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), §2 pp. 5–8; Assumption 1 pp. 10–11; influence vector p. 12; Definition 4 p. 13; Definition 5 p. 16; log-diameter and Definition 6 pp. 19–20; ring p. 21, (3) p. 23, G_η p. 25; Definitions 7–8 and φ pp. 25–26; Definition 9 and the principal's program p. 36

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting

open scoped ENNReal

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- The data of one instance of the paper's model (§2, pp. 4–8): `n` agents, the Bayesian set `B`,
the DeGroot weights `θ i`, `α i j`, signal qualities `p i`, the prior `q = P(y = S)`, the organic
and principal news intensities `λ = lam`, `λ* = lamStar`, the per-agent influence cost `ε` and the
payoff asymmetry `b` of Table 1. -/
structure Model (n : ℕ) where
  B : Finset (Fin n)
  θ : Fin n → ℝ
  α : Matrix (Fin n) (Fin n) ℝ
  p : Fin n → ℝ
  q : ℝ
  lam : ℝ
  lamStar : ℝ
  ε : ℝ
  b : ℝ

namespace Model

variable {n : ℕ}

/-- The standing constraints of §2: `p i ∈ [1/2, 1)` (display (1), p. 5), and for every DeGroot
agent nonnegative weights with `θ i + ∑ j α i j = 1` (p. 7). -/
def Standing (M : Model n) : Prop :=
  (∀ i, 1 / 2 ≤ M.p i ∧ M.p i < 1) ∧ (∀ i ∉ M.B, 0 ≤ M.θ i) ∧
    (∀ i ∉ M.B, ∀ j, 0 ≤ M.α i j) ∧ (∀ i ∉ M.B, M.θ i + ∑ j, M.α i j = 1)

/-- The game-parameter domain of §2: `q ∈ (0,1)`, `λ > 0`, `λ* > 0`, `ε > 0`, `b ∈ (-1,1)`. -/
def GameDomain (M : Model n) : Prop :=
  0 < M.q ∧ M.q < 1 ∧ 0 < M.lam ∧ 0 < M.lamStar ∧ 0 < M.ε ∧ -1 < M.b ∧ M.b < 1

/-- Assumption 1, pp. 10–11, with the unweighted network `G*` given by `adj` (`adj i j`: `i`
listens to `j`). A DeGroot agent's links are her positive weights; Bayesian links are free.
(i) `p i < (λ* + λ)/(2λ)`; (ii) `G*` strongly connected; (iii) for DeGroots `θ i > 0 ↔ p i > 1/2`;
(iv) some `p i > 1/2`. -/
def Assumption1 (M : Model n) (adj : Fin n → Fin n → Prop) : Prop :=
  (∀ i, M.p i < (M.lamStar + M.lam) / (2 * M.lam)) ∧
    (∀ i ∉ M.B, ∀ j, adj i j ↔ 0 < M.α i j) ∧
    (∀ i j, i ≠ j → Relation.TransGen adj i j) ∧
    (∀ i ∉ M.B, (0 < M.θ i ↔ 1 / 2 < M.p i)) ∧
    (∃ i, 1 / 2 < M.p i)

end Model

/-! ### Walks and DeGroot centrality (§3.3, p. 13) -/

/-- A Bayesian-avoiding walk of length `ℓ` (p. 13): a vertex sequence `v 0, …, v ℓ` (vertices may
repeat, footnote 16), every vertex DeGroot, every step `v k → v (k+1)` a link of `G*`, i.e. a
positive weight of the DeGroot row `v k`. -/
def IsAvoidingWalk {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ) (ℓ : ℕ)
    (v : Fin (ℓ + 1) → Fin n) : Prop :=
  (∀ k, v k ∉ B) ∧ ∀ k : Fin ℓ, 0 < α (v k.castSucc) (v k.succ)

/-- The weight `w_W = ∏ w_{v_k v_{k+1}}` of a walk (p. 13); the empty product of a length-zero walk
is `1`. -/
noncomputable def walkWeight {n : ℕ} (α : Matrix (Fin n) (Fin n) ℝ) (ℓ : ℕ)
    (v : Fin (ℓ + 1) → Fin n) : ℝ :=
  ∏ k : Fin ℓ, α (v k.castSucc) (v k.succ)

open Classical in
/-- `∑_{W ∈ 𝒲_ij} w_W`: the total weight of all Bayesian-avoiding walks from `i` to `j`, of every
length including `0`, as an extended nonnegative real (so a divergent sum is `∞`, not `0`). -/
noncomputable def avoidingWalkSum {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, ∑ v ∈ (Finset.univ.filter fun v : Fin (ℓ + 1) → Fin n =>
      v 0 = i ∧ v (Fin.last ℓ) = j ∧ IsAvoidingWalk B α ℓ v), ENNReal.ofReal (walkWeight α ℓ v)

/-- Definition 4, p. 13: the DeGroot centrality `D_i(γ) = ∑_j θ_j γ_j ∑_{W ∈ 𝒲_ij} w_W`. -/
noncomputable def centrality {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ)
    (α : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) (i : Fin n) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (θ j * γ j) * avoidingWalkSum B α i j

/-- The influence vector `γ(x)` of p. 12: `γ_i = 0` for Bayesians, `γ_i = x_i` for DeGroots. -/
def influence {n : ℕ} (B : Finset (Fin n)) (x : Fin n → Bool) : Fin n → ℝ :=
  fun i => if i ∈ B then 0 else if x i then 1 else 0

/-- The indicator vector of a Boolean vector. -/
def boolVec {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ := fun i => if x i then 1 else 0

/-! ### Log-distance and density (§5.1, pp. 19–20; Definition 9, p. 36) -/

/-- A walk admissible for the log-distance: every step is a positive DeGroot weight, so every
vertex except the terminal one is DeGroot (Bayesian rows of `W` are zero); the terminal vertex may
be Bayesian. -/
def IsLogWalk {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ) (ℓ : ℕ)
    (v : Fin (ℓ + 1) → Fin n) : Prop :=
  ∀ k : Fin ℓ, v k.castSucc ∉ B ∧ 0 < α (v k.castSucc) (v k.succ)

/-- The log-cost `∑_{(k → l) ∈ W} -log w_kl` of a walk. -/
noncomputable def logCost {n : ℕ} (α : Matrix (Fin n) (Fin n) ℝ) (ℓ : ℕ)
    (v : Fin (ℓ + 1) → Fin n) : ℝ :=
  ∑ k : Fin ℓ, -Real.log (α (v k.castSucc) (v k.succ))

/-- Definition 9, p. 36 (and the inner minimum of the log-diameter, p. 19): the log-distance
`d_ij`, the infimum of the log-cost over admissible walks from `i` to `j`; `+∞` when there is none. -/
noncomputable def logDist {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : EReal :=
  ⨅ (ℓ : ℕ) (v : Fin (ℓ + 1) → Fin n) (_ : v 0 = i ∧ v (Fin.last ℓ) = j ∧ IsLogWalk B α ℓ v),
    ((logCost α ℓ v : ℝ) : EReal)

/-- Corrected non-vacuous reading of Definition 6 (pp. 19–20, 37): only DeGroot starting
vertices are tested, and Bayesian terminal vertices are permitted. The literal all-start
formula has infinite diameter whenever a zero Bayesian row must reach another vertex, in
conflict with Example 3. The correction removes Bayesian starts from the diameter domain;
it does not assign positive outgoing influence to a Bayesian row. -/
def IsDense {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) : Prop :=
  0 < (n : ℝ) + δ ∧ ∀ i ∉ B, ∀ j, logDist B α i j ≤ ((Real.log ((n : ℝ) + δ) : ℝ) : EReal)

/-- Corrected non-vacuous reading of Definition 9, p. 36: the sets `I 0, …, I (k-1)` witness that `G` is `δ`-locally dense: they cover
all agents, and within each `I ℓ` the log-distance from every DeGroot agent to every agent is at
most `log(|I ℓ| + δ)` (with `|I ℓ| + δ > 0`). -/
def IsLocallyDenseCover {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (k : ℕ) (I : Fin k → Finset (Fin n)) : Prop :=
  (∀ a, ∃ l, a ∈ I l) ∧
    ∀ l, 0 < ((I l).card : ℝ) + δ ∧ ∀ i ∈ I l, i ∉ B → ∀ j ∈ I l,
      logDist B α i j ≤ ((Real.log (((I l).card : ℝ) + δ) : ℝ) : EReal)

/-! ### Network preservation (Definition 5, p. 16) -/

/-- Definition 5: the weights of the network preservation `(G', θ')` of `(G, θ)`,
`w'_ij = w_ij (1 - θ'_i)/(1 - θ_i)` for DeGroot rows (Bayesian rows are unchanged; `W` zeroes them). -/
noncomputable def preserve {n : ℕ} (B : Finset (Fin n)) (θ θ' : Fin n → ℝ)
    (α : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ B then α i j else α i j * (1 - θ' i) / (1 - θ i)

/-- The homogeneous network preservation `G_{θ'}` of a model (p. 16): every DeGroot experience
weight becomes `θ'` and the DeGroot rows are rescaled by `(1 - θ')/(1 - θ_i)`. -/
noncomputable def Model.homPreserve {n : ℕ} (M : Model n) (θ' : ℝ) : Model n :=
  { M with θ := fun _ => θ', α := preserve M.B M.θ (fun _ => θ') M.α }

/-! ### Ring, complete network and their mixture `G_η` (§5.2–5.3, pp. 21–25) -/

/-- The cyclic predecessor `i - 1` of an agent on the ring `0 → n-1 → … → 1 → 0`. -/
def ringPred {n : ℕ} (i j : Fin n) : Prop := (j : ℕ) = ((i : ℕ) + n - 1) % n

/-- The weights of `G_η` (p. 25): `θ_i = η θ^c_i + (1-η) θ^r_i` and
`α_ij = η α^c_ij + (1-η) α^r_ij`, where the complete network has `θ^c_i = α^c_ij = 1/(n+1)` for all `j`
(Example 3, p. 37) and the equal-influence ring has `θ^r_i = α^r_{i,i-1} = 1/2` (equation (3), p. 23),
`α^r_ij = 0` otherwise. -/
noncomputable def etaTheta (n : ℕ) (η : ℝ) : Fin n → ℝ :=
  fun _ => η / ((n : ℝ) + 1) + (1 - η) / 2

open Classical in
/-- See `etaTheta`. -/
noncomputable def etaAlpha (n : ℕ) (η : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => η / ((n : ℝ) + 1) + (1 - η) * (if ringPred i j then 1 / 2 else 0)

open Classical in
/-- A continuous chain of Bayesians on the ring (p. 21): `B` is a cyclic arc
`{s, s+1, …, s+m-1}` (indices mod `n`). -/
def IsRingArc {n : ℕ} (B : Finset (Fin n)) : Prop :=
  ∃ s m : ℕ, ∀ i : Fin n, i ∈ B ↔ ((i : ℕ) + n - s % n) % n < m

/-! ### Symmetric networks (Definitions 7–8, pp. 25–26) -/

/-- A directed unweighted graph on `V` is symmetric (p. 25): for every two vertices `i, j` some
graph automorphism `f` (footnote 28) maps `i` to `j`. -/
def IsSymmetricGraph (V : Type*) (adj : V → V → Prop) : Prop :=
  ∀ i j : V, ∃ f : V ≃ V, f i = j ∧ ∀ k l, adj k l ↔ adj (f k) (f l)

open Classical in
/-- Definition 7 with degree `k` (pp. 25–26): `G*` is symmetric, every agent has exactly `k`
neighbours `N(i) = {j | adj i j}`, and every DeGroot agent uses equal-influence weighting (3):
`θ_i = α_ij = 1/(1 + |N(i)|)` for `j ∈ N(i)`, `α_ij = 0` otherwise. -/
def IsDegreeSymmetric {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ)
    (α : Matrix (Fin n) (Fin n) ℝ) (adj : Fin n → Fin n → Prop) (k : ℕ) : Prop :=
  IsSymmetricGraph (Fin n) adj ∧ (∀ i, (Finset.univ.filter (adj i)).card = k) ∧
    ∀ i ∉ B, θ i = 1 / (1 + (k : ℝ)) ∧ ∀ j, α i j = if adj i j then 1 / (1 + (k : ℝ)) else 0

/-- Definition 8, p. 26: in an undirected `G*`, `B` is a symmetric placement if the induced
subgraph `G* \ B` on the DeGroot agents is symmetric. -/
def IsSymmetricPlacement {n : ℕ} (B : Finset (Fin n)) (adj : Fin n → Fin n → Prop) : Prop :=
  (∀ i j, adj i j ↔ adj j i) ∧
    IsSymmetricGraph {i : Fin n // i ∉ B} (fun i j => adj i.1 j.1)

open Classical in
/-- `φ`, p. 26: of all links into Bayesian agents, the fraction that join a DeGroot agent and a
Bayesian agent. -/
noncomputable def bayesEdgeFraction {n : ℕ} (B : Finset (Fin n)) (adj : Fin n → Fin n → Prop) : ℝ :=
  ((Finset.univ.filter fun e : Fin n × Fin n => e.1 ∉ B ∧ e.2 ∈ B ∧ adj e.1 e.2).card : ℝ) /
    ((Finset.univ.filter fun e : Fin n × Fin n => e.2 ∈ B ∧ adj e.1 e.2).card : ℝ)

/-! ### The principal's binary program (Appendix B, p. 36) -/

/-- Feasibility in the principal's integer program: `r_i ≤ D_i(γ) + (1+b)/2` for every agent `i`,
with `γ_i, r_i ∈ {0, 1}` (Booleans). -/
def ipFeasible {n : ℕ} (M : Model n) (γ r : Fin n → Bool) : Prop :=
  (∀ i ∈ M.B, γ i = false) ∧
    ∀ i, (if r i then (1 : ℝ) else 0) ≤
      (centrality M.B M.θ M.α (boolVec γ) i).toReal + (1 + M.b) / 2

/-- The objective `∑_{i ∈ D} (r_i - ε γ_i)` of the principal's integer program. -/
noncomputable def ipObjective {n : ℕ} (M : Model n) (γ r : Fin n → Bool) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· ∉ M.B), ((if r i then (1 : ℝ) else 0) - M.ε * (if γ i then 1 else 0))

/-- `Γ*`, p. 36: the set of all maximizers `(γ, r)` of the principal's integer program. -/
def ipArgmax {n : ℕ} (M : Model n) : Set ((Fin n → Bool) × (Fin n → Bool)) :=
  {g | ipFeasible M g.1 g.2 ∧ ∀ g' : (Fin n → Bool) × (Fin n → Bool), ipFeasible M g'.1 g'.2 →
    ipObjective M g'.1 g'.2 ≤ ipObjective M g.1 g.2}

end SocialManip.Beliefs.Supplement


