-- Prove2me | Definitions.Def_SWSSNet_Diffusion_Network
-- name    : SWSSNet_Diffusion_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:05.297935+00:00
-- url     : https://prove2.me/theorems/3a9af0a1-2f7f-4577-afb1-3470fb054769
-- title:
--   §2–§4, pp. 5–18 — tree network under CRP, θ, the SWSS value ϑ_p of (LP′), h (12), gains d (13), Ψ (37), drift (42), B₁, B₂ for a pool ĵ
-- statement:
--   This module fixes the model of a multiclass multi-pool Markovian parallel-server network in the Halfin–Whitt limit, with no abandonment.
--
--   **Network.** There are $I$ customer classes and $J$ server pools. Write $i\sim j$ when pool $j$ can serve class $i$, and let $G$ be the bipartite graph on classes and pools with these edges. The graph $G$ is assumed to be a **tree**.
--
--   **Parameters.** The first-order limits are $\lambda_i>0$ (arrival rates), $\nu_j>0$ (pool sizes) and $\mu_{ij}>0$ for $i\sim j$ (service rates). The second-order limits are $\hat\lambda_i,\hat\nu_j,\hat\mu_{ij}\in\mathbb R$.
--
--   **CRP.** Let $\xi^*$ be the unique solution of the linear program
--   $$
--   \text{minimize}\ \max_{j}\sum_i \xi_{ij}\quad\text{over }\xi\ge 0,\ \xi_{ij}=0\ (i\not\sim j),\quad\text{subject to}\ \sum_j \mu_{ij}\nu_j\xi_{ij}=\lambda_i\ \ \forall i. \qquad\text{(LP)}
--   $$
--   It is also required to satisfy (3): $\sum_i\xi^*_{ij}=1$ for every pool and $\xi^*_{ij}>0$ on every edge. Put $z^*_{ij}=\xi^*_{ij}\nu_j$.
--
--   **Derived quantities.** The module defines:
--
--   1. $\theta_j=\hat\nu_j+\sum_{i\in I(j)}\frac{\hat\mu_{ij}}{\mu_{ij}}z^*_{ij}$.
--   2. The vector $h$ of (12): $h_i=\hat\lambda_i-\sum_{j\in J(i)}(\mu_{ij}\xi^*_{ij}\hat\nu_j+\hat\mu_{ij}z^*_{ij})$.
--   3. For a positive probability vector $p$, the **SWSS parameter** $\vartheta_p$: the optimal value of
--   $$
--   \text{maximize}\ \vartheta\quad\text{subject to}\quad \hat\lambda_i\le\sum_{j\in J(i)}\mu_{ij}\kappa_{ij}-\vartheta p_i\ \ \forall i,\qquad \sum_{i\in I(j)}\kappa_{ij}=\theta_j\ \ \forall j, \qquad\text{(LP}'\text{)}
--   $$
--   over $\vartheta\in\mathbb R$ and $\kappa$ supported on the edges.
--   4. The **gains** (13). $d(a,b)$ is the product, along the unique path of $G$ from $a$ to $b$, of the weight $\mu_{ij}$ for each class-to-pool step $i\to j$ and $1/\mu_{ij}$ for each pool-to-class step $j\to i$. Thus $d(i,j)=\mu_{i_1j_1}\prod_k\mu_{i_{k+1}j_{k+1}}/\mu_{i_{k+1}j_k}$, $d(i,i')=\prod_k\mu_{i_kj_k}/\mu_{i_{k+1}j_k}$ and $d(i,i)=1$.
--   5. The map $\Psi$ of (37). $\Psi(\alpha,\beta)$ is the unique $z$ supported on the edges with row sums $\alpha$ and column sums $\beta$.
--   6. The drift (42), $b_i(x,u)=h_i-\sum_{j}\mu_{ij}\breve\Psi_{ij}[u](x)$ with $\breve\Psi[u](x)=\Psi(x-\langle e,x\rangle^+u^c,\,-\langle e,x\rangle^-u^s)$, for control values $u=(u^c,u^s)\in\Delta_I\times\Delta_J$. It is written with a general constant vector in place of $h$, so that the recentred drift with $-\vartheta_p p$ in place of $h$ is the same object.
--   7. For a pool $\hat\jmath$, the matrices $B_1\in\mathbb R^{I\times I}$ and $B_2\in\mathbb R^{I\times J}$ of (38). Column $k$ of $B_1$ is $M\Psi(e_k,e_{\hat\jmath})$ and column $\ell$ of $B_2$ is $M\Psi(0,e_\ell-e_{\hat\jmath})$, where $(Mz)_i=\sum_j\mu_{ij}z_{ij}$. This is (38) in the basis $(\alpha,(\beta)_{-\hat\jmath})$ of $D=\{\langle e,\alpha\rangle=\langle e,\beta\rangle\}$.
--   8. The constant control value $\bar v=(e_{\hat\imath},e_{\hat\jmath})$ of (56).
--
--   These objects are what Theorems 1–5 and 7 of the paper are stated in.
--
--   **Formalization Note** Classes are `Fin I` and pools `Fin J` (class $i$ is index $i-1$). The tree is Mathlib's `SimpleGraph.IsTree` on `Fin I ⊕ Fin J`. Edge-indexed arrays are functions `Fin I → Fin J → ℝ`. The values of $\mu$, $\hat\mu$ off the edges are irrelevant, since they are always multiplied by something that vanishes there. $\vartheta_p$ is the supremum of the feasible values of (LP′) (Theorem 2 shows the supremum is attained). $\Psi(\alpha,\beta)$ is chosen as the unique solution of (37) when there is one and is $0$ otherwise; Atar's Proposition A.2 says a solution exists exactly on $D$. The gains are computed along the path supplied by `IsTree.existsUnique_path`.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, pp. 5–6 ((1)–(4), (LP)), p. 8 (Definition 1, (LP′)), p. 9 ((12)), p. 10 ((13)), p. 16 ((34)), pp. 17–18 ((37), (38), (40), (42)), p. 25 ((56))

import Mathlib
import Definitions.Def_EthierKurtz_SDEState

open Matrix
open scoped BigOperators

namespace SWSSNet.Diffusion

/-!
Hmedi, Arapostathis & Pang, *On System-Wide Safety Staffing of Large-Scale Parallel Server
Networks*, arXiv:2009.01942v3, §2 (pp. 5–8), §3 (p. 10) and §4 (pp. 16–18): the multiclass
multi-pool tree network in the Halfin–Whitt limit, the CRP solution `ξ*`, `z*`, `θ`, the SWSS
value `ϑ_p` of (LP′), the vector `h` of (12), the path gains `d` of (13), the map `Ψ` of (37), the
drift (42), and the matrices `B₁`, `B₂` of (38) for a chosen pool `ĵ`.

Classes are `Fin I` and pools `Fin J` (the paper's class `i` is index `i − 1`).
-/

/-- The bipartite class–pool graph `G = (I ∪ J, E)` of p. 5 on the vertex type `Fin I ⊕ Fin J`:
class `i` and pool `j` are adjacent iff `adj i j` (i.e. `i ∼ j`); no two classes and no two pools
are adjacent. -/
def bipGraph {I J : ℕ} (adj : Fin I → Fin J → Prop) : SimpleGraph (Fin I ⊕ Fin J) :=
  SimpleGraph.fromRel fun a b => ∃ i j, a = Sum.inl i ∧ b = Sum.inr j ∧ adj i j

/-- Feasibility for the linear program (LP) of p. 6: `ξ ∈ ℝ^G_+` (nonnegative, zero off the
edges) and `∑_j µ_ij ν_j ξ_ij = λ_i` for every class `i`. -/
def IsLPFeasible {I J : ℕ} (adj : Fin I → Fin J → Prop) (lam : Fin I → ℝ) (nu : Fin J → ℝ)
    (mu : Fin I → Fin J → ℝ) (ξ : Fin I → Fin J → ℝ) : Prop :=
  (∀ i j, ¬ adj i j → ξ i j = 0) ∧ (∀ i j, 0 ≤ ξ i j) ∧
    ∀ i, ∑ j, mu i j * nu j * ξ i j = lam i

/-- The objective of (LP): the maximal pool load `max_j ∑_i ξ_ij`. -/
noncomputable def maxLoad {I J : ℕ} (ξ : Fin I → Fin J → ℝ) : ℝ :=
  ⨆ j, ∑ i, ξ i j

/-- The complete resource pooling condition (p. 6): `ξ` is the unique solution of (LP) and satisfies
(3), i.e. `∑_i ξ_ij = 1` for every pool `j` and `ξ_ij > 0` on every edge. -/
def IsCRPSolution {I J : ℕ} (adj : Fin I → Fin J → Prop) (lam : Fin I → ℝ) (nu : Fin J → ℝ)
    (mu : Fin I → Fin J → ℝ) (ξ : Fin I → Fin J → ℝ) : Prop :=
  IsLPFeasible adj lam nu mu ξ ∧
    (∀ ξ', IsLPFeasible adj lam nu mu ξ' → maxLoad ξ ≤ maxLoad ξ') ∧
    (∀ ξ', IsLPFeasible adj lam nu mu ξ' → maxLoad ξ' ≤ maxLoad ξ → ξ' = ξ) ∧
    (∀ j, ∑ i, ξ i j = 1) ∧
    (∀ i j, adj i j → 0 < ξ i j)

/-- A multiclass multi-pool Markovian network in the Halfin–Whitt limit (pp. 5–6): the class–pool
graph is a tree; the first-order limits (1) `λ_i > 0`, `ν_j > 0`, `µ_ij > 0` (`i ∼ j`); the
second-order limits (2) `λ̂_i, ν̂_j, µ̂_ij ∈ ℝ`; and the CRP solution `ξ*` of (LP) with (3).
Values of `mu`, `muHat` off the edges are irrelevant (every use multiplies them by a quantity that
vanishes off the edges). -/
structure TreeNetwork (I J : ℕ) where
  /-- the compatibility relation `i ∼ j` (`j ∈ J(i)`) -/
  adj : Fin I → Fin J → Prop
  /-- the graph `G` is a tree -/
  isTree : (bipGraph adj).IsTree
  /-- `λ_i` -/
  lam : Fin I → ℝ
  /-- `ν_j` -/
  nu : Fin J → ℝ
  /-- `µ_ij` -/
  mu : Fin I → Fin J → ℝ
  /-- `λ̂_i` -/
  lamHat : Fin I → ℝ
  /-- `ν̂_j` -/
  nuHat : Fin J → ℝ
  /-- `µ̂_ij` -/
  muHat : Fin I → Fin J → ℝ
  /-- the CRP solution `ξ*` -/
  xi : Fin I → Fin J → ℝ
  lam_pos : ∀ i, 0 < lam i
  nu_pos : ∀ j, 0 < nu j
  mu_pos : ∀ i j, adj i j → 0 < mu i j
  xi_crp : IsCRPSolution adj lam nu mu xi

variable {I J : ℕ}

/-- `z*_ij := ξ*_ij ν_j` of (4). -/
def zStar (N : TreeNetwork I J) (i : Fin I) (j : Fin J) : ℝ :=
  N.xi i j * N.nu j

/-- `θ_j := ν̂_j + ∑_{i ∈ I(j)} (µ̂_ij/µ_ij) z*_ij` (Definition 1, p. 8); the terms with `i ≁ j`
vanish because `z*_ij = 0` there. -/
noncomputable def theta (N : TreeNetwork I J) (j : Fin J) : ℝ :=
  N.nuHat j + ∑ i, N.muHat i j / N.mu i j * zStar N i j

/-- `h_i := λ̂_i − ∑_{j ∈ J(i)} (µ_ij ξ*_ij ν̂_j + µ̂_ij z*_ij)` of (12), p. 9 (the terms with
`i ≁ j` vanish). -/
def hvec (N : TreeNetwork I J) (i : Fin I) : ℝ :=
  N.lamHat i - ∑ j, (N.mu i j * N.xi i j * N.nuHat j + N.muHat i j * zStar N i j)

/-- `p` is a positive probability vector: `p ∈ ∆_I` with `p_i > 0` for all `i`. -/
def IsPosProb (p : Fin I → ℝ) : Prop :=
  (∀ i, 0 < p i) ∧ ∑ i, p i = 1

/-- `ϑ` is a feasible value of the linear program (LP′) of Definition 1, p. 8: there is
`κ ∈ ℝ^G` (zero off the edges) with `λ̂_i ≤ ∑_{j ∈ J(i)} µ_ij κ_ij − ϑ p_i` for every class `i`
and `∑_{i ∈ I(j)} κ_ij = θ_j` for every pool `j`. -/
def lpFeasible (N : TreeNetwork I J) (p : Fin I → ℝ) (ϑ : ℝ) : Prop :=
  ∃ κ : Fin I → Fin J → ℝ, (∀ i j, ¬ N.adj i j → κ i j = 0) ∧
    (∀ i, N.lamHat i ≤ ∑ j, N.mu i j * κ i j - ϑ * p i) ∧
    ∀ j, ∑ i, κ i j = theta N j

/-- The SWSS parameter `ϑ_p` (Definition 1, p. 8): the optimal value of (LP′), i.e. the supremum of
its feasible values. -/
noncomputable def swss (N : TreeNetwork I J) (p : Fin I → ℝ) : ℝ :=
  sSup {ϑ | lpFeasible N p ϑ}

/-- The weight of a step along the tree used by the gains (13): a class-to-pool step `i → j` weighs
`µ_ij`, a pool-to-class step `j → i` weighs `1/µ_ij` (other steps do not occur in `G`). -/
noncomputable def stepWeight (N : TreeNetwork I J) : (Fin I ⊕ Fin J) → (Fin I ⊕ Fin J) → ℝ
  | Sum.inl i, Sum.inr j => N.mu i j
  | Sum.inr j, Sum.inl i => 1 / N.mu i j
  | _, _ => 1

/-- The unique path in the tree `G` from `a` to `b`. -/
noncomputable def treePath (N : TreeNetwork I J) (a b : Fin I ⊕ Fin J) : (bipGraph N.adj).Walk a b :=
  (N.isTree.existsUnique_path a b).exists.choose

/-- The gain (13), p. 10: the product of the step weights along the unique path from `a` to `b`.
For a class `i` and a pool `j`, `gain N (inl i) (inr j)` is `d(i,j) = µ_{i₁j₁} ∏ µ_{i_{k+1}j_{k+1}}/µ_{i_{k+1}j_k}`;
for classes `i, i'`, `gain N (inl i) (inl i')` is `d(i,i') = ∏ µ_{i_kj_k}/µ_{i_{k+1}j_k}`, and
`d(i,i) = 1` (empty path). -/
noncomputable def gain (N : TreeNetwork I J) (a b : Fin I ⊕ Fin J) : ℝ :=
  ((treePath N a b).darts.map fun d => stepWeight N d.fst d.snd).prod

/-- `z` solves (37) for `(α, β)`: `z_ij = 0` for `i ≁ j`, `∑_j z_ij = α_i` for every class and
`∑_i z_ij = β_j` for every pool. -/
def IsFlow (N : TreeNetwork I J) (α : Fin I → ℝ) (β : Fin J → ℝ) (z : Fin I → Fin J → ℝ) : Prop :=
  (∀ i j, ¬ N.adj i j → z i j = 0) ∧ (∀ i, ∑ j, z i j = α i) ∧ ∀ j, ∑ i, z i j = β j

/-- The map `Ψ` of (37), p. 17: the unique solution of (37) when it exists (for a tree this is the
case exactly on `D = {⟨e,α⟩ = ⟨e,β⟩}`), and `0` otherwise. -/
noncomputable def flowMap (N : TreeNetwork I J) (α : Fin I → ℝ) (β : Fin J → ℝ) :
    Fin I → Fin J → ℝ := by
  classical
  exact if h : ∃! z, IsFlow N α β z then h.exists.choose else 0

/-- A control value `u = (u^c, u^s) ∈ U = ∆_I × ∆_J` of (34), p. 16. -/
def IsControlValue (u : (Fin I → ℝ) × (Fin J → ℝ)) : Prop :=
  u.1 ∈ stdSimplex ℝ (Fin I) ∧ u.2 ∈ stdSimplex ℝ (Fin J)

/-- The drift (42), p. 18, with the constant vector `h` replaced by a parameter `hv`:
`b_i(x,u) = hv_i − ∑_{j ∈ J(i)} µ_ij Ψ̆_ij[u](x)`, where
`Ψ̆[u](x) = Ψ(x − ⟨e,x⟩⁺u^c, −⟨e,x⟩⁻u^s)` is (40). With `hv = h` of (12) this is the paper's `b`;
with `hv = −ϑ_p p` it is the recentred drift `b̃` of pp. 24–28. -/
noncomputable def driftH (N : TreeNetwork I J) (hv : Fin I → ℝ) (u : (Fin I → ℝ) × (Fin J → ℝ))
    (x : EthierKurtz.SDEState I) : EthierKurtz.SDEState I :=
  WithLp.toLp 2 fun i => hv i - ∑ j, N.mu i j *
    flowMap N (fun k => x k - max (∑ l, x l) 0 * u.1 k)
      (fun l => -(max (-(∑ k, x k)) 0 * u.2 l)) i j

/-- The matrix `B₁` of (38) and Proposition 2 for the pool `ĵ`: eliminating `β_ĵ` from the basis
`(α, (β)_{−ĵ})` of `D`, its column `k` is `MΨ(e_k, e_ĵ)`, i.e.
`(B₁)_{ik} = ∑_j µ_ij Ψ_ij(e_k, e_ĵ)`. -/
noncomputable def B1 (N : TreeNetwork I J) (ĵ : Fin J) : Matrix (Fin I) (Fin I) ℝ :=
  fun i k => ∑ j, N.mu i j * flowMap N (Pi.single k 1) (Pi.single ĵ 1) i j

/-- The matrix `B₂` of (38) and Proposition 2 for the pool `ĵ`: its column `l` is
`MΨ(0, e_l − e_ĵ)`, so `B₁α + B₂β = MΨ(α, β)` on `D` and column `ĵ` vanishes. -/
noncomputable def B2 (N : TreeNetwork I J) (ĵ : Fin J) : Matrix (Fin I) (Fin J) ℝ :=
  fun i l => ∑ j, N.mu i j * flowMap N 0 (Pi.single l 1 - Pi.single ĵ 1) i j

/-- The constant control value `v̄ = (e_ı̂, e_ĵ)` of (56), p. 25. -/
noncomputable def constCtrl (î : Fin I) (ĵ : Fin J) : (Fin I → ℝ) × (Fin J → ℝ) :=
  (Pi.single î 1, Pi.single ĵ 1)

end SWSSNet.Diffusion


