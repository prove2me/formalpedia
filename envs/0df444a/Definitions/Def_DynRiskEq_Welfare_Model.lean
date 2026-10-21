-- Prove2me | Definitions.Def_DynRiskEq_Welfare_Model
-- name    : DynRiskEq_Welfare_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:57.36524+00:00
-- url     : https://prove2.me/theorems/4de2565d-585c-4ffd-bffc-db2474b7bebc
-- title:
--   §3–§5, pp. 5, 8, 10, 12–14 — scenario-tree market with storage, polyhedral risk sets, Z_a (18), AE_a (20), RTE (Definition 3), social risk set (Definition 1), SE(D)
-- statement:
--   This file sets up the multistage market of Ferris and Philpott, *Dynamic risked equilibrium*.
--
--   **The tree.** Uncertainty is a finite scenario tree $\mathcal N$ with root $0$. For a node $n$, $n_-$ is its parent and $n_+$ its set of children; the leaves $\mathcal L$ are the nodes without children.
--
--   **The agents.** A finite set $\mathcal A$ of agents. Agent $a$ chooses at each node $n$ a release vector $u_a(n)\in\mathbb R^{d_U(a)}$ and a storage vector $x_a(n)\in\mathbb R^{d_X(a)}$. Its data are a cost (or consumption disbenefit) $C_a$, a production function $g_a$, a terminal value of storage $V_a$, matrices $T_{ab}$ that turn releases of agent $b$ into storage of agent $a$, random supplies $\omega_a(n)$, an initial storage $x_a(0_-)$, and constraint sets $\mathcal U_a$, $\mathcal X_a$.
--
--   **Risk sets.** At each non-leaf node $n$, agent $a$ has finitely many generators $p^k_a(n)$, $k\in\mathcal K_a(n)$, and its polyhedral risk set is
--   $$\mathcal D_a(n)=\operatorname{conv}\{[p^k_a]_{n_+} : k\in\mathcal K_a(n)\},$$
--   a set of vectors indexed by the children of $n$; $[\mu]_{n_+}$ denotes the restriction of a node-indexed vector $\mu$ to $n_+$. The social planning risk set (Definition 1) is $\mathcal D_s(n)=\bigcap_{a\in\mathcal A}\mathcal D_a(n)$. The predicate *ProbGenerators* says that every generator is a probability vector on $n_+$.
--
--   **Optimality conditions.** For a function $f$, a set $S$ and a point $v$, "$0\in\nabla f(v)+N_S(v)$" means $v\in S$, $f$ has a gradient $w$ at $v$, and $-w$ lies in the normal cone $N_S(v)=\{d: d^\top(s-v)\le 0\ \forall s\in S\}$. Complementarity $0\le y\perp z\ge 0$ means $y\ge 0$, $z\ge 0$, $yz=0$; for vectors it is componentwise.
--
--   **Agent problem.** Given prices $\pi(n)$ (product), $\alpha_a(n)$ (storage) and $\mu(m)$ (Arrow–Debreu security paying $1$ in node $m$), and security holdings $W_a(m)$, the disbenefit (18) is
--   $$Z_a(n;u,x,W)=C_a(u_a(n))-\pi(n)g_a(u_a(n))+\alpha_a(n)^\top(x_a(n)-x_a(n_-)-\omega_a(n))-\sum_{b\in\mathcal A}\alpha_b(n)^\top T_{ba}u_a(n)+\sum_{m\in n_+}\mu(m)W_a(m).$$
--   $\mathrm{AE}_a(\pi,\alpha,\mu,\mathcal D_a)$ is the system (20a)–(20g) of p. 13 in the unknowns $(u_a,x_a,W_a,\theta_a,\gamma)$: the multipliers $\gamma^k(n)$ sum to one; $0\le\gamma^k(n)\perp\theta_a(n)-\sum_{m\in n_+}p^k_a(m)\big(Z_a(m;u,x,W)-W_a(m)+\theta_a(m)\big)\ge0$; $\theta_a(n)=-V_a(x_a(n))$ at leaves; stationarity of $Z_a(n;\cdot)$ in $u_a(n)$ over $\mathcal U_a$; the storage conditions (20e), (20f); and $\mu(m)=\sum_k\gamma^k(n)p^k_a(m)$ for $m\in n_+$.
--
--   **Equilibrium.** A multistage risk-trading equilibrium RTE$(\mathcal D_{\mathcal A})$ (Definition 3) is a family of prices and actions such that every agent solves $\mathrm{AE}_a$ with its own multipliers, and the markets clear:
--   $$0\le\pi(n)\perp\sum_a g_a(u_a(n))\ge0,\quad 0\le\alpha_a(n)\perp -x_a(n)+x_a(n_-)+\sum_b T_{ab}u_b(n)+\omega_a(n)\ge0,\quad 0\le\mu(n)\perp-\sum_aW_a(n)\ge0\ (n\neq0).$$
--
--   **Social planning system.** For a risk set given by generators $p^k(n)$, SE$(\mathcal D)$ is the eight-line complementarity system of p. 10 in $(u,x,\theta,\gamma,\pi,\alpha)$, the social analogue of $\mathrm{AE}_a$ with $\sum_aC_a$ as the stage cost and $-\sum_aV_a$ as terminal value. $\bar\theta(n)=\sum_a\theta_a(n)$.
--
--   These are the objects of the paper's First Welfare Theorem (Theorem 3).
--
--   **Formalization Note.** The tree is the platform's `StochasticProg.Multistage.Tree` ($n_+$ = `children n`, $n_-$ = `anc n`, root = `root`), and a leaf is a node with no children. Vectors live in `EuclideanSpace ℝ (Fin d)` and $T_{ab}$ acts through `Matrix.toEuclideanLin`. Prices $\mu$ and holdings $W_a$ are functions on all nodes; only their values at non-root nodes are used. Risk sets are convex hulls of an arbitrary finite generating family (the paper speaks of the extreme points; every generating family gives the same hull). Gradients are required to exist (`HasGradientAt`), and every normal-cone condition includes membership of the point in its set, since the platform normal cone does not. The parent of the root is replaced by given initial storage $x_a(0_-)$. In (20d) the gradient is taken in the variable $u_a(n)$ alone, by substituting $v$ for $u_a(n)$ in $Z_a(n;u,x,W)$.
-- source:
--   Ferris & Philpott, Dynamic risked equilibrium, author's manuscript of April 16, 2018 (Oper. Res. 2022, doi:10.1287/opre.2019.1958), pp. 3, 5, 8, 10, 12–14: risk sets (p. 3, p. 8), SE(D) (p. 10), Assumption 3 and Definition 1 (p. 12), (18) (p. 12), (20a)–(20g) (p. 13), Definition 3 with (21)–(23) (p. 14)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

namespace DynRiskEq.Welfare

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

/-- Real vectors of dimension `d` (releases, storages, prices of storages). -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

section Tree

variable {H : ℕ} (T : Tree H)

/-- `n ∈ ℒ` (p. 5): a leaf of the scenario tree is a node without children. The paper's
`n+` is `T.children n`, its `n−` is `T.anc n`, and its root node `0` is `T.root`. -/
def IsLeaf (n : T.Node) : Prop := T.children n = ∅

/-- `[μ]_{n+}` (p. 3): the restriction of a node-indexed vector to the children of `n`. -/
def restrictChildren (μ : T.Node → ℝ) (n : T.Node) : ↥(T.children n) → ℝ :=
  fun m => μ m

/-- Polyhedral risk set at node `n` (p. 8): `𝒟(n) = conv{[p^k]_{n+}, k ∈ 𝒦(n)}`, where the
generators of node `n` are `p n k : T.Node → ℝ`, `k : Fin (K n)`, read only on `n+`. -/
def riskSet (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ) (n : T.Node) :
    Set (↥(T.children n) → ℝ) :=
  convexHull ℝ (Set.range fun k : Fin (K n) => restrictChildren T (p n k) n)

/-- `[μ]_{n+} ∈ 𝒟(n)`. -/
def InRisk (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ) (n : T.Node)
    (μ : T.Node → ℝ) : Prop :=
  restrictChildren T μ n ∈ riskSet T K p n

/-- The generators of every non-leaf node are probability vectors on its children
(risk sets are sets of probability measures, p. 3). -/
def ProbGenerators (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ) : Prop :=
  ∀ n, ¬ IsLeaf T n → ∀ k : Fin (K n),
    (∀ m ∈ T.children n, 0 ≤ p n k m) ∧ ∑ m ∈ T.children n, p n k m = 1

/-- Definition 1 (p. 12): the social planning risk set `𝒟_s(n) = ⋂_{a ∈ 𝒜} 𝒟_a(n)`. -/
def socialRiskSet {A : Type} (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ) (n : T.Node) :
    Set (↥(T.children n) → ℝ) :=
  ⋂ a, riskSet T (Ka a) (pa a) n

end Tree

/-- `0 ∈ ∇f(v) + N_S(v)` (p. 8): `v ∈ S`, `f` has a gradient `w` at `v`, and `-w ∈ N_S(v)`. -/
def Stationary {d : ℕ} (f : Vec d → ℝ) (S : Set (Vec d)) (v : Vec d) : Prop :=
  v ∈ S ∧ ∃ w, HasGradientAt f w v ∧ -w ∈ normalCone S v

/-- `0 ∈ y + N_S(v)`, with `v ∈ S`. -/
def InNormal {d : ℕ} (y : Vec d) (S : Set (Vec d)) (v : Vec d) : Prop :=
  v ∈ S ∧ -y ∈ normalCone S v

/-- Complementarity `0 ≤ y ⊥ z ≥ 0` of two reals. -/
def Compl (y z : ℝ) : Prop := 0 ≤ y ∧ 0 ≤ z ∧ y * z = 0

/-- The agents' data (p. 8). Agent `a` releases `u ∈ ℝ^{dU a}` and stores `x ∈ ℝ^{dX a}`;
`C a` is its cost/disbenefit, `g a` its production, `V a` its terminal value of storage,
`Tm a b = T_ab` maps releases of `b` to storage of `a`, `ω a n` is the random supply at node `n`,
`x0 a` is the initial storage `x_a(0−)`, and `U a`, `X a` are the sets `𝒰_a`, `𝒳_a`. -/
structure Market {H : ℕ} (T : Tree H) (A : Type) where
  dU : A → ℕ
  dX : A → ℕ
  C : (a : A) → Vec (dU a) → ℝ
  g : (a : A) → Vec (dU a) → ℝ
  V : (a : A) → Vec (dX a) → ℝ
  Tm : (a b : A) → Matrix (Fin (dX a)) (Fin (dU b)) ℝ
  ω : (a : A) → T.Node → Vec (dX a)
  x0 : (a : A) → Vec (dX a)
  U : (a : A) → Set (Vec (dU a))
  X : (a : A) → Set (Vec (dX a))

section Market

variable {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]

/-- `x_a(n−)`, with `x_a(0−) := x0 a` at the root. -/
def prevStore (M : Market T A) (x : (a : A) → T.Node → Vec (M.dX a)) (a : A) (n : T.Node) :
    Vec (M.dX a) :=
  if n = T.root then M.x0 a else x a (T.anc n)

/-- The agent's disbenefit (18), p. 12:
`Z_a(n; u, x, W) = C_a(u_a(n)) − π(n) g_a(u_a(n)) + α_a(n)ᵀ(x_a(n) − x_a(n−) − ω_a(n))
 − Σ_b α_b(n)ᵀ T_ba u_a(n) + Σ_{m ∈ n+} μ(m) W_a(m)`. -/
noncomputable def Z (M : Market T A) (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a))
    (μ : T.Node → ℝ) (u : (a : A) → T.Node → Vec (M.dU a))
    (x : (a : A) → T.Node → Vec (M.dX a)) (W : A → T.Node → ℝ) (a : A) (n : T.Node) : ℝ :=
  M.C a (u a n) - π n * M.g a (u a n)
    + ⟪α a n, x a n - prevStore T M x a n - M.ω a n⟫
    - ∑ b, ⟪α b n, Matrix.toEuclideanLin (M.Tm b a) (u a n)⟫
    + ∑ m ∈ T.children n, μ m * W a m

/-- `AE_a(π, α, μ, 𝒟_a)`, (20a)–(20g) on p. 13, for agent `a` with risk generators `(K, p)`,
policy `(u_a, x_a, W_a, θ_a)` and multipliers `γ`. In (20d) the gradient is taken in the variable
`u_a(n)` alone: `Z_a(n; ·)` with `u_a(n)` replaced by `v`. -/
def AE (M : Market T A) (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ) (a : A) (γ : (n : T.Node) → Fin (K n) → ℝ) :
    Prop :=
  -- (20a)
  (∀ n, ¬ IsLeaf T n → 0 = 1 - ∑ k, γ n k) ∧
  -- (20b)
  (∀ n, ¬ IsLeaf T n → ∀ k, Compl (γ n k)
      (θa a n - ∑ m ∈ T.children n,
        p n k m * (Z T M π α μ u x W a m - W a m + θa a m))) ∧
  -- (20c)
  (∀ n, IsLeaf T n → θa a n = - M.V a (x a n)) ∧
  -- (20d)
  (∀ n, Stationary (fun v => Z T M π α μ (Function.update u a (Function.update (u a) n v)) x W a n)
      (M.U a) (u a n)) ∧
  -- (20e)
  (∀ n, ¬ IsLeaf T n →
      InNormal (α a n - ∑ m ∈ T.children n, μ m • α a m) (M.X a) (x a n)) ∧
  -- (20f)
  (∀ n, IsLeaf T n → ∃ w, HasGradientAt (M.V a) w (x a n) ∧ InNormal (α a n - w) (M.X a) (x a n)) ∧
  -- (20g)
  (∀ n, ¬ IsLeaf T n → ∀ m ∈ T.children n, 0 = μ m - ∑ k, γ n k * p n k m)

/-- The storage slack `−x_a(n) + x_a(n−) + Σ_b T_ab u_b(n) + ω_a(n)` of (22) and SE. -/
noncomputable def storageSlack (M : Market T A) (u : (a : A) → T.Node → Vec (M.dU a))
    (x : (a : A) → T.Node → Vec (M.dX a)) (a : A) (n : T.Node) : Vec (M.dX a) :=
  -x a n + prevStore T M x a n + ∑ b, Matrix.toEuclideanLin (M.Tm a b) (u b n) + M.ω a n

/-- Definition 3 (p. 14), multistage risk-trading equilibrium `RTE(𝒟_𝒜)`: every agent `a`
solves `AE_a(π, α, μ, 𝒟_a)` (with its own multipliers `γ`), and (21)–(23) hold; the vector
complementarity (22) is componentwise. -/
def IsRTE (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ) : Prop :=
  (∀ a, ∃ γ, AE T M (Ka a) (pa a) π α μ u x W θa a γ) ∧
  -- (21)
  (∀ n, Compl (π n) (∑ a, M.g a (u a n))) ∧
  -- (22)
  (∀ a n, ∀ i, Compl (α a n i) (storageSlack T M u x a n i)) ∧
  -- (23)
  (∀ n, n ≠ T.root → Compl (μ n) (- ∑ a, W a n))

/-- `θ̄(n) = Σ_{a ∈ 𝒜} θ_a(n)`. -/
def thetaBar (θa : A → T.Node → ℝ) (n : T.Node) : ℝ := ∑ a, θa a n

/-- `SE(𝒟)` (p. 10), all eight lines, for a risk set given by generators `(K, p)`, actions
`(u, x)`, value `θ`, multipliers `γ` and prices `(π, α)`. -/
def SE (M : Market T A) (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (θ : T.Node → ℝ) (γ : (n : T.Node) → Fin (K n) → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) : Prop :=
  (∀ n, ¬ IsLeaf T n → 0 = 1 - ∑ k, γ n k) ∧
  (∀ n, ¬ IsLeaf T n → ∀ k, Compl (γ n k)
      (θ n - ∑ m ∈ T.children n, p n k m * (∑ a, M.C a (u a m) + θ m))) ∧
  (∀ n, IsLeaf T n → θ n = - ∑ a, M.V a (x a n)) ∧
  (∀ a n, Stationary
      (fun v => M.C a v - π n * M.g a v - ∑ b, ⟪α b n, Matrix.toEuclideanLin (M.Tm b a) v⟫)
      (M.U a) (u a n)) ∧
  (∀ a n, ¬ IsLeaf T n →
      InNormal (α a n - ∑ m ∈ T.children n, ∑ k, (γ n k * p n k m) • α a m) (M.X a) (x a n)) ∧
  (∀ a n, IsLeaf T n →
      ∃ w, HasGradientAt (M.V a) w (x a n) ∧ InNormal (α a n - w) (M.X a) (x a n)) ∧
  (∀ a n, ∀ i, Compl (α a n i) (storageSlack T M u x a n i)) ∧
  (∀ n, Compl (π n) (∑ a, M.g a (u a n)))

end Market

end DynRiskEq.Welfare


