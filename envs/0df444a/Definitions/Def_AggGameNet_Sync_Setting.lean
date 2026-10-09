-- Prove2me | Definitions.Def_AggGameNet_Sync_Setting
-- name    : AggGameNet_Sync_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:30.186996+00:00
-- url     : https://prove2.me/theorems/c6b55500-4f5d-4f2c-b191-4ad307c974b6
-- title:
--   Assumptions 1–6 and (5)–(12), pp. 6–9 — the aggregate map φ, the synchronous scheme, y^k, Φ(k,s), θ and β
-- statement:
--   Let $F_i(x_i,u)$ be the gradient map of player $i$ (in the paper $F_i(x_i,\bar x)=\nabla_{x_i}f_i(x_i,\bar x)$, equation (6)). The game's map is $\phi_i(x)=F_i\big(x_i,\sum_{j}x_j\big)$ (equation (8)), and $\mathrm{VI}(K,\phi)$ is the variational inequality on $K=\prod_iK_i$. The definition fixes the paper's standing assumptions:
--
--   1. **Assumption 1** (set and continuity part): each $K_i$ is nonempty, compact and convex, and $(x_i,u)\mapsto F_i(x_i,u)$ is continuous on $K_i\times\bar K$.
--   2. **Assumption 2**: $\phi$ is strictly monotone over $K$: $\sum_i(\phi_i(x)-\phi_i(x'))^\top(x_i-x_i')>0$ for all $x\neq x'$ in $K$.
--   3. **Assumption 3**: there are constants $\bar L_i>0$ with $\|F_i(x_i,z_1)-F_i(x_i,z_2)\|\le\bar L_i\|z_1-z_2\|$ for all $x_i\in K_i$ and all $z_1,z_2\in\mathbb R^n$.
--   4. **Assumption 4**: for the given integer $Q\ge1$, the graph with edge set $\bigcup_{\ell=1}^{Q}\mathcal E_{\ell+k}$ is connected for every $k\ge0$. The neighbourhood $\mathcal N_i(k)=\{j:\{i,j\}\in\mathcal E_k\}$ always contains $i$.
--   5. **Assumption 5**: $w_{ij}(k)\ge\delta$ for $j\in\mathcal N_i(k)$, $w_{ij}(k)=0$ otherwise, and every row and every column of $W(k)$ sums to $1$.
--   6. **Assumption 6**: $\alpha_{k+1}\le\alpha_k$, $\sum_k\alpha_k=\infty$ and $\sum_k\alpha_k^2<\infty$.
--
--   The synchronous scheme starts from $x_i^0\in K_i$, $v_i^0=x_i^0$, and for $k\ge0$ sets
--
--   $$
--   \hat v_i^k=\sum_{j=1}^N w_{ij}(k)\,v_j^k,\qquad x_i^{k+1}=\Pi_{K_i}\big[x_i^k-\alpha_kF_i(x_i^k,N\hat v_i^k)\big],\qquad v_i^{k+1}=\hat v_i^k+x_i^{k+1}-x_i^k ,
--   $$
--
--   equations (9)–(11), where $\Pi_{K_i}$ is the Euclidean projection. It also defines the mean estimate $y^k=\frac1N\sum_iv_i^k$ of (12), the transition matrices $\Phi(k,s)=W(k)W(k-1)\cdots W(s)$ for $k\ge s$, and the constants of Lemma 1,
--
--   $$
--   \theta=\Big(1-\frac{\delta}{4N^2}\Big)^{-2},\qquad \beta=\Big(1-\frac{\delta}{4N^2}\Big)^{1/Q}.
--   $$
--
--   These are the hypotheses and the iteration that Lemmas 1–6 and Proposition 2 are about.
--
--   **Formalization Note** Only $F_i$ enters the algorithm, so it is taken as primitive data; Assumption 1's differentiability and convexity of $f_i$ are used only to identify Nash equilibria with VI solutions and are represented here by continuity of $F_i$ on $K_i\times\bar K$. Nonemptiness of $K_i$ is implicit in the paper (it draws $x_i^0\in K_i$). Assumption 3 is required for all $z_1,z_2\in\mathbb R^n$ instead of $\bar K$, because (10) evaluates $F_i$ at $N\hat v_i^k$, which can lie outside $\bar K$. The positivity $\delta>0$, implicit in the paper, is a separate hypothesis of every theorem that uses Assumption 5. The integer $Q$ is a parameter of Assumption 4, which the theorems quantify. $\Phi(k,s)$ is indexed as `Phi W s m` $=\Phi(s+m,s)$. The projection is the nearest-point relation `ChanPangGQVI.Shared.IsProj` (a published definition), so a run of the scheme is a relation on sequences; for nonempty closed convex $K_i$ the nearest point exists and is unique, so the run is determined by $x^0$. Iterations start at $k=0$ and players are indexed from $0$.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, (5)–(8) and Assumptions 1–3, pp. 6–7; Assumptions 4–6, (9)–(12), Φ(k,s) and Lemma 1's θ, β, pp. 7–9

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_Projection
import Definitions.Def_AggGameNet_Sync_Game

namespace AggGameNet.Sync

open Filter

/-- The aggregate gradient map in (5)–(8). -/
def phi {N n : ℕ} (F : Fin N → E n → E n → E n)
    (x : Fin N → E n) : Fin N → E n :=
  fun i => F i (x i) (∑ j, x j)

/-- `VI(K, φ)` with `φ(x) = F(x, Σⱼ xⱼ)`. -/
def IsVISol {N n : ℕ} (K : Fin N → Set (E n))
    (F : Fin N → E n → E n → E n) (xs : Fin N → E n) : Prop :=
  IsVI K (phi F) xs

/-- Assumption 1's set conditions and the continuity of the coordinate map. -/
def Assumption1 {N n : ℕ} (K : Fin N → Set (E n))
    (F : Fin N → E n → E n → E n) : Prop :=
  (∀ i, (K i).Nonempty ∧ IsCompact (K i) ∧ Convex ℝ (K i)) ∧
    ∀ i, ContinuousOn (fun q : E n × E n => F i q.1 q.2) (K i ×ˢ Kbar K)

/-- Assumption 2: strict monotonicity on feasible profiles. -/
def Assumption2 {N n : ℕ} (K : Fin N → Set (E n))
    (F : Fin N → E n → E n → E n) : Prop :=
  ∀ x x' : Fin N → E n, (∀ i, x i ∈ K i) → (∀ i, x' i ∈ K i) →
    x ≠ x' → 0 < ∑ i, inner ℝ (phi F x i - phi F x' i) (x i - x' i)

/-- Assumption 3, extended to all aggregate arguments as needed by (10). -/
def Assumption3 {N n : ℕ} (K : Fin N → Set (E n))
    (F : Fin N → E n → E n → E n) (Lbar : Fin N → ℝ) : Prop :=
  (∀ i, 0 < Lbar i) ∧
    ∀ i, ∀ xi ∈ K i, ∀ z1 z2 : E n,
      ‖F i xi z1 - F i xi z2‖ ≤ Lbar i * ‖z1 - z2‖

/-- The neighbour relation includes each agent itself. -/
def nbr {N : ℕ} (G : ℕ → SimpleGraph (Fin N)) (k : ℕ) (i j : Fin N) : Prop :=
  j = i ∨ (G k).Adj i j

/-- Assumption 4: every consecutive `Q`-window has connected edge union. -/
def Assumption4 {N : ℕ} (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) : Prop :=
  1 ≤ Q ∧ ∀ k, (⨆ ℓ ∈ Finset.Icc 1 Q, G (ℓ + k)).Connected

/-- Assumption 5: supported positive weights with unit row and column sums. -/
def Assumption5 {N : ℕ} (G : ℕ → SimpleGraph (Fin N))
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ) : Prop :=
  ∀ k, (∀ i j, (nbr G k i j → δ ≤ W k i j) ∧
      (¬ nbr G k i j → W k i j = 0)) ∧
    (∀ i, ∑ j, W k i j = 1) ∧
    (∀ j, ∑ i, W k i j = 1)

/-- Assumption 6: decreasing steps, divergent sum, square-summability. -/
def Assumption6 (α : ℕ → ℝ) : Prop :=
  Antitone α ∧
    Tendsto (fun T => ∑ k ∈ Finset.range T, α k) atTop atTop ∧
    Summable (fun k => α k ^ 2)

/-- Aligned local estimate (9). -/
def vhat {N n : ℕ} (W : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (v : ℕ → Fin N → E n) (k : ℕ) (i : Fin N) : E n :=
  ∑ j, W k i j • v k j

/-- A run of the synchronous projected-gradient iteration (10)–(11). -/
def IsSyncRun {N n : ℕ} (K : Fin N → Set (E n))
    (F : Fin N → E n → E n → E n)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (α : ℕ → ℝ)
    (x v : ℕ → Fin N → E n) : Prop :=
  (∀ i, x 0 i ∈ K i) ∧ v 0 = x 0 ∧
    ∀ k i, ChanPangGQVI.Shared.IsProj (K i)
      (x k i - α k • F i (x k i) ((N : ℝ) • vhat W v k i))
      (x (k + 1) i) ∧
      v (k + 1) i = vhat W v k i + x (k + 1) i - x k i

/-- The mean estimate (12). -/
noncomputable def yavg {N n : ℕ} (v : ℕ → Fin N → E n) (k : ℕ) : E n :=
  (1 / (N : ℝ)) • ∑ i, v k i

/-- `Phi W s m = W(s+m) ⋯ W(s)`. -/
noncomputable def Phi {N : ℕ} (W : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (s : ℕ) : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => W s
  | m + 1 => W (s + m + 1) * Phi W s m

/-- The paper's mixing prefactor `θ`. -/
noncomputable def theta (N : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ / (4 * (N : ℝ) ^ 2)) ^ (-2 : ℤ)

/-- The paper's mixing base `β`. -/
noncomputable def beta (N Q : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ / (4 * (N : ℝ) ^ 2)) ^ ((1 : ℝ) / (Q : ℝ))

end AggGameNet.Sync


