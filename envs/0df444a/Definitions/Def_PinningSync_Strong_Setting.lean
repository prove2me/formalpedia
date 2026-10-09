-- Prove2me | Definitions.Def_PinningSync_Strong_Setting
-- name    : PinningSync_Strong_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:41.244202+00:00
-- url     : https://prove2.me/theorems/9cc15518-b598-479c-8bf6-df727b44fe4f
-- title:
--   (2.2)–(2.8), (3.2)–(3.3), Defs. 2.2–2.4, pp. 1397–1402 — coupling matrix, pinned network and its solutions, synchronization, Assumption 1, connectivity, irreducibility, Ĝ
-- statement:
--   This file fixes the objects of Yu, Chen, Lü and Kurths' pinning-control model of a directed complex network of $N$ identical vertices with states in $\mathbb R^n$.
--
--   1. **Coupling matrix (2.2).** A real $N\times N$ matrix $G=(G_{ij})$ with $G_{ij}\ge 0$ for $i\ne j$ and zero row sums $\sum_{j=1}^N G_{ij}=0$, i.e. $G_{ii}=-\sum_{j\ne i}G_{ij}$. The entry $G_{ij}>0$ means that there is a connection **from vertex $j$ to vertex $i$**.
--   2. **In-degree (Definition 2.2).** $k_i^{\mathrm{in}}=\sum_{j\ne i}G_{ij}$.
--   3. **Strong connectivity (Definition 2.3).** The network has a directed edge $a\to b$ when $a\ne b$ and $G_{ba}>0$; it is strongly connected when for any two distinct vertices $i,j$ there is a directed path (a finite chain of edges) from $i$ to $j$.
--   4. **Irreducibility (Definition 2.4).** $G$ is reducible if there are a permutation $\sigma$ of the vertices (the permutation matrix $P$) and an integer $1\le m\le N-1$ such that $P^TGP$ has a zero upper-right block, i.e. $G_{\sigma(i)\sigma(j)}=0$ whenever $i<m\le j$ (0-based positions). $G$ is irreducible if it is not reducible; in particular every matrix of order $0$ or $1$ is irreducible.
--   5. **Spectral radius and row-sum norm.** $\rho(A)$ is the largest modulus of a complex root of the characteristic polynomial of $A$, and $\|A\|_\infty=\max_i\sum_j|A_{ij}|$.
--   6. **Largest eigenvalue.** For a symmetric matrix $A$, $\lambda_{\max}(A)$ is characterised as the least real $r$ with $v^TAv\le r\,v^Tv$ for every vector $v$ (Rayleigh quotient).
--   7. **Assumption 1 (2.8).** For a vector field $f:\mathbb R^n\times\mathbb R_+\to\mathbb R^n$ and matrices $K,\Gamma\in\mathbb R^{n\times n}$:
--   $$
--   (x-y)^T\bigl(f(x,t)-f(y,t)\bigr)\le (x-y)^TK\Gamma(x-y)\qquad\forall x,y\in\mathbb R^n,\ t\ge 0 .
--   $$
--   8. **Reference trajectory (2.4).** $s:\mathbb R\to\mathbb R^n$ with $\dot s(t)=f(s(t),t)$ for $t\ge 0$.
--   9. **Controlled network (2.5)–(2.6).** With coupling strength $c$, inner coupling matrix $\Gamma$ and control gains $d_i\ge 0$ (vertex $i$ is pinned iff $d_i>0$), a solution $x=(x_1,\dots,x_N)$ satisfies, for $t\ge 0$,
--   $$
--   \dot x_i(t)=f(x_i(t),t)+c\sum_{j=1}^N G_{ij}\Gamma x_j(t)-c\,d_i\Gamma\bigl(x_i(t)-s(t)\bigr).
--   $$
--   10. **Global synchronization (2.7).** $x_i(t)-s(t)\to 0$ as $t\to\infty$ for every $i$.
--   11. **The weighted symmetrisation and the LMI (3.2).** With $\Xi=\operatorname{diag}(\xi_1,\dots,\xi_N)$ and $D=\operatorname{diag}(d_1,\dots,d_N)$, $\widehat G=\tfrac12(\Xi G+G^T\Xi)$ and
--   $$
--   \Xi\otimes\frac{K\Gamma+\Gamma^TK^T}{2}+c\,\widehat G\otimes\frac{\Gamma+\Gamma^T}{2}-c\,(\Xi D)\otimes\frac{\Gamma+\Gamma^T}{2}.
--   $$
--   12. **Error and Lyapunov functional (3.3).** $e_i(t)=x_i(t)-s(t)$, stacked as $e=(e_1^T,\dots,e_N^T)^T$, and $V(t)=\tfrac12\sum_i \xi_i\,e_i(t)^Te_i(t)$.
--
--   These are the shared objects of every statement in the mission.
--
--   **Formalization Note.** States are `Fin n → ℝ`; the convergence (2.7) is stated with the filter `𝓝 0`, which does not depend on the choice of norm on $\mathbb R^n$. Derivatives are `HasDerivWithinAt … (Set.Ici 0)`: two-sided for $t>0$ and from the right at $t=0$. The paper reorders vertices so that the first $l$ are pinned; here pinning is encoded by $d_i>0$ and $D=\operatorname{diag}(d)$ without reordering. Kronecker products are indexed by pairs $(i,a)$ with $(A\otimes B)_{(i,a),(j,b)}=A_{ij}B_{ab}$, and the stacked error uses the same order. $\rho$ and $\|\cdot\|_\infty$ take the value $0$ when $N=0$.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), pp. 1397–1402, (2.2)–(2.8), Definitions 2.2–2.4, p. 1400 (ρ, λ_max), (3.2), (3.3)

import Mathlib

namespace PinningSync.Strong

open Matrix Kronecker Filter Topology

/-- (2.2): `G` is a coupling configuration matrix: nonnegative off-diagonal entries
(`G i j > 0` is a connection from vertex `j` to vertex `i`) and zero row sums
(the diagonal is `G i i = -∑_{j ≠ i} G i j`). -/
def IsCouplingMatrix {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ G i j) ∧ ∀ i, ∑ j, G i j = 0

/-- A directed edge from vertex `a` to vertex `b` of the network of `G` (p. 1397): `a ≠ b`
and `G b a > 0`. -/
def edge {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N) : Prop :=
  a ≠ b ∧ 0 < G b a

/-- Definition 2.3: the network of `G` is strongly connected if between any two distinct
vertices there is a directed path (a chain of edges) from the first to the second. -/
def IsStronglyConnected {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j : Fin N, i ≠ j → Relation.TransGen (edge G) i j

/-- Definition 2.2: the in-degree `k_i^in = ∑_{j ≠ i} G i j` of vertex `i`. -/
def inDegree {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, G i j

/-- Definition 2.4: `G` is reducible if, for some permutation `σ` (the permutation matrix `P`)
and some `1 ≤ m ≤ N - 1`, the block of `PᵀGP` with rows `< m` and columns `≥ m` vanishes,
i.e. `G (σ i) (σ j) = 0` whenever `i < m ≤ j`. -/
def IsReducible {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin N)) (m : ℕ), 1 ≤ m ∧ m ≤ N - 1 ∧
    ∀ i j : Fin N, i.val < m → m ≤ j.val → G (σ i) (σ j) = 0

/-- Definition 2.4: `G` is irreducible if it is not reducible. -/
def IsIrred {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ¬ IsReducible G

/-- The spectral radius `ρ(A)`: the largest modulus of a complex root of the characteristic
polynomial of `A` (a finite set; empty only when `N = 0`, where the value is `0`). -/
noncomputable def specRad {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖z‖) '' {z : ℂ | (A.charpoly.map Complex.ofRealHom).IsRoot z})

/-- The maximum absolute row sum norm `‖A‖∞ = max_i ∑_j |A i j|` (`0` when `N = 0`). -/
noncomputable def infNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ⨆ i, ∑ j, |A i j|

/-- `IsLamMax A r`: `r` is the least real with `vᵀ A v ≤ r vᵀ v` for all `v`; for a symmetric
`A` (of positive dimension) this is `λ_max(A)`, the largest eigenvalue (Rayleigh quotient). -/
def IsLamMax {m : Type*} [Fintype m] (A : Matrix m m ℝ) (r : ℝ) : Prop :=
  IsLeast {r : ℝ | ∀ v : m → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ r * (v ⬝ᵥ v)} r

/-- Assumption 1, (2.8): `(x - y)ᵀ (f(x,t) - f(y,t)) ≤ (x - y)ᵀ K Γ (x - y)` for all
`x, y ∈ ℝⁿ` and all times `t ≥ 0`. -/
def Assumption1 {n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ)) (K Γ : Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x y : Fin n → ℝ,
    (x - y) ⬝ᵥ (f x t - f y t) ≤ (x - y) ⬝ᵥ ((K * Γ) *ᵥ (x - y))

/-- (2.4): `s` is a solution of the isolated vertex, `ṡ(t) = f(s(t), t)` for `t ≥ 0`
(right derivative at `t = 0`). -/
def IsIsolatedSolution {n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ)) (s : ℝ → Fin n → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt s (f (s t) t) (Set.Ici 0) t

/-- (2.5)–(2.6): `x` is a solution of the pinning-controlled network
`ẋ_i = f(x_i, t) + c ∑_j G_ij Γ x_j - c d_i Γ (x_i - s)` for `t ≥ 0`; vertex `i` is pinned
iff `d i > 0`, and unpinned vertices have `d i = 0`. -/
def IsControlledSolution {N n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ)) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (Γ : Matrix (Fin n) (Fin n) ℝ) (d : Fin N → ℝ)
    (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ) : Prop :=
  ∀ i : Fin N, ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun τ => x τ i)
      (f (x t i) t + c • ∑ j, G i j • (Γ *ᵥ x t j) - (c * d i) • (Γ *ᵥ (x t i - s t)))
      (Set.Ici 0) t

/-- (2.7): every vertex state converges to the reference trajectory `s`. -/
def GloballySynchronized {N n : ℕ} (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ) : Prop :=
  ∀ i : Fin N, Tendsto (fun t => x t i - s t) atTop (𝓝 0)

/-- `Ĝ = ½(ΞG + GᵀΞ)` with `Ξ = diag(ξ)` (Lemma 2.12, Theorem 3.1). -/
noncomputable def Ghat {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (ξ : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (1 / 2 : ℝ) • (diagonal ξ * G + Gᵀ * diagonal ξ)

/-- The left-hand side of (3.2):
`Ξ ⊗ (KΓ + ΓᵀKᵀ)/2 + c Ĝ ⊗ (Γ + Γᵀ)/2 - c (ΞD) ⊗ (Γ + Γᵀ)/2`, with `D = diag(d)`. -/
noncomputable def lmi32 {N n : ℕ} (K Γ : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (ξ d : Fin N → ℝ) :
    Matrix (Fin N × Fin n) (Fin N × Fin n) ℝ :=
  diagonal ξ ⊗ₖ ((1 / 2 : ℝ) • (K * Γ + Γᵀ * Kᵀ))
    + c • (Ghat G ξ ⊗ₖ ((1 / 2 : ℝ) • (Γ + Γᵀ)))
    - c • ((diagonal ξ * diagonal d) ⊗ₖ ((1 / 2 : ℝ) • (Γ + Γᵀ)))

/-- The error `e_i(t) = x_i(t) - s(t)` stacked as `e = (e_1ᵀ, …, e_Nᵀ)ᵀ`, indexed by
`Fin N × Fin n` in the Kronecker order `(i, a) ↦ e_i(t)_a`. -/
def errStack {N n : ℕ} (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ) (t : ℝ) :
    Fin N × Fin n → ℝ :=
  fun p => x t p.1 p.2 - s t p.2

/-- The Lyapunov functional (3.3): `V(t) = ½ ∑_i ξ_i e_i(t)ᵀ e_i(t)`. -/
noncomputable def lyapV {N n : ℕ} (ξ : Fin N → ℝ) (s : ℝ → Fin n → ℝ)
    (x : ℝ → Fin N → Fin n → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ξ i * ((x t i - s t) ⬝ᵥ (x t i - s t))

end PinningSync.Strong


