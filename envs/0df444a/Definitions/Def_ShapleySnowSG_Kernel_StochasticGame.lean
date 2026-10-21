-- Prove2me | Definitions.Def_ShapleySnowSG_Kernel_StochasticGame
-- name    : ShapleySnowSG_Kernel_StochasticGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:47.358033+00:00
-- url     : https://prove2.me/theorems/3e490e92-28e0-4a23-85d7-6c3c97a34846
-- title:
--   §2.1–§2.2, §3.1 — local games G^k(λ, z), Shapley fixed point, data array D(λ), auxiliary matrices Δ^ℓ and kernel-reduced Δ̇^ℓ
-- statement:
--   This file fixes the discounted stochastic game of §2.1 and its array presentation.
--
--   A two-player zero-sum stochastic game has a finite state set $K=\{1,\dots,n\}$, finite nonempty action sets $I_k$, $J_k$ at each state $k$, a payoff $g(k,i,j)\in\mathbb R$, a transition probability $q(\cdot\mid k,i,j)$ on $K$ and a discount factor $\lambda\in(0,1]$.
--
--   1. **Local game** (Definition 2.1.1). For $z\in\mathbb R^n$, $\mathcal G^k(\lambda,z)$ is the $I_k\times J_k$ matrix game with entries
--   $$\big(\mathcal G^k(\lambda,z)\big)_{ij}=\lambda g(k,i,j)+(1-\lambda)\sum_{\ell=1}^n q(\ell\mid k,i,j)\,z^\ell .$$
--   2. **Shapley fixed point** (Definition 2.1.2 and §2.1, result 2). $v\in\mathbb R^n$ is a fixed point of the Shapley operator when $\mathrm{val}(\mathcal G^k(\lambda,v))=v^k$ for every $k$; the vector of discounted values $v_\lambda$ is the unique such $v$.
--   3. **Data array** (2.2)–(2.4). $M^k_0=\lambda G^k$, $M^k_k=(1-\lambda)Q^k_k-U$ and $M^k_\ell=(1-\lambda)Q^k_\ell$ for $\ell\neq k$, where $G^k=(g(k,i,j))_{i,j}$ and $Q^k_\ell=(q(\ell\mid k,i,j))_{i,j}$.
--   4. **Auxiliary matrices.** $\Delta^0,\dots,\Delta^n$ are those of $D(\lambda)$ (Definition 2.2.2). Given a Shapley–Snow kernel $\dot I_k\times\dot J_k$ of each local game, $\dot\Delta^0,\dots,\dot\Delta^n$ are those of the reduced array $\dot D(\lambda)$ (3.2); they are square of size $\prod_k|\dot I_k|$.
--
--   These are the objects of Theorem 3.4.2.
--
--   **Formalization Note** The action sets may depend on the state, as in §4, p. 20, where the paper extends all results "word for word" to this case; the paper's §2–3 setting is the constant family. States are `Fin n` (index base 0). The value $v_\lambda$ enters theorems as any $v$ satisfying the fixed-point relation; its existence and uniqueness is the milestone `shapley_fixed_point`.
-- source:
--   Attia & Oliu-Barton, Shapley–Snow kernels, multiparameter eigenvalue problems and stochastic games, arXiv:1810.08798v2, pp. 6–8, §2.1 (Definitions 2.1.1, 2.1.2), §2.2 ((2.2)–(2.4), Definition 2.2.2); p. 14, §3.1; p. 20, §4 (state-dependent action sets)

import Mathlib
import Definitions.Def_ShapleySnowSG_Kernel_MatrixGame
import Definitions.Def_ShapleySnowSG_Kernel_KroneckerMEP

namespace ShapleySnowSG.Kernel

open Matrix

/-- Definition 2.1.1 (p. 7): the local game `G^k(λ, z)` at state `k`, with entries
`λ g(k,i,j) + (1 − λ) Σ_ℓ q(ℓ | k,i,j) z^ℓ`. States are `Fin n`; the action sets `I k × J k`
may depend on the state (§4, p. 20). -/
def localGame {n : ℕ} {I J : Fin n → Type*} (g : ∀ k, I k → J k → ℝ)
    (q : ∀ k, I k → J k → Fin n → ℝ) (lam : ℝ) (z : Fin n → ℝ) (k : Fin n) :
    Matrix (I k) (J k) ℝ :=
  Matrix.of fun i j => lam * g k i j + (1 - lam) * ∑ l, q k i j l * z l

/-- `v` is a fixed point of the Shapley operator `Φ(λ, ·)` (Definition 2.1.2, p. 7):
`val(G^k(λ, v)) = v^k` for every state `k`. By §2.1, p. 7, result 2, the discounted value
`v_λ` is the unique such vector. -/
def IsShapleyFixed {n : ℕ} {I J : Fin n → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    (g : ∀ k, I k → J k → ℝ) (q : ∀ k, I k → J k → Fin n → ℝ) (lam : ℝ) (v : Fin n → ℝ) :
    Prop :=
  ∀ k, IsMatVal (localGame g q lam v k) (v k)

/-- The data array `D(λ)` (2.2)/(2.4), p. 7: row `k`, column `0` is `M^k_0 = λ G^k`; row `k`,
column `ℓ + 1` is `M^k_ℓ = (1 − λ) Q^k_ℓ − [ℓ = k] U`, where `Q^k_ℓ = (q(ℓ | k,i,j))_{i,j}`. -/
def dataArray {n : ℕ} {I J : Fin n → Type*} (g : ∀ k, I k → J k → ℝ)
    (q : ∀ k, I k → J k → Fin n → ℝ) (lam : ℝ) :
    ∀ k : Fin n, Fin (n + 1) → Matrix (I k) (J k) ℝ :=
  fun k l => Fin.cases (motive := fun _ => Matrix (I k) (J k) ℝ)
    (Matrix.of fun i j => lam * g k i j)
    (fun l' => Matrix.of fun i j => (1 - lam) * q k i j l' - if l' = k then 1 else 0) l

/-- The auxiliary matrices `Δ^0, …, Δ^n` of the game (Definition 2.2.2, p. 8). -/
noncomputable def Delta {n : ℕ} {I J : Fin n → Type*} (g : ∀ k, I k → J k → ℝ)
    (q : ∀ k, I k → J k → Fin n → ℝ) (lam : ℝ) (ℓ : Fin (n + 1)) :
    Matrix (∀ k, I k) (∀ k, J k) ℝ :=
  aux (dataArray g q lam) ℓ

/-- The auxiliary matrices `Δ̇^0, …, Δ̇^n` of the reduced array `Ḋ(λ)` (§3.1, p. 14), for the
kernels `İ_k = r k (Fin (s k))`, `J̇_k = c k (Fin (s k))`; square of size `Π_k s k`. -/
noncomputable def DeltaDot {n : ℕ} {I J : Fin n → Type*} (g : ∀ k, I k → J k → ℝ)
    (q : ∀ k, I k → J k → Fin n → ℝ) (lam : ℝ) (s : Fin n → ℕ)
    (r : ∀ k, Fin (s k) ↪ I k) (c : ∀ k, Fin (s k) ↪ J k) (ℓ : Fin (n + 1)) :
    Matrix (∀ k, Fin (s k)) (∀ k, Fin (s k)) ℝ :=
  aux (redArray (dataArray g q lam) s r c) ℓ

end ShapleySnowSG.Kernel


