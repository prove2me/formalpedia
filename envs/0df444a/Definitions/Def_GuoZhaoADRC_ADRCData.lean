-- Prove2me | Definitions.Def_GuoZhaoADRC_ADRCData
-- name    : GuoZhaoADRC_ADRCData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:42.216535+00:00
-- url     : https://prove2.me/theorems/1914cfd6-bfc8-48b0-9f65-8d17dc744a45
-- title:
--   The data of the nonlinear ADRC closed loop: plant (1.1), reference, ESO gains, Lyapunov data of A2–A3
-- statement:
--   This structure collects the objects of the MIMO system (1.1) controlled by the extended state observer (1.5) and the feedback ADRC(G) (3.2). The plant has $m\ge1$ subsystems; subsystem $i$ has $n_i\ge1$ states $x^i=(x^i_1,\dots,x^i_{n_i})$, and the stacked state is $x=(x^1,\dots,x^m)\in\mathbb R^n$, $n=n_1+\dots+n_m$. With the zero dynamics $\xi\in\mathbb R^s$, the disturbance $w=(w_1,\dots,w_m)\in\mathbb R^m$ and the control $u\in\mathbb R^m$, the plant reads
--
--   $$\dot x^i_j=x^i_{j+1}\ (1\le j<n_i),\qquad \dot x^i_{n_i}=f_i(x,\xi,w_i)+\sum_{k=1}^m a_{ik}u_k,\qquad \dot\xi=F_0(x,\xi,w).$$
--
--   The fields are: the functions $f_i$ and $F_0$; the constant control gains $a_{ik}$ and the nominal gains $b_{ik}$ (the page's $(b^*_{kl})$ is the inverse matrix of $(b_{ik})$); the disturbance $w$ and its derivative $\dot w$; the reference $z^i=(z^i_1,\dots,z^i_{n_i+1})$ and the derivative of its last component; the reference model $\varphi_i:\mathbb R^{n_i}\to\mathbb R$ of (1.4) with Lipschitz constant $L_i$; the observer functions $g^i_j$ and constants $\Lambda^i_j$ ($1\le j\le n_i+1$); and the Lyapunov data $V_1^i,W_1^i,\lambda^i_{11},\dots,\lambda^i_{14},\beta^i_1$ of Assumption A2 and $V_2^i,W_2^i,\lambda^i_{21},\dots,\lambda^i_{24},\beta^i_2$ of Assumption A3.
--
--   The structure only names the objects; every assumption on them is in `ADRCHyp`.
--
--   **Formalization Note** Indices are 0-based: the page's $x^i_j$ is `x ⟨i, j-1⟩`, and the page's index $n_i+1$ of $z^i,\hat x^i,g^i,\Lambda^i$ is `Fin.last (n i)`. The gains $a_{ik}$ are constants (the page's $a_{ik}(w_i)$ is corrected in Theorem 3.1). Vectors live in `EuclideanSpace`, so all norms are Euclidean.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eqs. (1.1)–(1.7), pp.1728–1730; Assumptions A2, A3, pp.1729–1730; GA1–GA3 and (3.2), pp.1736–1737

import Mathlib

namespace GuoZhaoADRC

/-- **The data of the nonlinear ADRC closed loop (1.1), (1.5), (3.2).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eqs. (1.1)–(1.7), pp.1728–1730; Assumptions A2, A3,
pp.1729–1730; GA1–GA3, (3.2), pp.1736–1737.

The MIMO plant (1.1) has `m` subsystems; subsystem `i` has `n i` states
`x^i = (x^i_1, …, x^i_{n_i})`, the zero dynamics `ξ ∈ ℝ^s`, the disturbance `w ∈ ℝ^m` and the
control `u ∈ ℝ^m`:
`ẋ^i_j = x^i_{j+1}` (`j < n_i`), `ẋ^i_{n_i} = f_i(x, ξ, w_i) + ∑_k a_ik u_k`, `ξ̇ = F₀(x, ξ, w)`.
This structure only collects the objects; every assumption on them is in `ADRCHyp`.

Fields:
* `hm`, `hn` — `m ≥ 1` and every `n_i ≥ 1` (the page's subsystems are nonempty).
* `f i : ℝ^n × ℝ^s × ℝ → ℝ` (curried; it takes the scalar `w_i`) and `F0 : ℝ^n × ℝ^s × ℝ^m → ℝ^s`.
* `a` — the control gains `a_ik`, **constant** (GA2 with the correction that `a_ik` does not
  depend on `w_i`); `b` — the nominal gains `b_ik`; the page's `(b*_kl)` is `b⁻¹`.
* `w`, `w'` — the disturbance and its derivative.
* `z` — the reference (the TD state) `z^i = (z^i_1, …, z^i_{n_i+1})`, and `zLast' i` the
  derivative of `z^i_{n_i+1}`.
* `φ i`, `L i` — the reference model (1.4) and its Lipschitz constant (A3).
* `g i j`, `Λ i j` — the ESO functions `g^i_j` of (1.5) and the constants `Λ^i_j` of A2.
* `V1 i`, `W1 i`, `lam11 … lam14`, `beta1` — the Lyapunov data of A2; `V2 i`, `W2 i`,
  `lam21 … lam24`, `beta2` — the Lyapunov data of A3.

**Formalization Note.** Indices are 0-based: the page's `x^i_j` (`1 ≤ j ≤ n_i`) is
`x ⟨i, j - 1⟩`, the page's `z^i_j`, `x̂^i_j`, `g^i_j`, `Λ^i_j` (`1 ≤ j ≤ n_i + 1`) are at
`j - 1 : Fin (n i + 1)`, so `Fin.last (n i)` is the page's `n_i + 1`. The stacked state lives in
`EuclideanSpace ℝ (Σ i, Fin (n i))`, so `‖x‖` is the Euclidean norm of the page. -/
structure ADRCData (m : ℕ) (n : Fin m → ℕ) (s : ℕ) where
  /-- At least one subsystem. -/
  hm : 0 < m
  /-- Every subsystem has at least one state. -/
  hn : ∀ i, 0 < n i
  /-- The unmodelled dynamics `f_i(x, ξ, w_i)` of (1.1). -/
  f : Fin m → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i)) → EuclideanSpace ℝ (Fin s) → ℝ → ℝ
  /-- The zero dynamics `F₀(x, ξ, w)` of (1.1). -/
  F0 : EuclideanSpace ℝ (Σ i : Fin m, Fin (n i)) → EuclideanSpace ℝ (Fin s) →
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin s)
  /-- The (constant) control gains `a_ik`. -/
  a : Matrix (Fin m) (Fin m) ℝ
  /-- The nominal control gains `b_ik` of GA2. -/
  b : Matrix (Fin m) (Fin m) ℝ
  /-- The external disturbance `w(t) = (w_1(t), …, w_m(t))`. -/
  w : ℝ → EuclideanSpace ℝ (Fin m)
  /-- The derivative `ẇ(t)` of the disturbance. -/
  w' : ℝ → EuclideanSpace ℝ (Fin m)
  /-- The reference signal `z^i_j(t)`, `1 ≤ j ≤ n_i + 1` (0-based `j`). -/
  z : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ
  /-- The derivative of the last reference component `z^i_{n_i+1}`. -/
  zLast' : Fin m → ℝ → ℝ
  /-- The reference model `φ_i : ℝ^{n_i} → ℝ` of (1.4). -/
  φ : (i : Fin m) → EuclideanSpace ℝ (Fin (n i)) → ℝ
  /-- The Lipschitz constant `L_i` of `φ_i` (A3). -/
  L : Fin m → NNReal
  /-- The ESO functions `g^i_j`, `1 ≤ j ≤ n_i + 1` (0-based `j`), of (1.5). -/
  g : (i : Fin m) → Fin (n i + 1) → ℝ → ℝ
  /-- The constants `Λ^i_j` of A2. -/
  Λ : (i : Fin m) → Fin (n i + 1) → ℝ
  /-- The Lyapunov function `V_1^i : ℝ^{n_i+1} → ℝ` of A2. -/
  V1 : (i : Fin m) → EuclideanSpace ℝ (Fin (n i + 1)) → ℝ
  /-- The function `W_1^i : ℝ^{n_i+1} → ℝ` of A2. -/
  W1 : (i : Fin m) → EuclideanSpace ℝ (Fin (n i + 1)) → ℝ
  /-- `λ^i_{11}` of A2. -/
  lam11 : Fin m → ℝ
  /-- `λ^i_{12}` of A2. -/
  lam12 : Fin m → ℝ
  /-- `λ^i_{13}` of A2. -/
  lam13 : Fin m → ℝ
  /-- `λ^i_{14}` of A2. -/
  lam14 : Fin m → ℝ
  /-- `β^i_1` of A2. -/
  beta1 : Fin m → ℝ
  /-- The Lyapunov function `V_2^i : ℝ^{n_i} → ℝ` of A3. -/
  V2 : (i : Fin m) → EuclideanSpace ℝ (Fin (n i)) → ℝ
  /-- The function `W_2^i : ℝ^{n_i} → ℝ` of A3. -/
  W2 : (i : Fin m) → EuclideanSpace ℝ (Fin (n i)) → ℝ
  /-- `λ^i_{21}` of A3. -/
  lam21 : Fin m → ℝ
  /-- `λ^i_{22}` of A3. -/
  lam22 : Fin m → ℝ
  /-- `λ^i_{23}` of A3. -/
  lam23 : Fin m → ℝ
  /-- `λ^i_{24}` of A3. -/
  lam24 : Fin m → ℝ
  /-- `β^i_2` of A3. -/
  beta2 : Fin m → ℝ

end GuoZhaoADRC


