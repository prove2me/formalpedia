-- Prove2me | Definitions.Def_Def_CAH21_NeuralNetworks
-- name    : Def_CAH21_NeuralNetworks
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T17:18:44.196503+00:00
-- url     : https://prove2.me/theorems/f62a935a-04dd-48c2-8354-6c8a4bb68d28
-- title:
--   The neural network class $\mathcal N_{D,T,q}$ and widths $D_{(n,p)}$
-- statement:
--   The class $\mathcal N_{D,T,q}$ of neural networks (SI Appendix, §1.2.1) and the widths $D_{(n,p)}$ of Theorem 3.
--
--   A neural network $\varphi:\mathbb C^m\to\mathbb C^N$ is a composition
--   $$\varphi(y)=V_T(\rho_{T-1}(\cdots\rho_1(V_1(y)))),$$
--   where each $V_j(x)=W_jx+R_jy+c_j$ is affine in the current vector $x$ and in the input $y$ (skip connections), and each $\rho_j:\mathbb C^{N_j}\to\mathbb C^{N_j}$ is of one of two forms:
--
--   1. there is an index set $I_j$ and a function $f_j:\mathbb C\to\mathbb C$ with $\rho_j(x)_k=f_j(x_k)$ for $k\in I_j$ and $\rho_j(x)_k=x_k$ otherwise;
--   2. there is a function $f_j$ such that, writing $x=(x_0,X,Y)$ with $X\in\mathbb C^{m_j}$, $\rho_j(x_0,X,Y)=(0,f_j(x_0)X,Y)$ (eq. (1.13)).
--
--   $D=(N_0=m,N_1,\dots,N_T=N)$ lists the layer widths, $T$ the number of affine layers and $q$ the number of distinct non-linear maps (counting different $I_j$ and $m_j$). Theorem 3 uses
--   $$D_{(n,p)}=(m,\underbrace{2N+m,\ 2(N+m),\ 2N+m+1}_{np\text{ times}},N).$$
--
--   **Formalization Note** The class is the predicate `IsNeuralNet φ D T q` (with "at most $q$" distinct maps, where two layers are the same map iff their form, function and index data agree). The functions $f_j$ are arbitrary; the paper additionally builds them from arithmetic operations and an approximate square root, which is not modeled here.
-- source:
--   Colbrook, Antun, Hansen, Can stable and accurate neural networks be computed? On the barriers of deep learning and Smale's 18th problem, arXiv:2101.08286v2 (PNAS 119(12), 2022), https://arxiv.org/abs/2101.08286, SI Appendix, pp. 3–4, §1.2.1 (network definition, eq. (1.13)); p. 6, Theorem 3 (1) for D_(n,p)

import Mathlib

/-!
Colbrook–Antun–Hansen (arXiv:2101.08286v2), SI Appendix §1.2.1: the class
`𝒩_{D,T,q}` of (complex-valued, feed-forward) neural networks `φ : ℂ^m → ℂ^N`,
`φ(y) = V_T(ρ_{T-1}(⋯ρ_1(V_1(y))))`, where each `V_j(x) = W_j x + R_j y + c_j` is affine
in the current vector `x` and in the input `y` (skip connections), and each `ρ_j` is a
non-linear layer of one of the two forms (i) (a function `f_j` applied entrywise on an
index set `I_j`) or (ii) (the gating map `(x₀, X, Y) ↦ (0, f_j(x₀) X, Y)` with `X ∈ ℂ^{m_j}`),
eq. (1.13).  Also the layer-width vector `D_{(n,p)}` of Theorem 3.
-/

namespace ColbrookAntunHansen

/-- A non-linear layer `ρ : ℂ^d → ℂ^d` of form (i) or (ii) (SI §1.2.1). -/
inductive NonlinLayer (d : ℕ) where
  /-- Form (i): apply `f` to the entries with index in `I`, leave the others unchanged. -/
  | pointwise (I : Finset (Fin d)) (f : ℂ → ℂ)
  /-- Form (ii): write `x = (x₀, X, Y)` with `X ∈ ℂ^{k}`; map it to `(0, f(x₀) X, Y)`. -/
  | gated (k : ℕ) (hk : k + 1 ≤ d) (f : ℂ → ℂ)

namespace NonlinLayer

/-- The action of a non-linear layer on a vector of `ℂ^d`. -/
def apply {d : ℕ} : NonlinLayer d → (Fin d → ℂ) → (Fin d → ℂ)
  | pointwise I f, x => fun i => if i ∈ I then f (x i) else x i
  | gated k hk f, x => fun i =>
      if i.val = 0 then 0
      else if i.val ≤ k then f (x ⟨0, by omega⟩) * x i
      else x i

/-- The data identifying a non-linear layer up to its width: its form, its function `f_j`
and its index data (`I_j` for form (i), `m_j` for form (ii)).  Two layers are counted
as the same non-linear map in `q` iff their keys agree. -/
def key {d : ℕ} : NonlinLayer d → Bool × (ℂ → ℂ) × Set ℕ × ℕ
  | pointwise I f => (false, f, (fun i : Fin d => i.val) '' (I : Set (Fin d)), 0)
  | gated k _ f => (true, f, ∅, k)

end NonlinLayer

/-- The hidden vectors of a network with widths `D`: `hidden 0 = V_1(y)` and
`hidden (j+1) = V_{j+2}(ρ_{j+1}(hidden j))`. -/
noncomputable def hiddenVec {m : ℕ} (D : ℕ → ℕ)
    (W₀ : Matrix (Fin (D 1)) (Fin m) ℂ)
    (W : (j : ℕ) → Matrix (Fin (D (j + 2))) (Fin (D (j + 1))) ℂ)
    (R : (j : ℕ) → Matrix (Fin (D (j + 1))) (Fin m) ℂ)
    (c : (j : ℕ) → Fin (D (j + 1)) → ℂ)
    (σ : (j : ℕ) → NonlinLayer (D (j + 1)))
    (y : Fin m → ℂ) : (j : ℕ) → Fin (D (j + 1)) → ℂ
  | 0 => W₀.mulVec y + (R 0).mulVec y + c 0
  | j + 1 => (W j).mulVec ((σ j).apply (hiddenVec D W₀ W R c σ y j)) + (R (j + 1)).mulVec y + c (j + 1)

/-- `φ ∈ 𝒩_{D,T,q}`: `φ : ℂ^m → ℂ^N` is a neural network with `T ≥ 1` affine layers,
widths `D = (D_0 = m, D_1, …, D_T = N)` and at most `q` different non-linear maps
(counted with their index data `I_j` / `m_j`). The non-linear layers are
`ρ_j = σ (j-1)` for `j = 1, …, T-1`. -/
def IsNeuralNet {m N : ℕ} (φ : (Fin m → ℂ) → (Fin N → ℂ)) (D : ℕ → ℕ) (T q : ℕ) : Prop :=
  1 ≤ T ∧ D 0 = m ∧
  ∃ (hD : D (T - 1 + 1) = N)
    (W₀ : Matrix (Fin (D 1)) (Fin m) ℂ)
    (W : (j : ℕ) → Matrix (Fin (D (j + 2))) (Fin (D (j + 1))) ℂ)
    (R : (j : ℕ) → Matrix (Fin (D (j + 1))) (Fin m) ℂ)
    (c : (j : ℕ) → Fin (D (j + 1)) → ℂ)
    (σ : (j : ℕ) → NonlinLayer (D (j + 1))),
    ((fun j => (σ j).key) '' {j | j < T - 1}).ncard ≤ q ∧
    ∀ y i, φ y i = hiddenVec D W₀ W R c σ y (T - 1) (Fin.cast hD.symm i)

/-- The width vector `D_{(n,p)} = (m, 2N+m, 2(N+m), 2N+m+1, …, 2N+m, 2(N+m), 2N+m+1, N)`
of Theorem 3, in which the block `(2N+m, 2(N+m), 2N+m+1)` is repeated `n p` times;
entry `j` for `j = 0, …, 3np+1`. -/
def firenetDims (m N n p : ℕ) (j : ℕ) : ℕ :=
  if j = 0 then m
  else if j = 3 * n * p + 1 then N
  else if (j - 1) % 3 = 0 then 2 * N + m
  else if (j - 1) % 3 = 1 then 2 * (N + m)
  else 2 * N + m + 1

end ColbrookAntunHansen


