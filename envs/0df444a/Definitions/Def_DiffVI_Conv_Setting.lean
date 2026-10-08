-- Prove2me | Definitions.Def_DiffVI_Conv_Setting
-- name    : DiffVI_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:37.294364+00:00
-- url     : https://prove2.me/theorems/b65165a4-cb94-42fa-bc3f-1b15a94ab2d2
-- title:
--   §7, pp. 41–43 — the grid t_{h,i}, the time-stepping scheme (7.1)–(7.2), the interpolants x̂^h, û^h, weak L² convergence
-- statement:
--   This file fixes the objects of the time-stepping scheme of Pang and Stewart for the initial-value differential variational inequality (DVI) (6.2)
--   $$\dot x=f(t,x)+B(t,x)u,\quad x(0)=x^0,\qquad u\in\mathrm{SOL}(K,G(t,x)+F),$$
--   on $[0,T]$, with $f:[0,T]\times\mathbb R^n\to\mathbb R^n$, $B:[0,T]\times\mathbb R^n\to\mathbb R^{n\times m}$, $G:[0,T]\times\mathbb R^n\to\mathbb R^m$, $F:\mathbb R^m\to\mathbb R^m$ and $K\subseteq\mathbb R^m$. Here $\mathrm{SOL}(K,\Phi)$ is the solution set of the variational inequality: the $u\in K$ with $(u'-u)^{\mathsf T}\Phi(u)\ge0$ for all $u'\in K$. The objects common to the whole paper (Assumptions (A) and (B), $G(\Omega)$, positive semidefiniteness, the weak solution of (6.2)) are in the imported shared setting `DiffVI.Exist.Setting`.
--
--   1. **Grid.** For an integer $N\ge1$, the step is $h=T/N$ and the grid points are $t_{h,i}=ih$.
--   2. **Scheme (7.1)–(7.2).** Given a parameter $\theta$, sequences $(x^{h,i})_i\subset\mathbb R^n$ and $(u^{h,i})_i\subset\mathbb R^m$ solve the scheme if $x^{h,0}=x^0$ and, for $i=0,\dots,N-1$,
--   $$x^{h,i+1}=x^{h,i}+h\big[f(t_{h,i+1},\theta x^{h,i}+(1-\theta)x^{h,i+1})+B(t_{h,i},x^{h,i})u^{h,i+1}\big],\qquad u^{h,i+1}\in\mathrm{SOL}(K,G(t_{h,i+1},x^{h,i+1})+F).$$
--   3. **Interpolants.** $\hat x^h$ is the continuous piecewise linear interpolant of $x^{h,0},\dots,x^{h,N}$: $\hat x^h(t)=x^{h,i}+\frac{t-t_{h,i}}{h}(x^{h,i+1}-x^{h,i})$ for $t\in[t_{h,i},t_{h,i+1}]$. $\hat u^h$ is the piecewise constant interpolant: $\hat u^h(t)=u^{h,i+1}$ for $t\in(t_{h,i},t_{h,i+1}]$, and $\hat u^h(0)=u^{h,1}$.
--   4. **Weak $L^2$ convergence.** $g_k\rightharpoonup u$ weakly in $L^2(0,T;\mathbb R^m)$ if every $g_k$ and $u$ lie in $L^2(0,T;\mathbb R^m)$ and $\int_0^T\psi^{\mathsf T}g_k\,dt\to\int_0^T\psi^{\mathsf T}u\,dt$ for every $\psi\in L^2(0,T;\mathbb R^m)$.
--
--   These are the objects of the convergence theorem for the time-stepping scheme (Theorem 7.1) and of the cone-constrained scheme of Section 8.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin k)` and matrices are continuous linear maps. $\mathrm{SOL}(K,\Phi)$ is the published `SolodovSvaiterVI.Alg21.viSol Φ K`. The scheme leaves $\theta$ free; the theorems impose $\theta\in[0,1]$. The interpolant $\hat x^h$ uses interval index $\min(\lfloor t/h\rfloor,N-1)$, so $\hat x^h(T)=x^{h,N}$; $\hat u^h$ uses index $\max(1,\lceil t/h\rceil)$, and its value at $t=0$, which the paper leaves unspecified, is $u^{h,1}$. Both are meant for $N\ge1$ only (at $N=0$, $h=T/0=0$ in Lean). Membership of every $g_k$ in $L^2$ is part of weak convergence, so that no Lean integral of a non-integrable function enters.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 41–43, §7, (7.1), (7.2), interpolants x̂^h, û^h (p. 43)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace DiffVI.Conv

local notation "𝔼" k:max => EuclideanSpace ℝ (Fin k)

open SolodovSvaiterVI.Alg21

/-- The grid point `t_{h,i} = i h` with `h = T / N`. -/
noncomputable def tGrid (T : ℝ) (N : ℕ) (i : ℕ) : ℝ := (i : ℝ) * (T / N)

/-- The time-stepping scheme (7.1)–(7.2) with step `h = T / N` and parameter `θ`:
`x^{h,0} = x⁰` and, for `i = 0, …, N - 1`,
`x^{h,i+1} = x^{h,i} + h [f(t_{h,i+1}, θ x^{h,i} + (1 - θ) x^{h,i+1}) + B(t_{h,i}, x^{h,i}) u^{h,i+1}]`,
`u^{h,i+1} ∈ SOL(K, G(t_{h,i+1}, x^{h,i+1}) + F)`. -/
def IsScheme {n m : ℕ} (K : Set (𝔼 m)) (f : ℝ → 𝔼 n → 𝔼 n)
    (B : ℝ → 𝔼 n → (𝔼 m →L[ℝ] 𝔼 n)) (G : ℝ → 𝔼 n → 𝔼 m) (F : 𝔼 m → 𝔼 m) (T θ : ℝ)
    (x0 : 𝔼 n) (N : ℕ) (xs : ℕ → 𝔼 n) (us : ℕ → 𝔼 m) : Prop :=
  xs 0 = x0 ∧
  (∀ i < N, xs (i + 1) = xs i + (T / N) •
      (f (tGrid T N (i + 1)) (θ • xs i + (1 - θ) • xs (i + 1)) +
        B (tGrid T N i) (xs i) (us (i + 1)))) ∧
  ∀ i < N, us (i + 1) ∈ viSol (fun v => G (tGrid T N (i + 1)) (xs (i + 1)) + F v) K

/-- The continuous piecewise linear interpolant `x̂^h` of `x^{h,0}, …, x^{h,N}` on `[0, T]`,
`h = T / N` (p. 43): on `[t_{h,i}, t_{h,i+1}]`,
`x̂^h(t) = x^{h,i} + ((t - t_{h,i}) / h) (x^{h,i+1} - x^{h,i})`. -/
noncomputable def xhat {n : ℕ} (T : ℝ) (N : ℕ) (xs : ℕ → 𝔼 n) (t : ℝ) : 𝔼 n :=
  let h := T / N
  let i := min ⌊t / h⌋₊ (N - 1)
  xs i + ((t - (i : ℝ) * h) / h) • (xs (i + 1) - xs i)

/-- The piecewise constant interpolant `û^h` (p. 43): `û^h(t) = u^{h,i+1}` for
`t ∈ (t_{h,i}, t_{h,i+1}]`, and `û^h(0) = u^{h,1}`. -/
noncomputable def uhat {m : ℕ} (T : ℝ) (N : ℕ) (us : ℕ → 𝔼 m) (t : ℝ) : 𝔼 m :=
  us (max 1 ⌈t / (T / N)⌉₊)

/-- Weak convergence in `L²(0, T; ℝᵐ)`: every `g_k` and the limit `ul` are in `L²` and
`∫₀ᵀ ψᵀ g_k → ∫₀ᵀ ψᵀ ul` for every `ψ ∈ L²(0, T; ℝᵐ)`. -/
def WeakL2Tendsto {m : ℕ} (T : ℝ) (g : ℕ → ℝ → 𝔼 m) (ul : ℝ → 𝔼 m) : Prop :=
  (∀ k, MemLp (g k) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
  MemLp ul 2 (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
  ∀ ψ : ℝ → 𝔼 m, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) T)) →
    Tendsto (fun k => ∫ t in Set.Icc (0 : ℝ) T, ⟪ψ t, g k t⟫_ℝ) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) T, ⟪ψ t, ul t⟫_ℝ))

end DiffVI.Conv


