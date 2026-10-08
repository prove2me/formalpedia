-- Prove2me | Definitions.Def_HarrisonReimanRBM_Orthant_Basic
-- name    : HarrisonReimanRBM_Orthant_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:58:46.458054+00:00
-- url     : https://prove2.me/theorems/4d232dca-57a5-4b2c-806f-1b52edd26cfa
-- title:
--   Standing hypotheses on $Q$, matrix norms, $C_0$, the map $\pi$ of (12), the norm on $C[0,T]$, Picard iterates and the shifted triple (11)
-- statement:
--   This file collects the deterministic objects of §1 and of the proof of Theorem 1 of Harrison and Reiman (1981). Vectors in $\mathbb R^K$ are **row** vectors, indexed by $j=1,\dots,K$; a row vector times a matrix is $(yQ)_j=\sum_{i=1}^K y_i q_{ij}$. A path is a function of time $t\ge 0$ with values in $\mathbb R^K$.
--
--   1. **Standing hypotheses on $Q$** (§1). $Q=(q_{ij})$ is a nonnegative $K\times K$ matrix with zeros on the diagonal and spectral radius strictly less than unity.
--   2. **Matrix norms.** For a nonnegative matrix $P$, the maximal row sum $\max_i\sum_j p_{ij}$ (the paper's $\|P\|$ as printed) and the maximal column sum $\max_j\sum_i p_{ij}$.
--   3. **Diagonal rescaling.** For $d\in\mathbb R^K$ with positive entries and $\Lambda=\operatorname{diag}(d)$: the matrix $Q^*=\Lambda^{-1}Q\Lambda$, with entries $q^*_{ij}=q_{ij}d_j/d_i$, and the rescaled path $t\mapsto y(t)\Lambda$.
--   4. **The set $C_0$.** The paths $y$ that are continuous on $[0,\infty)$, nondecreasing in each component, and satisfy $y(0)=0$.
--   5. **The map $\pi$ of (12).** For a fixed path $x$,
--   $$\pi_j(y)(t)=\sup_{0\le s\le t}\Big[\sum_{i=1}^K q_{ij}y_i(s)-x_j(s)\Big]^+,\qquad t\ge 0,\ j=1,\dots,K,$$
--   that is, $\pi(y)(t)=\sup_{0\le s\le t}[y(s)Q-x(s)]^+$ componentwise.
--   6. **The norm on $C[0,T]$.** $\|y\|=\max_{1\le j\le K}\sup_{0\le t\le T}|y_j(t)|$.
--   7. **Picard iterates (16)–(18).** $y^0\equiv 0$ and $y^{n+1}=\pi(y^n)$.
--   8. **The shifted triple of (11).** For $T$ and paths $x,y,z$: $x^*(t)=z(T)+x(T+t)-x(T)$, $y^*(t)=y(T+t)-y(T)$, $z^*(t)=z(T+t)$.
--
--   These objects are shared by every step of the proof of Theorem 1 and by its consequence (11).
--
--   **Formalization Note** Indices run over `Fin K`, so the paper's index $j$ is Lean's $j-1$. The spectral-radius condition is rendered as $Q^m\to 0$ ($m\to\infty$), which is equivalent for real matrices and is the rendering of the referenced `Reiman84.QueueLength.lemma_1`. Paths are functions $\mathbb R\to\mathbb R^K$; only times $t\ge0$ matter. The suprema in $\pi$ and in the norm are real suprema over $[0,t]$ and $[0,T]$; they are the true suprema for continuous paths (bounded on compact intervals), and every statement that uses them assumes continuity. For $t<0$ (resp. $T<0$) the index set is empty and the value is $0$; such times are never used. The maximal column sum is the constant of the contraction of p. 304 under the row-vector convention (see the contraction milestone).
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 302, §1 (standing assumptions); p. 303, (11); p. 304, proof of Theorem 1, (12), (16)–(18) and the norm on C[0, T]

import Mathlib

namespace HarrisonReimanRBM.Orthant

open Filter Topology Matrix

/-!
Harrison & Reiman (1981), §1 (p. 302) and the proof of Theorem 1 (p. 304): the standing
hypotheses on the matrix `Q`, the matrix norms, the set `C₀`, the map `π` of (12), the norm on
`C[0, T]`, the Picard iterates (16)–(18), the diagonal rescaling by `Λ`, and the shifted triple
of (11).

Vectors are `K`-dimensional **row** vectors, encoded as `Fin K → ℝ` (paper index `j` is Lean
index `j − 1`); a row vector times a matrix is `Matrix.vecMul`. Paths are functions
`ℝ → (Fin K → ℝ)` of which only the values at times `t ≥ 0` matter, as in
`Reiman84.QueueLength.Paths`.
-/

/-- The standing hypotheses on `Q` (§1, p. 302): `Q = (q_ij)` is a nonnegative `K × K` matrix
with zeros on the diagonal and spectral radius strictly less than unity. The spectral radius
condition is rendered as `Qᵐ → 0` (`m → ∞`), which is equivalent for real matrices. -/
structure IsReflectionMatrix {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ Q i j
  diag_zero : ∀ j, Q j j = 0
  pow_tendsto_zero : Tendsto (fun m : ℕ => Q ^ m) atTop (𝓝 0)

/-- `‖P‖` of p. 304 as printed: the maximal row sum `max_i Σ_j p_ij` of a (nonnegative)
`K × K` matrix `P`. (For `K = 0` the value is `0`.) -/
noncomputable def maxRowSum {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  ⨆ i : Fin K, ∑ j : Fin K, P i j

/-- The maximal column sum `max_j Σ_i p_ij` of a (nonnegative) `K × K` matrix `P`. Under the
row-vector convention `(yP)_j = Σ_i y_i p_ij` this is the operator norm of `y ↦ yP` for the
max-norm, i.e. the constant of the contraction on p. 304. (For `K = 0` the value is `0`.) -/
noncomputable def maxColSum {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) : ℝ :=
  ⨆ j : Fin K, ∑ i : Fin K, P i j

/-- The rescaled matrix `Q* = Λ⁻¹ Q Λ` of p. 304, for the diagonal matrix `Λ = diag(d)`; its
entries are `q*_ij = q_ij d_j / d_i`. -/
noncomputable def rescaleMatrix {K : ℕ} (d : Fin K → ℝ) (Q : Matrix (Fin K) (Fin K) ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  Matrix.diagonal (fun i => (d i)⁻¹) * Q * Matrix.diagonal d

/-- The path `t ↦ y(t) Λ` for `Λ = diag(d)` (row vector times matrix), p. 304. -/
noncomputable def scalePath {K : ℕ} (d : Fin K → ℝ) (y : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t => Matrix.vecMul (y t) (Matrix.diagonal d)

/-- `y ∈ C₀` (p. 304): `y` is continuous on `[0, ∞)`, nondecreasing on `[0, ∞)` (each component,
for the pointwise order) and `y(0) = 0`. -/
def InC0 {K : ℕ} (y : ℝ → Fin K → ℝ) : Prop :=
  ContinuousOn y (Set.Ici 0) ∧ MonotoneOn y (Set.Ici 0) ∧ y 0 = 0

/-- The map `π` of (12), p. 304, for fixed `x`:
`π_j(y)(t) = sup_{0 ≤ s ≤ t} [ Σ_i q_ij y_i(s) − x_j(s) ]⁺`, i.e.
`π(y)(t) = sup_{0 ≤ s ≤ t} [y(s) Q − x(s)]⁺` componentwise.
The supremum is a real `⨆` over `s ∈ [0, t]`; it is the true supremum when `x` and `y` are
continuous on `[0, t]` (bounded there), and every statement using `piMap` assumes this. For
`t < 0` the index set is empty and the value is `0`; such times are never used. -/
noncomputable def piMap {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (x : ℝ → Fin K → ℝ)
    (y : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t j => ⨆ s : Set.Icc (0 : ℝ) t, max (Matrix.vecMul (y s) Q j - x s j) 0

/-- The norm `‖y‖ = max_{1 ≤ j ≤ K} sup_{0 ≤ t ≤ T} |y_j(t)|` on `C[0, T]` (p. 304), written as
`sup_{0 ≤ t ≤ T} ‖y(t)‖_∞` with Mathlib's sup norm on `Fin K → ℝ`. It is the true supremum
when `y` is continuous on `[0, T]`; for `T < 0` it is `0`. -/
noncomputable def supNormOn {K : ℕ} (T : ℝ) (y : ℝ → Fin K → ℝ) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) T, ‖y t‖

/-- The Picard iterates (16)–(18), p. 304: `y⁰ ≡ 0` and `yⁿ⁺¹ = π(yⁿ)`. -/
noncomputable def picardIter {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (x : ℝ → Fin K → ℝ)
    (n : ℕ) : ℝ → Fin K → ℝ :=
  (piMap Q x)^[n] 0

/-- `x*(t) = z(T) + x(T + t) − x(T)` of (11), p. 303. -/
def shiftX {K : ℕ} (T : ℝ) (x z : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t => z T + x (T + t) - x T

/-- `y*(t) = y(T + t) − y(T)` of (11), p. 303. -/
def shiftY {K : ℕ} (T : ℝ) (y : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t => y (T + t) - y T

/-- `z*(t) = z(T + t)` of (11), p. 303. -/
def shiftZ {K : ℕ} (T : ℝ) (z : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t => z (T + t)

end HarrisonReimanRBM.Orthant


