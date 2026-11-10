-- Prove2me | Definitions.Def_KoanaKPaths_Main_Estimator
-- name    : KoanaKPaths_Main_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:19.421195+00:00
-- url     : https://prove2.me/theorems/0bbcad02-818b-4c03-926f-aa10364205db
-- title:
--   §3.1 — sign labels, the tensor $\Psi$, recursive sign sketches $S_i$ and the estimators $Y_i$
-- statement:
--   Fix $n,k\ge1$ and a homogeneous degree-$k$ 0–1 coefficient tensor $(c_\tau)_{\tau\in[n]^k}$, with $N=\sum_{\tau\ \text{multilinear}}c_\tau$.
--
--   Let $\sigma_{j,r}$ ($j\in[n]$, $r\in[k]$) be mutually independent uniform signs in $\{-1,1\}$ and $\sigma_j=(\sigma_{j,1},\dots,\sigma_{j,k})^T$. For $\tau\in[n]^k$ put $D_\tau=\det[\sigma_{\tau_1}\cdots\sigma_{\tau_k}]$ and $\Psi(\tau)=c_\tau D_\tau$, with $\|\Psi\|_F^2=\sum_\tau\Psi(\tau)^2$.
--
--   Fix a sketch width $\ell\ge1$. Independently of the labels, let $R_1\in\{-1,1\}^{[\ell]\times[n]}$ and $R_i\in\{-1,1\}^{[\ell]\times([\ell]\times[n])}$ for $2\le i\le k$ have mutually independent uniform entries. With $S_0=\Psi$,
--   $$S_1(a_1,\tau_2,\dots,\tau_k)=\sum_{\tau_1\in[n]}R_1[a_1,\tau_1]\,\Psi(\tau_1,\dots,\tau_k),$$
--   $$S_i(a_i,\tau_{i+1},\dots,\tau_k)=\sum_{a_{i-1}\in[\ell]}\sum_{\tau_i\in[n]}R_i[a_i,(a_{i-1},\tau_i)]\,S_{i-1}(a_{i-1},\tau_i,\dots,\tau_k)\quad(2\le i\le k),$$
--   so $S_k\in\mathbb R^{\ell}$. The same $R_i$ acts on every residual word $(\tau_{i+1},\dots,\tau_k)$. Finally
--   $$Y_i=\frac{\|S_i\|_F^2}{\ell^i\,k!}\qquad(0\le i\le k).$$
--   For a real $d\times t$ matrix $X$ and a sign matrix $R\in\{-1,1\}^{\ell\times d}$ we also write $\|X\|_F^2=\sum_{u,b}X(u,b)^2$ and $RX$ for the matrix product.
--
--   These are the random objects of Lemmas 4–6: the unbiased estimator $\|\Psi\|_F^2/k!$ of extensor-coding and its recursive compression by shared sign matrices.
--
--   **Formalization Note** Coordinates, variables and rows are 0-based (`Fin k`, `Fin n`, `Fin ℓ`). Expectations are averages over the finite sample space of all label bits and sign-matrix bits, i.e. under mutually independent fair signs; a bit `true` is the sign $+1$. The residual word of $S_i$ is a function on the positions $r$ with $i\le r$ (0-based), and `sketch c σ R i` is $S_{i+1}$. The matrix $R_t$ ($2\le t\le k$) is the slice at index $t-2$ of the second component.
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), pp. 5–7 (PDF pp. 6–8), Section 3.1 and Section 2 (Frobenius norm)

import Mathlib

noncomputable section

open scoped BigOperators

namespace KoanaKPaths.Main

/-- A uniform random sign: a fair bit `b` read as `+1` (`true`) or `-1` (`false`). -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- The expectation of `f` under the uniform distribution on the finite sample space `Ω`. When
`Ω` is a product of copies of `Bool` this is the law of mutually independent fair signs. -/
def uniformMean {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

/-- `‖X‖_F² = ∑_{u,b} X(u,b)²` for a real `d × t` matrix `X` (rows `Fin d`, columns `Fin t`). -/
def realFrobSq {d t : ℕ} (X : Fin d → Fin t → ℝ) : ℝ :=
  ∑ u, ∑ b, (X u b) ^ 2

/-- The product `R X` of a sign matrix `R ∈ {±1}^{ℓ×d}` (entry `sgn (R a u)`) and a real `d × t`
matrix `X`. -/
def signMul {ℓ d t : ℕ} (R : Fin ℓ → Fin d → Bool) (X : Fin d → Fin t → ℝ) : Fin ℓ → Fin t → ℝ :=
  fun a b => ∑ u, (sgn (R a u) : ℝ) * X u b

/-- A homogeneous degree-`k` 0–1 coefficient tensor `c = (c_τ)_{τ ∈ [n]^k}` (§2, printed p. 4);
coordinates and variables are 0-based, `τ : Fin k → Fin n`. -/
def IsZeroOneTensor {n k : ℕ} (c : (Fin k → Fin n) → ℤ) : Prop :=
  ∀ τ, c τ = 0 ∨ c τ = 1

/-- `N = N(P) = ∑_{τ multilinear} c_τ`: the sum over the words with pairwise distinct entries. -/
def tensorN {n k : ℕ} (c : (Fin k → Fin n) → ℤ) : ℤ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : Fin k → Fin n => Function.Injective τ), c τ

/-- The vertex labels of §3.1: `σ j r` is the fair bit giving the sign `σ_{j,r}`, for `j ∈ [n]`,
`r ∈ [k]`; all `nk` of them are independent and uniform under `uniformMean`. -/
abbrev Labels (n k : ℕ) := Fin n → Fin k → Bool

/-- `D_τ = det[σ_{τ₁} ⋯ σ_{τ_k}]`: the determinant of the `k × k` sign matrix whose `s`-th column
is the label vector `σ_{τ_s}`, i.e. whose `(r, s)` entry is `σ_{τ_s, r}`. -/
def detD {n k : ℕ} (σ : Labels n k) (τ : Fin k → Fin n) : ℤ :=
  Matrix.det (Matrix.of fun r s : Fin k => sgn (σ (τ s) r))

/-- The determinant-weighted tensor `Ψ(τ) = c_τ D_τ` (§3.1, printed p. 5). -/
def Psi {n k : ℕ} (c : (Fin k → Fin n) → ℤ) (σ : Labels n k) (τ : Fin k → Fin n) : ℤ :=
  c τ * detD σ τ

/-- `‖Ψ‖_F² = ∑_τ Ψ(τ)²`. -/
def psiFrobSq {n k : ℕ} (c : (Fin k → Fin n) → ℤ) (σ : Labels n k) : ℤ :=
  ∑ τ, (Psi c σ τ) ^ 2

/-- The residual word coordinates of the sketch `S_i`: the coordinates `τ_{i+1}, …, τ_k`, i.e. the
0-based positions `r ∈ Fin k` with `i ≤ r`. For `i = k` there is exactly one (empty) residual
word, so `S_k` is a vector indexed by `[ℓ]` alone. -/
abbrev Resid (n k i : ℕ) := {r : Fin k // i ≤ r.val} → Fin n

/-- Extend a residual word for stage `i + 1` by the value `j` of the coordinate `τ_{i+1}` (0-based
position `i`). -/
def extendResid {n k i : ℕ} (ρ : Resid n k (i + 1)) (j : Fin n) : Resid n k i :=
  fun r => if h : r.1.val = i then j else ρ ⟨r.1, by have := r.2; omega⟩

/-- A residual word at stage `0` is a full word `τ ∈ [n]^k`. -/
def fullWord {n k : ℕ} (ρ : Resid n k 0) : Fin k → Fin n := fun r => ρ ⟨r, Nat.zero_le _⟩

/-- The sign matrices of §3.1: the first component is `R₁ ∈ {±1}^{[ℓ]×[n]}`; the slice at index
`t - 2` of the second component is `R_t ∈ {±1}^{[ℓ]×([ℓ]×[n])}`, for `2 ≤ t ≤ k`. Under
`uniformMean` on `Labels n k × SketchSigns n k ℓ` all entries of all matrices and all labels are
mutually independent fair signs. -/
abbrev SketchSigns (n k ℓ : ℕ) := (Fin ℓ → Fin n → Bool) × (Fin (k - 1) → Fin ℓ → Fin ℓ × Fin n → Bool)

/-- The recursive sketches of §3.1 (printed p. 6), shifted by one: `sketch c σ R i = S_{i+1}`.
`S₁(a₁, τ₂, …, τ_k) = ∑_{τ₁} R₁[a₁, τ₁] Ψ(τ₁, …, τ_k)` and, for `2 ≤ i ≤ k`,
`S_i(a_i, τ_{i+1}, …, τ_k) = ∑_{a_{i-1} ∈ [ℓ]} ∑_{τ_i ∈ [n]} R_i[a_i, (a_{i-1}, τ_i)] S_{i-1}(a_{i-1}, τ_i, …, τ_k)`.
The same `R_i` is used for every residual word. Stages beyond `k` are not used and are `0`. -/
def sketch {n k ℓ : ℕ} (c : (Fin k → Fin n) → ℤ) (σ : Labels n k) (R : SketchSigns n k ℓ) :
    (i : ℕ) → Fin ℓ → Resid n k (i + 1) → ℤ
  | 0 => fun a ρ => ∑ j : Fin n, sgn (R.1 a j) * Psi c σ (fullWord (extendResid ρ j))
  | i + 1 => fun a ρ =>
      if h : i < k - 1 then
        ∑ b : Fin ℓ, ∑ j : Fin n, sgn (R.2 ⟨i, h⟩ a (b, j)) * sketch c σ R i b (extendResid ρ j)
      else 0

/-- `‖S_i‖_F²` for `i ≥ 0`, with `S₀ = Ψ`: the sum of the squares of all entries of `S_i`. -/
def sketchFrobSq {n k ℓ : ℕ} (c : (Fin k → Fin n) → ℤ) (σ : Labels n k) (R : SketchSigns n k ℓ) :
    ℕ → ℤ
  | 0 => psiFrobSq c σ
  | i + 1 => ∑ a : Fin ℓ, ∑ ρ : Resid n k (i + 1), (sketch c σ R i a ρ) ^ 2

/-- The normalized estimator of Lemma 6: `Y_i = ‖S_i‖_F² / (ℓ^i k!)`. -/
def Yhat {n k ℓ : ℕ} (c : (Fin k → Fin n) → ℤ) (i : ℕ) (σ : Labels n k) (R : SketchSigns n k ℓ) : ℝ :=
  (sketchFrobSq c σ R i : ℝ) / ((ℓ : ℝ) ^ i * (Nat.factorial k : ℝ))

end KoanaKPaths.Main

end


