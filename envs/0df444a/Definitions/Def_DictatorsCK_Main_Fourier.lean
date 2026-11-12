-- Prove2me | Definitions.Def_DictatorsCK_Main_Fourier
-- name    : DictatorsCK_Main_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:32:25.585425+00:00
-- url     : https://prove2.me/theorems/a6604e5f-d76c-481f-91a4-61a433436deb
-- title:
--   Fourier–Walsh coefficients, levels $W_k$, $\alpha$, $\delta$, half-differences $\partial_i$, Dirichlet energy, variance, $\mathrm{Ent}$ and coordinate projections $P_K$ on the uniform cube
-- statement:
--   Let $n\ge1$ and let $X$ be uniform on the cube $\{-1,1\}^n$; $\mathbb E h=2^{-n}\sum_x h(x)$ is the uniform average. The cube is encoded as $\mathtt{Cube}\,n=(\mathrm{Fin}\,n\to\mathrm{Bool})$, the cube of the published Courtade–Kumar statement, with sign coordinate $x_i=1$ when the $i$-th bit is `true` and $x_i=-1$ when it is `false`; a Boolean function $f:\{-1,1\}^n\to\{-1,1\}$ is a map $\mathtt{Cube}\,n\to\mathrm{Bool}$ read through the same encoding (`signEncoding`).
--
--   1. **Walsh characters and Fourier coefficients.** For $S\subseteq[n]$, $\chi_S(x)=\prod_{i\in S}x_i$ (with $\chi_\emptyset=1$), and for $h:\{-1,1\}^n\to\mathbb R$
--   $$\hat h(S)=\mathbb E[h(X)\chi_S(X)],\qquad \hat h(i)=\hat h(\{i\})=\mathbb E[h(X)X_i].$$
--   2. **Levels.** $W_k(h)=\sum_{|S|=k}\hat h(S)^2$, which is $0$ for $k>n$.
--   3. **Distance to a dictator.** For Boolean $f$, $\alpha(f)=\max_{i\in[n]}|\hat f(i)|$ and $\delta(f)=\min_{i\in[n],\,\sigma\in\{-1,1\}}\mathbb P(f(X)\ne\sigma X_i)$ (2.1).
--   4. **Half-differences and energy.** $\partial_i h(x_{-i})=\tfrac12\big(h(x_{-i},1)-h(x_{-i},-1)\big)$, viewed on the full cube ignoring $x_i$; $L_ih(x)=\tfrac12(h(x)-h(x^{\oplus i}))$ (the published `cubeDerivative`), $L=\sum_iL_i$, and the Dirichlet energy $\mathrm{Dir}(h)=\mathbb E[hLh]$.
--   5. **Variance and entropy.** $\mathrm{Var}(h)=\mathbb E h^2-(\mathbb E h)^2$ and, for $v\ge0$, $\mathrm{Ent}(v)=\mathbb E[v\log v]-\mathbb E v\log\mathbb E v$ with $0\log0=0$.
--   6. **Coordinate projection.** For $K\subseteq[n]$, $(P_Kv)(x)=\mathbb E_{X_{K^c}}v(x_K,X_{K^c})$ (7.1): keep the coordinates in $K$, average over the others.
--
--   These are the standard uniform-cube Fourier objects that every milestone of this mission is stated in.
--
--   **Formalization Note.** Coordinates are indexed by `Fin n` (the paper's $1,\dots,n$ shifted to $0,\dots,n-1$). $\alpha$ is a real supremum `⨆ i` and $\delta$ a real infimum `⨅ (i, σ)` over a finite index set; both are the maximum/minimum when $n\ge1$ (and $0$ for $n=0$, a case the paper excludes). $\log$ is `Real.log`, whose value $\log0=0$ gives the convention $0\log0=0$.
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), pp. 7–10 (PDF 8–11), §2.1–2.4, (2.1), (2.4); p. 11 (PDF 12), §3.1 (Ent); p. 35 (PDF 36), (7.1)

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

noncomputable section

/-- The sign coordinate `x_i ∈ {−1, 1}` of a cube point `x : Fin n → Bool`
(`true ↦ 1`, `false ↦ −1`, the encoding of `signEncoding`). -/
def coord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

/-- The Walsh character `χ_S(x) = ∏_{i ∈ S} x_i`, with `χ_∅ = 1`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  ∏ i ∈ S, coord x i

/-- The Fourier–Walsh coefficient `ĥ(S) = E[h(X) χ_S(X)]` for the uniform average `E`. -/
def fourierCoeff {n : ℕ} (h : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  cubeAverage (fun x => h x * chi S x)

/-- The singleton coefficient `ĥ(i) = ĥ({i}) = E[h(X) X_i]`. -/
def singletonCoeff {n : ℕ} (h : Cube n → ℝ) (i : Fin n) : ℝ :=
  fourierCoeff h {i}

/-- The Fourier weight at level `k`: `W_k(h) = ∑_{|S| = k} ĥ(S)^2` (an empty sum, `0`, for `k > n`). -/
def levelWeight {n : ℕ} (h : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k), fourierCoeff h S ^ 2

/-- `α(f) = max_i |f̂(i)|` for a Boolean `f`, read through `signEncoding`
(a maximum over the nonempty finite index set when `n ≥ 1`). -/
def maxSingleton {n : ℕ} (f : Cube n → Bool) : ℝ :=
  ⨆ i : Fin n, |singletonCoeff (signEncoding f) i|

/-- `δ(f) = min_{i ∈ [n], σ ∈ {−1,1}} P(f(X) ≠ σ X_i)`, uniform `X`; the sign `σ` is
encoded by a Boolean (`true ↦ 1`). -/
def dictatorDistance {n : ℕ} (f : Cube n → Bool) : ℝ :=
  ⨅ p : Fin n × Bool,
    cubeAverage (fun x =>
      if signEncoding f x = (if p.2 then (1 : ℝ) else -1) * coord x p.1 then (0 : ℝ) else 1)

/-- The half-difference `∂_i h(x_{−i}) = (h(x_{−i}, 1) − h(x_{−i}, −1)) / 2`, viewed as a
function on the full cube that ignores `x_i` (coordinate value `1` is `true`). -/
def halfDiff {n : ℕ} (i : Fin n) (h : Cube n → ℝ) (x : Cube n) : ℝ :=
  (h (Function.update x i true) - h (Function.update x i false)) / 2

/-- The cube Laplacian `L h = ∑_i L_i h`, where `L_i h(x) = (h(x) − h(x^{⊕i})) / 2` is
`cubeDerivative`. -/
def laplacian {n : ℕ} (h : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ i, cubeDerivative i h x

/-- The Dirichlet (quadratic) energy `Dir(h) = E[h L h]`. -/
def dirichlet {n : ℕ} (h : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => h x * laplacian h x)

/-- The variance `Var(h) = E[h^2] − (E h)^2` under the uniform measure. -/
def variance {n : ℕ} (h : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => h x ^ 2) - cubeAverage h ^ 2

/-- The coordinate projection `(P_K v)(x) = E_{X_{K^c}} v(x_K, X_{K^c})`: keep the coordinates
in `K` and average uniformly over the others. -/
def proj {n : ℕ} (K : Finset (Fin n)) (v : Cube n → ℝ) (x : Cube n) : ℝ :=
  cubeAverage (fun z : Cube n => v (fun i => if i ∈ K then x i else z i))

/-- The entropy functional `Ent(v) = E[v log v] − E v · log E v` (with `0 log 0 = 0`, which
`Real.log 0 = 0` provides). -/
def ent {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => v x * Real.log (v x)) - cubeAverage v * Real.log (cubeAverage v)

end

end DictatorsCK.Main


