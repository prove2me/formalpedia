-- Prove2me | Definitions.Def_MatrixQuantumSampler595_Correspondence_MatrixSampler
-- name    : MatrixQuantumSampler595_Correspondence_MatrixSampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:56.687174+00:00
-- url     : https://prove2.me/theorems/493a5bbb-360c-4bd0-93bf-1009d871b601
-- title:
--   Definition 1.2 — ordinary and strong matrix samplers
-- statement:
--   Let $n,m,t,D$ be natural numbers and let $F:\{0,1\}^n\times[t]\to\{0,1\}^m$ be any map; the seed set $[t]=\{1,\dots,t\}$ is indexed by $\{0,\dots,t-1\}$. Matrices are complex $D\times D$ matrices, measured in the Euclidean operator norm
--   $$\|A\|=\max_{\|v\|_2=1}\|Av\|_2 .$$
--
--   For a family of tests $f_1,\dots,f_t:\{0,1\}^m\to\mathbb C^{D\times D}$ and a string $x\in\{0,1\}^n$, the **sampling error** at $x$ is
--   $$A_f(x)=\frac1t\sum_{i=1}^t\Bigl(f_i(F(x,i))-\mathbb E_{Z\sim U_m}f_i(Z)\Bigr),\qquad \mathbb E_{Z\sim U_m}f_i(Z)=2^{-m}\sum_{z\in\{0,1\}^m}f_i(z).$$
--
--   1. $F$ is a **(ordinary) $D$-dimensional $(\delta,\varepsilon)$ matrix sampler** if for every $f:\{0,1\}^m\to\mathbb C^{D\times D}$ with $\|f(z)\|\le1$ for all $z$, taking $f_i=f$ for every $i$,
--   $$\Pr_{R\sim U_n}\bigl[\|A_f(R)\|>\varepsilon\bigr]=2^{-n}\,\bigl|\{x:\|A_f(x)\|>\varepsilon\}\bigr|\le\delta .$$
--   2. $F$ is a **strong $D$-dimensional $(\delta,\varepsilon)$ matrix sampler** if the same bound holds for every sequence $f_1,\dots,f_t$ with $\|f_i(z)\|\le1$ for all $i,z$.
--
--   The tests need not be Hermitian, positive or commuting. The strong notion lets the test depend on the sample position. These are the sampler predicates of the extractor–sampler correspondence (Theorem 1.5).
--
--   **Formalization Note** Bit strings are `Fin n → Bool`; the norm is Mathlib's scoped `Matrix.Norms.L2Operator` instance (the operator norm of `Matrix.toEuclideanCLM`). The definition is total in $t$: at $t=0$ the factor $1/t$ is Lean's $0$; Theorem 1.5 assumes $t\ge1$.
-- source:
--   Kuan Cheng, Ruiyang Wu, Matrix Samplers and Quantum-Proof Extractors: Their Correspondence and Almost-Optimal Constructions, STOC 2027 submission #595 (October 2026), Definition 1.2, p.2; Eq. (3.1), p.14

import Mathlib

open scoped Matrix.Norms.L2Operator

namespace MatrixQuantumSampler595.Correspondence

/-- Bit strings of length `n`, the paper's `{0,1}^n` (Definition 1.2, p.2). -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- Definition 1.2 (p.2) and Eq. (3.1) (p.14): for a map `F : {0,1}^n × [t] → {0,1}^m`
(the seed set `[t]` indexed by `Fin t`) and tests `f i : {0,1}^m → ℂ^{D×D}`, the matrix
`A_f(x) = (1/t) ∑_i (f i (F x i) - E_{Z ∼ U_m} f i Z)`, with `E_Z f i Z = 2^{-m} ∑_z f i z`. -/
noncomputable def samplingError {n m t D : ℕ} (F : BitString n → Fin t → BitString m)
    (f : Fin t → BitString m → Matrix (Fin D) (Fin D) ℂ) (x : BitString n) :
    Matrix (Fin D) (Fin D) ℂ :=
  (t : ℂ)⁻¹ • ∑ i : Fin t, (f i (F x i) - ((2 : ℂ) ^ m)⁻¹ • ∑ z : BitString m, f i z)

/-- The probability, for `R` uniform on `{0,1}^n`, that the sampling error exceeds `ε` in the
Euclidean operator norm `‖A‖ = max_{‖v‖₂ = 1} ‖A v‖₂`. -/
noncomputable def badProbability {n m t D : ℕ} (F : BitString n → Fin t → BitString m)
    (f : Fin t → BitString m → Matrix (Fin D) (Fin D) ℂ) (ε : ℝ) : ℝ :=
  ((Finset.univ.filter fun x : BitString n => ε < ‖samplingError F f x‖).card : ℝ) /
    (2 : ℝ) ^ n

/-- Definition 1.2 (p.2): `F` is a (ordinary) `D`-dimensional `(δ, ε)` matrix sampler if for
every `f : {0,1}^m → ℂ^{D×D}` with `‖f z‖ ≤ 1` for all `z`, the same test used at every
position, `Pr_R[‖(1/t) ∑_i f(F(R,i)) - E_Z f(Z)‖ > ε] ≤ δ`. -/
def IsMatrixSampler {n m t : ℕ} (F : BitString n → Fin t → BitString m) (D : ℕ)
    (δ ε : ℝ) : Prop :=
  ∀ f : BitString m → Matrix (Fin D) (Fin D) ℂ, (∀ z, ‖f z‖ ≤ 1) →
    badProbability F (fun _ => f) ε ≤ δ

/-- Definition 1.2 (p.2): `F` is a strong `D`-dimensional `(δ, ε)` matrix sampler if for every
sequence `f_1, …, f_t : {0,1}^m → ℂ^{D×D}` with `‖f_i z‖ ≤ 1` for all `i, z`,
`Pr_R[‖(1/t) ∑_i (f_i(F(R,i)) - E_Z f_i(Z))‖ > ε] ≤ δ`. -/
def IsStrongMatrixSampler {n m t : ℕ} (F : BitString n → Fin t → BitString m) (D : ℕ)
    (δ ε : ℝ) : Prop :=
  ∀ f : Fin t → BitString m → Matrix (Fin D) (Fin D) ℂ, (∀ i z, ‖f i z‖ ≤ 1) →
    badProbability F f ε ≤ δ

end MatrixQuantumSampler595.Correspondence


