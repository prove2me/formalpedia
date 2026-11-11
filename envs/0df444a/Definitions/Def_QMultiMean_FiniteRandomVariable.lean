-- Prove2me | Definitions.Def_QMultiMean_FiniteRandomVariable
-- name    : QMultiMean_FiniteRandomVariable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:07:16.534597+00:00
-- url     : https://prove2.me/theorems/523c8bd2-2373-4b35-bb5a-959b2c35c03c
-- title:
--   Finite random variables in $\mathbb R^d$: mean, $\mathrm{Tr}(\Sigma)$, $\|\Sigma\|$, norms, truncations and random experiments
-- statement:
--   A **finite random variable** is a map $X:\Omega\to\mathbb R^d$ on a finite sample set $\Omega$ carrying a probability mass function $P:\Omega\to[0,1]$, $\sum_\omega P(\omega)=1$. Its **mean** and the trace and spectral norm of its **covariance matrix** $\Sigma=\mathbb E[XX^\top]-\mathbb E[X]\mathbb E[X]^\top$ are
--   $$\mu=\sum_{\omega}P(\omega)X(\omega),\qquad \mathrm{Tr}(\Sigma)=\sum_\omega P(\omega)\|X(\omega)-\mu\|_2^2,\qquad \|\Sigma\|=\sup_{\|v\|_2=1}\sum_\omega P(\omega)\langle v,X(\omega)-\mu\rangle^2 .$$
--   The module also fixes the expectation $\mathbb E[f]=\sum_\omega P(\omega)f(\omega)$ and probability $\Pr[A]=\sum_{\omega\in A}P(\omega)$ of functions and events of the sample, the $\ell_\infty$ norm $\|x\|_\infty=\max_i|x_i|$, the **truncation**
--   $$[\![x]\!]_a^b=\begin{cases}x&\text{if }a<\|x\|_2\le b,\\0&\text{otherwise,}\end{cases}$$
--   its one-sided version $[\![x]\!]_a^{+\infty}$ (keep $x$ when $\|x\|_2>a$), the scalar truncation $[\![y]\!]_a^b$ (with $|y|$ in place of $\|x\|_2$), and the law of $K$ **random experiments** followed by a classical map $f$: the probability that $f(X(\omega_1),\dots,X(\omega_K))\in S$ for independent $\omega_i\sim P$,
--   $$\sum_{(\omega_1,\dots,\omega_K)\in\Omega^K}\Big(\prod_i P(\omega_i)\Big)\mathbf 1\big[f(X(\omega_1),\dots,X(\omega_K))\in S\big].$$
--
--   These are the objects every statement of the paper is written in.
--
--   **Formalization Note** $\Omega=\mathrm{Fin}(N+1)$ and $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with its $\ell_2$ norm. $\mathrm{Tr}(\Sigma)$ and $\|\Sigma\|$ are written as the trace and the largest directional variance, which equal the trace and the spectral norm of $\Sigma$. The supremum defining $\|\Sigma\|$ is over a nonempty bounded set for $d\ge1$ (and is $0$ for $d=0$).
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, pp.6–7, Definitions 2.1, 2.2, 2.4 and the truncation after Definition 2.1

import Mathlib

set_option autoImplicit false

namespace QMultiMean

/-- The ambient space `ℝ^d` with its Euclidean (`ℓ₂`) norm and inner product (Cornelissen, Hamoudi,
Jerbi, *Near-Optimal Quantum Algorithms for Multivariate Mean Estimation*, arXiv:2111.09787v2,
Definition 2.1, p.6). -/
abbrev Vec (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- A probability mass function on the finite sample set `Ω = Fin (N+1)` (arXiv:2111.09787v2,
Definition 2.2, p.6): nonnegative weights summing to one.

**Formalization Note.** Every finite sample set containing the distinguished point `0` of
Definition 2.5 is in bijection with `Fin (N+1)`, with `0 ↦ 0`. -/
def IsPMF {N : ℕ} (P : Fin (N + 1) → ℝ) : Prop :=
  (∀ ω, 0 ≤ P ω) ∧ ∑ ω, P ω = 1

/-- The expectation `E[f] = Σ_ω P(ω) f(ω)` of a real function of the sample under `P`. -/
def expect {N : ℕ} (P : Fin (N + 1) → ℝ) (f : Fin (N + 1) → ℝ) : ℝ :=
  ∑ ω, P ω * f ω

open Classical in
/-- The probability `Pr[A] = Σ_{ω : A ω} P(ω)` of an event of the sample under `P`. -/
noncomputable def prob {N : ℕ} (P : Fin (N + 1) → ℝ) (A : Fin (N + 1) → Prop) : ℝ :=
  ∑ ω ∈ Finset.univ.filter A, P ω

/-- The mean `µ = E[X] = Σ_ω P(ω) X(ω)` of a finite random variable `X : Ω → ℝ^d`
(arXiv:2111.09787v2, Definition 2.2, p.6). -/
noncomputable def mean {N d : ℕ} (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d) : Vec d :=
  ∑ ω, P ω • X ω

/-- The trace `Tr(Σ)` of the covariance matrix `Σ = E[XXᵀ] − E[X]E[X]ᵀ` of Definition 2.2, p.6
(arXiv:2111.09787v2).

**Formalization Note.** Encoded as `Σ_ω P(ω) ‖X(ω) − µ‖₂²`, which equals `Tr(E[XXᵀ] − µµᵀ)`
for a probability mass function `P`. -/
noncomputable def traceCov {N d : ℕ} (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d) : ℝ :=
  ∑ ω, P ω * ‖X ω - mean P X‖ ^ 2

/-- The spectral norm `‖Σ‖` (the induced `ℓ₂` norm of Definition 2.1, p.6) of the covariance matrix
`Σ` of Definition 2.2, p.6 (arXiv:2111.09787v2).

**Formalization Note.** Encoded as the largest directional variance
`sup_{‖v‖₂ = 1} Σ_ω P(ω) ⟨v, X(ω) − µ⟩²`, which equals the spectral norm of the positive
semidefinite matrix `Σ` when `P` is a probability mass function. The supremum is over the unit sphere,
which is nonempty for `d ≥ 1`, and the set is bounded above by `Tr(Σ)`; for `d = 0` the value is `0`,
which is the spectral norm of the empty matrix. -/
noncomputable def covNorm {N d : ℕ} (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d) : ℝ :=
  ⨆ v : {v : Vec d // ‖v‖ = 1}, ∑ ω, P ω * (inner ℝ (v : Vec d) (X ω - mean P X)) ^ 2

/-- The `ℓ∞` norm `‖x‖∞ = max_{i ∈ [d]} |x_i|` of Definition 2.1, p.6 (arXiv:2111.09787v2).

**Formalization Note.** `Vec d` carries the `ℓ₂` norm, so the `ℓ∞` norm is a separate function.
The supremum is over the finite index set; at `d = 0` it is `0`. -/
noncomputable def supNorm {d : ℕ} (x : Vec d) : ℝ :=
  ⨆ i : Fin d, |x i|

/-- The truncation `⟦x⟧_a^b = x if a < ‖x‖₂ ≤ b, 0 otherwise` (arXiv:2111.09787v2, p.6, after
Definition 2.1), for `0 ≤ a < b`. -/
noncomputable def trunc {d : ℕ} (a b : ℝ) (x : Vec d) : Vec d :=
  if a < ‖x‖ ∧ ‖x‖ ≤ b then x else 0

/-- The one-sided truncation `⟦x⟧_a^{+∞} = x if a < ‖x‖₂, 0 otherwise`, used in display (4) of the
proof of Theorem 3.4, p.13 (arXiv:2111.09787v2). -/
noncomputable def truncTop {d : ℕ} (a : ℝ) (x : Vec d) : Vec d :=
  if a < ‖x‖ then x else 0

/-- The scalar truncation `⟦y⟧_a^b = y if a < |y| ≤ b, 0 otherwise` (the case `d = 1` of the
truncation on p.6, arXiv:2111.09787v2), used as `⟦α⟨u, X⟩⟧_0^1` on p.9. -/
noncomputable def truncR (a b : ℝ) (y : ℝ) : ℝ :=
  if a < |y| ∧ |y| ≤ b then y else 0

open Classical in
/-- **Random experiments** (Definition 2.4, p.7, arXiv:2111.09787v2), `K` of them, followed by a
classical post-processing `f`: the probability that `f(X(ω₁), …, X(ω_K)) ∈ S` when `ω₁, …, ω_K` are
drawn independently according to `P`,
`Σ_{ω⃗ ∈ Ω^K} (Π_i P(ω_i)) · 1[f(X ∘ ω⃗) ∈ S]`. -/
noncomputable def sampleProb {N : ℕ} {V Out : Type} (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → V)
    (K : ℕ) (f : (Fin K → V) → Out) (S : Set Out) : ℝ :=
  ∑ w : Fin K → Fin (N + 1), (∏ i, P (w i)) * (if f (fun i => X (w i)) ∈ S then 1 else 0)

end QMultiMean


