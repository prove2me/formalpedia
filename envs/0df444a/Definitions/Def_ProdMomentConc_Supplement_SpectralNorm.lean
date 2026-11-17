-- Prove2me | Definitions.Def_ProdMomentConc_Supplement_SpectralNorm
-- name    : ProdMomentConc_Supplement_SpectralNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:32:48.361846+00:00
-- url     : https://prove2.me/theorems/ae772e97-f62a-4089-95c6-c09962c65fef
-- title:
--   Ergodicity, $L^2(\pi)$ norms and the spectral norm $\lambda(M)$ of a finite Markov chain
-- statement:
--   Let $M$ be a transition matrix on the finite state space $[n]$ and $\pi$ a probability vector on $[n]$. Functions $f:[n]\to\mathbb R$ form the space $L^2(\pi)$ with inner product and norm
--   $$\langle f,g\rangle_\pi=\sum_{x\in[n]}\pi(x)f(x)g(x),\qquad \|f\|_{2,\pi}=\langle f,f\rangle_\pi^{1/2},$$
--   and stationary mean $\mathbb E_\pi f=\sum_x \pi(x)f(x)$. The matrix acts on functions by $(Mf)(x)=\sum_y M(x,y)f(y)$.
--
--   1. $M$ is **ergodic** (irreducible and aperiodic) if some power $M^N$ has all entries positive.
--   2. The **spectral norm** of $M$ (Definition 2.8, following Chung et al.) is
--   $$\lambda(M)=\sup_{\substack{f\in L^2(\pi),\ f\neq 0\\ \mathbb E_\pi f=0}}\frac{\|Mf\|_{2,\pi}}{\|f\|_{2,\pi}},$$
--   the operator norm of $M$ on the mean-zero subspace of $L^2(\pi)$.
--   3. For a probability distribution $\varphi$ on $[n]$, $\|\varphi\|_{\pi^{-1}}=\big(\sum_x \varphi(x)^2/\pi(x)\big)^{1/2}$.
--
--   These quantities state the spectral product bound for Markov chains (Theorem 5.1).
--
--   **Formalization Note** For a finite stochastic matrix, irreducible and aperiodic is equivalent to primitivity, which is the form used. $\lambda(M)$ is an `sSup` of reals; when $\pi$ has full support (which ergodicity and stationarity force) the set is bounded, and for $n\le1$ it is empty and the value is $0$, the norm of the zero operator. It is not the second-largest eigenvalue, and no reversibility is assumed.
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §2.4, p.10 (PDF p.10: ergodic chain, ⟨f,g⟩_π, ‖f‖_{2,π}, ‖φ‖_{π⁻¹}, E_π f, function convention (Mf)(x)); Definition 2.8, p.11 (PDF p.11: λ(M))

import Mathlib

namespace ProdMomentConc.Supplement

/-- **Ergodic finite Markov chain** (Saks, Srinivasan, Valieva, *Concentration from Product Moments
via an Additional Element of Randomness*, arXiv:2608.04125, held version, sha256 5218e9d0…, §2.4,
p.10: "Let M be an ergodic Markov chain on a finite state space [n]").

A transition matrix `M` on a finite state space is ergodic (irreducible and aperiodic) iff some power
of it has all entries positive.

**Formalization Note.** For a finite stochastic matrix, "irreducible and aperiodic" is equivalent to
primitivity (`∃ N, M^N > 0` entrywise); primitivity is the form used here. Stochasticity is a separate
hypothesis (the published `FiniteTD.Markov.IsStochastic`). -/
def IsErgodic {n : ℕ} (M : Fin n → Fin n → ℝ) : Prop :=
  ∃ N : ℕ, ∀ x y, 0 < (Matrix.of M ^ N) x y

/-- The inner product `⟨f, g⟩_π = ∑ₓ π(x) f(x) g(x)` of `L²(π)` (§2.4, p.10). -/
def piInner {n : ℕ} (π f g : Fin n → ℝ) : ℝ :=
  ∑ x, π x * f x * g x

/-- The norm `‖f‖_{2,π} = ⟨f, f⟩_π^{1/2}` of `L²(π)` (§2.4, p.10). -/
noncomputable def piNorm {n : ℕ} (π f : Fin n → ℝ) : ℝ :=
  Real.sqrt (piInner π f f)

/-- The stationary mean `E_π f = ∑ₓ π(x) f(x)` (§2.4, p.10). -/
def piMean {n : ℕ} (π f : Fin n → ℝ) : ℝ :=
  ∑ x, π x * f x

/-- The action `(Mf)(x) = ∑_y M(x, y) f(y)` of a transition matrix on functions (function
convention, §2.4, p.10). -/
def applyM {n : ℕ} (M : Fin n → Fin n → ℝ) (f : Fin n → ℝ) : Fin n → ℝ :=
  fun x => ∑ y, M x y * f y

/-- **Spectral norm** `λ(M)` (Definition 2.8, p.11, following Chung et al.):
`λ(M) = sup { ‖Mf‖_{2,π} / ‖f‖_{2,π} : f ∈ L²(π), f ≠ 0, E_π f = 0 }`, the operator norm of `M`
restricted to the mean-zero subspace of `L²(π)`.

**Formalization Note.** The supremum is `sSup` of a set of reals. For a stationary `π` with full
support (which ergodicity forces) the set is bounded (finite dimension) and nonempty when `n ≥ 2`;
for `n ≤ 1` the mean-zero subspace is `{0}`, the set is empty and `sSup ∅ = 0`, which is the norm of
the zero operator. This is the norm on mean-zero functions, not the second-largest eigenvalue; no
reversibility is assumed. -/
noncomputable def specNorm {n : ℕ} (M : Fin n → Fin n → ℝ) (π : Fin n → ℝ) : ℝ :=
  sSup {c : ℝ | ∃ f : Fin n → ℝ, f ≠ 0 ∧ piMean π f = 0 ∧
    c = piNorm π (applyM M f) / piNorm π f}

/-- The norm `‖φ‖_{π⁻¹} = (∑ₓ φ(x)² / π(x))^{1/2}` of an initial distribution `φ` (§2.4, p.10). -/
noncomputable def piInvNorm {n : ℕ} (π φ : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ x, φ x ^ 2 / π x)

end ProdMomentConc.Supplement


