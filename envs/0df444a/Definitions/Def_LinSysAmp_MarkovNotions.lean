-- Prove2me | Definitions.Def_LinSysAmp_MarkovNotions
-- name    : LinSysAmp_MarkovNotions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:08.893686+00:00
-- url     : https://prove2.me/theorems/e8da6a89-f615-4425-a82c-d0ca28179424
-- title:
--   Reversible, positive semidefinite, second eigenvalue: Markov operators for the uniform law
-- statement:
--   Let $\Omega$ be a finite set and let $\langle f,g\rangle=\mathbb E_{x\leftarrow\Omega}[f(x)g(x)]$ be the inner product of the uniform distribution on real functions on $\Omega$. A Markov operator with transition probabilities $K(x,x')$ acts by $(Kf)(x)=\sum_{x'}K(x,x')f(x')$.
--
--   1. $K$ is **reversible** with respect to the uniform distribution if it is self-adjoint, which here means $K(x,x')=K(x',x)$.
--   2. $K$ is **positive semidefinite** if $\langle f,Kf\rangle\ge0$ for all $f$.
--   3. $K$ has **second eigenvalue at most $\lambda$** if $\langle f,Kf\rangle\le\lambda\|f\|^2$ for every $f$ orthogonal to the constant function $1$.
--
--   These three notions are the language of the spectral statements about the additive walk and the operator $K_k$.
--
--   **Formalization Note** The paper defines these notions for a general distribution $\pi$, and uses them in this mission only for uniform $\pi$. The factor $1/|\Omega|$ of the inner product appears on both sides of each inequality, so the inequalities are written with plain sums. Item 3 is the paper's quadratic-form bound on mean-zero functions and not a statement about a spectral radius.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.3 "Markov operators", p.14 (PDF p.16)

import Mathlib

set_option autoImplicit false

namespace LinSysAmp

/-!
# Markov operators for the uniform distribution (§3.3)

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.3 "Markov
operators", p.14 (PDF p.16).

A Markov operator with transition probabilities `K(x, x')` on a finite set `Ω` acts by
`(Kf)(x) = Σ_{x'} K(x, x') f(x')`. With `π` uniform on `Ω`, `⟨f, g⟩ = E_{x←π}[f(x)g(x)]`, and:

* `K` is **reversible** w.r.t. `π` if it is self-adjoint in `L²(π)`;
* `K` is **positive semidefinite** if `⟨f, Kf⟩ ≥ 0` for all `f`;
* `K` has **second eigenvalue at most `λ`** if `⟨f, Kf⟩ ≤ λ‖f‖²` for every `f` orthogonal to `1`.

**Formalization Note.** Only the uniform `π` is used in the paper's §4, so these are stated for it.
Self-adjointness in `L²(uniform)` is symmetry of the kernel, `K x x' = K x' x`. The normalizing factor
`1/|Ω|` of the inner product appears on both sides of each inequality and cancels, so the
inequalities are written with plain sums. "Second eigenvalue at most `λ`" is the paper's quadratic-form
bound on mean-zero functions, not a statement about a spectral radius.
-/

variable {Ω : Type*} [Fintype Ω]

/-- The action `(Kf)(x) = Σ_{x'} K(x, x') f(x')` of a kernel on real functions.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.3, p.14 (PDF p.16).) -/
def applyK (K : Ω → Ω → ℝ) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => ∑ x', K x x' * f x'

/-- Reversible with respect to the uniform distribution: self-adjoint in `L²(uniform)`, i.e. a
symmetric kernel.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.3, p.14 (PDF p.16).) -/
def IsReversibleUnif (K : Ω → Ω → ℝ) : Prop :=
  ∀ x x', K x x' = K x' x

/-- Positive semidefinite in `L²(uniform)`: `⟨f, Kf⟩ ≥ 0` for every `f`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.3, p.14 (PDF p.16).) -/
def IsPSDUnif (K : Ω → Ω → ℝ) : Prop :=
  ∀ f : Ω → ℝ, 0 ≤ ∑ x, f x * applyK K f x

/-- Second eigenvalue at most `lam` in `L²(uniform)`: `⟨f, Kf⟩ ≤ lam ‖f‖²` for every `f` with
`E[f] = 0`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.3, p.14 (PDF p.16).) -/
def SecondEigLe (K : Ω → Ω → ℝ) (lam : ℝ) : Prop :=
  ∀ f : Ω → ℝ, ∑ x, f x = 0 → ∑ x, f x * applyK K f x ≤ lam * ∑ x, f x ^ 2

end LinSysAmp


