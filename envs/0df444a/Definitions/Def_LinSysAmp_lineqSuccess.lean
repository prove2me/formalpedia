-- Prove2me | Definitions.Def_LinSysAmp_lineqSuccess
-- name    : LinSysAmp_lineqSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:45.740436+00:00
-- url     : https://prove2.me/theorems/5894e930-8afc-4df7-9bfb-27620073b794
-- title:
--   $\mathsf{LINEQ}_{n,q}$: success probability on a random invertible system
-- statement:
--   The distributional problem $\mathsf{LINEQ}_{n,q}$ asks, given $M$ uniform in $\mathrm{GL}_n(\mathbb F_q)$ and $y$ uniform in $\mathbb F_q^n$, independent, to output $M^{-1}y$. For an oracle $\mathcal O$, whose answers are random, the success probability is
--   $$
--   \Pr_{M,y,\mathcal O}\bigl[\mathcal O(M,y)=M^{-1}y\bigr]=\frac{1}{|\mathrm{GL}_n(\mathbb F_q)|\,q^n}\sum_{M\in\mathrm{GL}_n(\mathbb F_q)}\ \sum_{y\in\mathbb F_q^n}\Pr\bigl[\mathcal O(M,y)=M^{-1}y\bigr],
--   $$
--   and $\mathcal O$ **solves $\mathsf{LINEQ}_{n,q}$ with probability $\alpha$** when this quantity is at least $\alpha$.
--
--   This item also defines the success function of the proof of the main theorem: for $N\in\mathrm{GL}_n(\mathbb F_q)$,
--   $$
--   h(N)=\frac1{q^n}\sum_{c\in\mathbb F_q^n}\Pr\bigl[\mathcal O(N,c)=N^{-1}c\bigr],
--   $$
--   the success probability of $\mathcal O$ on the matrix $N$ for a uniform right-hand side.
--
--   **Formalization Note** $\mathrm{GL}_n(F)$ is the subtype of matrices with nonzero determinant, and $M^{-1}$ is Mathlib's matrix inverse, which is the true inverse on this subtype. The average runs over invertible matrices only.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Definition 3.1, p.13 (PDF p.15); proof of Proposition 4.8, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_LinSysAmp_Machine

set_option autoImplicit false

open Matrix

namespace LinSysAmp

/-!
# LINEQ: solving a random invertible linear system (Definition 3.1)

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), Definition 3.1, p.13
(PDF p.15); the success function `h` of the proof of Proposition 4.8, p.22 (PDF p.24).

**Formalization Note.** `GL_n(F_q)` is the subtype `InvMat n F` of matrices with nonzero
determinant; `M⁻¹` is Mathlib's `Matrix.inv` (the true inverse on `InvMat`). An algorithm is an
`Oracle n F` (a randomized map to `PMF (Fin n → F)`); `Pr_{M,y,A}` averages its own probability of
returning `M⁻¹y` over `M` uniform in `GL_n(F_q)` and `y` uniform in `F_qⁿ`, independent. "Solves
`LINEQ_{n,q}` with probability `α`" is `α ≤ lineqSuccess O`.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `GL_n(F)`: the invertible `n × n` matrices over `F`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.2, p.13 (PDF p.15).) -/
abbrev InvMat (n : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] :=
  {M : Matrix (Fin n) (Fin n) F // M.det ≠ 0}

/-- Definition 3.1: `Pr_{M ← GL_n(F), y ← Fⁿ, O}[O(M, y) = M⁻¹y]`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 3.1, p.13 (PDF p.15).) -/
noncomputable def lineqSuccess {n : ℕ} (O : Oracle n F) : ℝ :=
  ((Fintype.card (InvMat n F) : ℝ) * (Fintype.card F : ℝ) ^ n)⁻¹ *
    ∑ M : InvMat n F, ∑ y : Fin n → F, (O M.1 y (M.1⁻¹ *ᵥ y)).toReal

/-- The success function of the proof of Proposition 4.8 (p.22): `h(N)` is the success probability
of `O` on the matrix `N ∈ GL_n(F)` for a uniform right-hand side,
`h(N) = q^{-n} Σ_c Pr[O(N, c) = N⁻¹c]`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, proof of Proposition 4.8, p.22 (PDF p.24).) -/
noncomputable def succFn {n : ℕ} (O : Oracle n F) (N : InvMat n F) : ℝ :=
  ((Fintype.card F : ℝ) ^ n)⁻¹ * ∑ c : Fin n → F, (O N.1 c (N.1⁻¹ *ᵥ c)).toReal

end LinSysAmp


