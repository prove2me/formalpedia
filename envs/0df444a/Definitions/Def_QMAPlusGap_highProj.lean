-- Prove2me | Definitions.Def_QMAPlusGap_highProj
-- name    : QMAPlusGap_highProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:51.600215+00:00
-- url     : https://prove2.me/theorems/6ef5b84e-3e20-47e2-a0b5-c66797f144dc
-- title:
--   Spectral projector $\mathbf 1_{(1/m,1]}(\rho_1)$
-- statement:
--   For a Hermitian operator $\rho_1$ on $\mathcal H$ and $m\ge1$, $\mathbf 1_{(1/m,1]}(\rho_1)$ is the orthogonal projector onto the span of the eigenvectors of $\rho_1$ whose eigenvalues are larger than $1/m$: if $\rho_1=\sum_i\lambda_i|v_i\rangle\langle v_i|$, then
--   $$
--   \mathbf 1_{(1/m,1]}(\rho_1)=\sum_{i:\ \lambda_i>1/m}|v_i\rangle\langle v_i| ,
--   $$
--   independently of the choice of eigenbasis.
--
--   **Formalization Note** It is the continuous functional calculus of the indicator $x\mapsto[x>1/m]$ (any function is continuous on the finite spectrum). For a density operator the eigenvalues lie in $[0,1]$, so the indicator of $(1/m,\infty)$ is the paper's indicator of $(1/m,1]$.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 13, p.27

import Mathlib

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder

namespace QMAPlusGap

/-- The **spectral projector `1_{(1/m,1]}(ρ₁)`**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 13, p.27: "the orthogonal projector onto the span of
the eigenvectors of ρ₁ whose eigenvalues are larger than 1/m".

It is the continuous functional calculus of the indicator `x ↦ [1/m < x]` applied to `ρ₁`, which for a Hermitian
`ρ₁` is `Σ_{λ_i > 1/m} |v_i⟩⟨v_i|` for any orthonormal eigenbasis `(v_i)` and does not depend on the choice of
eigenbasis.

**Formalization Note** `cfc` of a function on the finite spectrum is always defined (a function on a finite set is
continuous on it); for a non-Hermitian argument `cfc` returns `0`, but every use applies it to a reduced density
operator, which is Hermitian. For a density operator the eigenvalues lie in `[0,1]`, so the indicator of
`(1/m, ∞)` is the paper's indicator of `(1/m, 1]`. -/
noncomputable def highProj {ι : Type} [Fintype ι] [DecidableEq ι] (ρ₁ : Matrix ι ι ℂ) (m : ℕ) :
    Matrix ι ι ℂ :=
  cfc (fun x : ℝ => if 1 / (m : ℝ) < x then (1 : ℝ) else 0) ρ₁

end QMAPlusGap


