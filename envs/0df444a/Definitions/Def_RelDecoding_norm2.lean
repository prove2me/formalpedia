-- Prove2me | Definitions.Def_RelDecoding_norm2
-- name    : RelDecoding_norm2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:17:02.475064+00:00
-- url     : https://prove2.me/theorems/73e8dbbe-b75d-4fe3-8a52-ac867504c692
-- title:
--   Physical operator norm $\|X\|_{2,L}=\sqrt{\tau_L(X^*X)}$
-- statement:
--   Let $H_L=\mathbb C^{N_L}$ be a finite-dimensional Hilbert space and $\tau_L(X)=\operatorname{Tr}_{H_L}X/N_L$ the normalized trace of an operator $X$ on $H_L$. The **physical operator norm** is
--
--   $$\|X\|_{2,L}=\sqrt{\tau_L(X^*X)},$$
--
--   the norm of the operator inner product $\langle X,Y\rangle_L=\tau_L(X^*Y)$ of eq. (38). It is the norm of the vectorized operator $|X\rangle\rangle_L$, so it measures the normalization of the operator states that the paper transports.
--
--   **Formalization Note** Operators are complex $N_L\times N_L$ matrices, $X^*$ is the conjugate transpose, and $\tau_L$ is the platform's `normalizedTrace` (trace divided by the dimension). Since $\tau_L(X^*X)=\sum_{ij}|X_{ij}|^2/N_L\ge0$, the norm is the real square root of its real part. On an empty index type $\tau_L\equiv0$ (Lean's $x/0=0$).
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), §4.1, eq. (38), p.17 (pdf_page 17)

import Mathlib
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace

set_option autoImplicit false

namespace RelDecoding

open LIDT.MIPStarRE.Quantum

/-- The physical (normalized Hilbert–Schmidt) operator norm `∥X∥_{2,L} = √(τ_L(X∗X))` on
`B(H_L) = Matrix n n ℂ`, where `τ_L(X) = Tr X / N_L` is the normalized trace
(`LIDT.MIPStarRE.Quantum.normalizedTrace`). Shang, Stilck França, *From Simple Sources to
Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding*,
arXiv:2609.35101 (held version, sha256 d2be7859…), §4.1, eq. (38), p.17.

**Formalization Note.** `τ_L(X∗X) = Σᵢⱼ |Xᵢⱼ|² / N_L` is a nonnegative real number; the norm is
the real square root of its real part. `X∗` is the conjugate transpose (`star` on `Matrix`).
For an empty index type Lean's `x / 0 = 0` gives `τ ≡ 0`, so the norm is `0` there. -/
noncomputable def norm2 {n : Type*} [Fintype n] (X : Matrix n n ℂ) : ℝ :=
  Real.sqrt (normalizedTrace (star X * X)).re

end RelDecoding


