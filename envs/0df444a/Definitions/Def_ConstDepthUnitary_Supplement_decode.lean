-- Prove2me | Definitions.Def_ConstDepthUnitary_Supplement_decode
-- name    : ConstDepthUnitary_Supplement_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:23:20.419605+00:00
-- url     : https://prove2.me/theorems/22793e3f-6fd9-450e-9e7b-ee77d16cd257
-- title:
--   The decoding map $E^\dagger:L^2(\mathbb R^N)\to\mathbb C^N$
-- statement:
--   The **decoding map** is the adjoint $E^\dagger=\sum_{y\in[N]}|y\rangle\langle\psi_y|$ of the encoding isometry, a coisometry $L^2(\mathbb R^N)\to\mathbb C^N$. Its $y$-th coordinate is the $L^2$ inner product with $\psi_y$:
--   $$
--   (E^\dagger f)_y=\langle\psi_y,f\rangle=\int_{\mathbb R^N}\overline{\psi_y(v)}\,f(v)\,dv ,\qquad y\in[N].
--   $$
--
--   **Formalization Note** The inner product is conjugate-linear in the first slot and taken with respect to Lebesgue measure on `EuclideanSpace ℝ (Fin N)`. The Bochner integral is $0$ for a non-integrable integrand; the mission applies $E^\dagger$ only to Schwartz functions, where it is the $L^2$ pairing.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.3, Eq. (26) and the sentence after it, p.20

import Mathlib
import Definitions.Def_ConstDepthUnitary_Supplement_excState

namespace ConstDepthUnitary

namespace Supplement

/-- The decoding map `E† = ∑_{y ∈ [N]} |y⟩⟨ψ_y| : L²(ℝ^N) → ℂ^N`, the adjoint of the encoding isometry:
`(E† f)_y = ⟨ψ_y, f⟩ = ∫ conj(ψ_y(v)) f(v) dv`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.3, Eq. (26) and the sentence after it, p.20.

**Formalization Note** The inner product of `L²(ℝ^N)` is conjugate-linear in the first slot and taken
against Lebesgue measure (`volume`) on `EuclideanSpace ℝ (Fin N)`. The Bochner integral is `0` for a
non-integrable integrand; the mission applies `decode` only to Schwartz functions, where it is the
`L²` pairing. -/
noncomputable def decode {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℂ) (y : Fin N) : ℂ :=
  ∫ v : EuclideanSpace ℝ (Fin N), (starRingEnd ℂ) (excState y v) * f v

end Supplement

end ConstDepthUnitary


