-- Prove2me | Definitions.Def_QNoiseStab_fourierVec
-- name    : QNoiseStab_fourierVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:55.962243+00:00
-- url     : https://prove2.me/theorems/9fa96cfb-4c55-4f83-a4cc-aa90cf8be21c
-- title:
--   Fourier basis state $|\hat z\rangle=m^{-n/2}\sum_x\omega_m^{z\cdot x}|x\rangle$ of $\mathbb C^{\mathbb Z_m^n}$
-- statement:
--   For $z\in\mathbb Z_m^{\,n}$ the Fourier basis state of the input register $\mathbb C^{\mathbb Z_m^n}$ is the tensor product of single-coordinate Fourier states,
--
--   $$
--   |\hat z\rangle=\bigotimes_{i\in[n]}|\hat z_i\rangle=\frac1{m^{n/2}}\sum_{x\in\mathbb Z_m^n}\omega_m^{\,z\cdot x}\,|x\rangle,\qquad \omega_m=e^{2\pi i/m}.
--   $$
--
--   These $m^n$ states form an orthonormal basis, in which both the low-degree projections $\Pi_{B_t}$ and the noise operators $T_p^A$ are diagonal.
--
--   **Formalization Note** The amplitude at $x$ is the product $\prod_i\langle x_i|\hat z_i\rangle$. Coordinates are $0$-based.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.3, p.10 (first display, |ẑ⟩ for n ≥ 1)

import Mathlib
import Definitions.Def_QNoiseStab_fourierKet

namespace QNoiseStab

/-- The Fourier basis state `|ẑ⟩ = ⊗_{i ∈ [n]} |ẑ_i⟩ = m^{-n/2} Σ_{x ∈ [m]ⁿ} ω_m^{z·x} |x⟩` of the
input register `ℂ^{Z_mⁿ}`, for `z ∈ Z_mⁿ` (Beame–Holman–Kornerup, *A Noise Operator Approach to
Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of
2026-11-02, sha256 814fe20e…), §2.3, p.10, first display).

**Formalization Note** The value at `x` is the product `∏_i ⟨x_i|ẑ_i⟩` of the single-coordinate
Fourier states `fourierKet` (primitive root `exp(2πi/m)`), i.e. the tensor-product form of the
display; it equals `m^{-n/2} ω_m^{z·x}`. Coordinates are `Fin n` (0-based). -/
noncomputable def fourierVec {n m : ℕ} [NeZero m] (z : Fin n → ZMod m) :
    EuclideanSpace ℂ (Fin n → ZMod m) :=
  WithLp.toLp 2 fun x => ∏ i, fourierKet (z i) (x i)

end QNoiseStab


