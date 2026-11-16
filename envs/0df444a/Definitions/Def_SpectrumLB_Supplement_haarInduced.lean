-- Prove2me | Definitions.Def_SpectrumLB_Supplement_haarInduced
-- name    : SpectrumLB_Supplement_haarInduced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:58:16.789197+00:00
-- url     : https://prove2.me/theorems/adc319f3-f587-4231-8545-e1318d112de2
-- title:
--   Haar-induced state $\rho_{\mathrm{Haar}}=\mathrm{Tr}_2[|\psi\rangle\langle\psi|]$ of a column of a unitary on $\mathbb C^d\otimes\mathbb C^d$
-- statement:
--   Identify $\mathbb C^d\otimes\mathbb C^d$ with $\mathbb C^{d^2}$. For a unitary $V$ on this space and a basis index $c$, let $|\psi\rangle=V e_c$ be the $c$-th column of $V$, a unit vector. Its reduced state on the first tensor factor is
--
--   $$
--   \rho_{\mathrm{Haar}}=\mathrm{Tr}_2\big[|\psi\rangle\langle\psi|\big],\qquad
--   (\rho_{\mathrm{Haar}})_{ij}=\sum_{k=1}^d\psi_{(i,k)}\,\overline{\psi_{(j,k)}} .
--   $$
--
--   When $V$ is Haar-distributed on $U(d^2)$, $|\psi\rangle$ is a Haar-random unit vector of $\mathbb C^d\otimes\mathbb C^d$, so $\rho_{\mathrm{Haar}}$ is the random induced state of the second ensemble of §4.
--
--   **Formalization Note** The identification of $\mathbb C^d\otimes\mathbb C^d$ with $\mathbb C^{d^2}$ is Mathlib's `finProdFinEquiv`; the first coordinate of a pair is the kept factor and the second the traced-out one.
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, §4, Eq. (4.2), p. 15

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder ComplexConjugate

namespace SpectrumLB.Supplement

/-- **The Haar-induced state `ρ_Haar = Tr₂[|ψ⟩⟨ψ|]` for `|ψ⟩ = V e_c`.**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
§4, Eq. (4.2), p. 15: "Draw a Haar random unit vector |ψ⟩ from C^d ⊗ C^d and set
ρ_Haar := Tr₂[|ψ⟩⟨ψ|], where Tr₂ denotes the partial trace over the second tensor factor."

For a unitary `V` on `ℂ^{d²} ≅ ℂ^d ⊗ ℂ^d` and a column index `c`, `|ψ⟩ = V e_c` is the `c`-th column of
`V`, and `haarInduced d c V` is its reduced state on the first factor:
`(ρ_Haar)_{ij} = Σ_k ψ_{(i,k)} · conj(ψ_{(j,k)})`.

**Formalization Note.** `ℂ^d ⊗ ℂ^d` is identified with `ℂ^{d·d}` through `finProdFinEquiv`
(`(i, k)` ↦ a basis index of `Fin (d * d)`); `i` is the first factor and `k`, the summed index, the
second. When `V` is Haar-distributed on `U(d²)`, every column `V e_c` is uniformly distributed on the
unit sphere of `ℂ^{d²}`, which is the paper's Haar-random unit vector. -/
def haarInduced (d : ℕ) (c : Fin (d * d)) (V : Matrix.unitaryGroup (Fin (d * d)) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ∑ k : Fin d,
    (V : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) (finProdFinEquiv (i, k)) c *
      conj ((V : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) (finProdFinEquiv (j, k)) c)

end SpectrumLB.Supplement


