-- Prove2me | Definitions.Def_KnownFidelity_Rank_ginibreLaw
-- name    : KnownFidelity_Rank_ginibreLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:57.977757+00:00
-- url     : https://prove2.me/theorems/b8570233-71f7-4cce-a70e-5914b1499316
-- title:
--   Standard complex Ginibre law on $s\times s$ matrices
-- statement:
--   A **standard complex Ginibre matrix** $Z\in\mathbb C^{s\times s}$ has independent entries, each a standard complex Gaussian with density $\pi^{-1}e^{-|z|^2}$ on $\mathbb C$, i.e. with independent real and imaginary parts of variance $1/2$ (so $\mathbb E|Z_{ij}|^2=1$). This is the randomness of the size-biased Wishart model of §5.4 and of Lemma 5.13.
--
--   **Formalization Note** Each entry has the platform's law `BraneBrauer.Orthogonal.complexGaussian`; the law on matrices is the product over rows and columns, on the entrywise σ-algebra.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.4, p. 17 (PDF p. 19); Lemma 5.13, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian
import Definitions.Def_KnownFidelity_Rank_instMeasurableSpaceMatrix

open MeasureTheory

namespace KnownFidelity.Rank

/-- **The standard complex Ginibre law on `s × s` matrices.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.4, printed p. 17 (PDF p. 19): "Let Z be an r × r standard complex Ginibre
matrix: its entries are independent complex Gaussians with density π^{−1}e^{−|z|²}", and
Lemma 5.13, printed p. 22 (PDF p. 24) ("every standard complex Ginibre matrix Z_s ∈ C^{s×s}").

`ginibreLaw s` is the law of a matrix `Z ∈ ℂ^{s×s}` whose `s²` entries are independent standard
complex Gaussians.

**Formalization Note.** Each entry has the platform's law `BraneBrauer.Orthogonal.complexGaussian`
(independent real and imaginary parts `N(0, 1/2)`, i.e. density `π^{−1}e^{−|z|²}`, `E|z|² = 1`).
The law on matrices is the product measure over rows and columns, on the entrywise σ-algebra
`instMeasurableSpaceMatrix`. -/
noncomputable def ginibreLaw (s : ℕ) : Measure (Matrix (Fin s) (Fin s) ℂ) :=
  (Measure.pi fun _ : Fin s => Measure.pi fun _ : Fin s =>
    BraneBrauer.Orthogonal.complexGaussian : Measure (Fin s → Fin s → ℂ))

end KnownFidelity.Rank


