-- Prove2me | Definitions.Def_WildeQIT_Covering_expectation
-- name    : WildeQIT_Covering_expectation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:50.943013+00:00
-- url     : https://prove2.me/theorems/4f9e6c47-cb6c-4558-9579-bb8e5d46a906
-- title:
--   Expectation $\mathbb E\{X\}$ of an operator-valued random variable
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $X:\Omega\to\mathcal L(\mathcal H)$ an operator-valued random variable on a finite-dimensional Hilbert space. Its **expectation** $\mathbb E\{X\}$ is the operator whose matrix entries are the expectations of the entries of $X$:
--
--   $$\mathbb E\{X\}_{ij}=\int_\Omega X(\omega)_{ij}\,d\mu(\omega).$$
--
--   This is the expectation in the operator Markov inequality, the Bernstein trick and the operator Chernoff bound.
--
--   **Formalization Note** The entries are Bochner integrals, which Lean sets to $0$ for a non-integrable entry; every statement using this definition assumes the entries it integrates are integrable.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §17.3, Lemma 17.3.2, p. 508

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §17.3, p. 508
(expectation `E{X}` of an operator-valued random variable).
-/

open MeasureTheory

namespace WildeQIT.Covering

/-- **Expectation of an operator-valued random variable** (Wilde, arXiv:1106.1445v8, §17.3,
Lemma 17.3.2, p. 508). For a random operator `X : Ω → L(H)` on a probability space `(Ω, μ)`,
`E{X}` is the operator whose matrix entries are the expectations of the entries of `X`:
`E{X}_{ij} = ∫ X(ω)_{ij} dμ(ω)`.

**Formalization Note.** The entries are Bochner integrals, which are `0` for a non-integrable
entry; the statements that use this definition assume the entries integrable, as the book
presupposes when it writes `E{X}`. -/
noncomputable def expectation {Ω m n : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Matrix m n ℂ) : Matrix m n ℂ :=
  Matrix.of fun i j => ∫ ω, X ω i j ∂μ

end WildeQIT.Covering


