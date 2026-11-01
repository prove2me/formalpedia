-- Prove2me | Definitions.Def_SeqHolevo_codebookLaw
-- name    : SeqHolevo_codebookLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:07.870916+00:00
-- url     : https://prove2.me/theorems/14bfe34e-32bc-4103-b2a1-9396037f6594
-- title:
--   Law of the random codebook
-- statement:
--   For a distribution $p_X$ on the input space $X$, the random codebook draws each codeword $x^n(m)\in X^n$ independently from $p_{X^n}(x^n)=\prod_{i=1}^np_X(x_i)$. Its law on codebooks $(x^n(m))_{m\in\mathcal M}$ is the product measure
--
--   $$\big(p_X^{\otimes n}\big)^{\otimes|\mathcal M|}.$$
--
--   **Formalization Note** $p_X$ is any measure on any measurable space; codebooks are `Fin M → Fin n → X`.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, §II, p.2 (Codebook Construction)

import Mathlib

open MeasureTheory

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, §II, p.2 (PDF page), "Codebook Construction": "for every message `m ∈ 𝓜`, generate a
codeword `xⁿ(m) ≡ x_1(m) ⋯ x_n(m)` randomly and independently according to
`p_{Xⁿ}(xⁿ) ≡ ∏_{i=1}^n p_X(x_i)`". This is the law `(μ^{⊗n})^{⊗M}` of the random codebook
`C : Fin M → Fin n → X`.

**Formalization Note.** `p_X` is any measure `μ` on any measurable space `X` (the paper: "it does
not matter whether the classical input x is discrete or continuous"); the mission applies it to
probability measures. `Measure.pi` is the product measure. -/
noncomputable def codebookLaw {X : Type*} [MeasurableSpace X] (μ : Measure X) (n M : ℕ) :
    Measure (Fin M → Fin n → X) :=
  Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ))

end SeqHolevo


