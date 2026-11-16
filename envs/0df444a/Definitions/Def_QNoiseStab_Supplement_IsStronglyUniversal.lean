-- Prove2me | Definitions.Def_QNoiseStab_Supplement_IsStronglyUniversal
-- name    : QNoiseStab_Supplement_IsStronglyUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:20:15.699073+00:00
-- url     : https://prove2.me/theorems/a94fd1d6-cb3a-4951-879c-ba4ccf9552f9
-- title:
--   Strongly universal hash function family
-- statement:
--   A family $H=(h_i)_{i\in\iota}$ of functions from $\mathcal X$ to a finite set $\mathcal Y$, with $i$ drawn uniformly from the finite index set $\iota$, is **strongly universal** if for all $x\ne x'$ in $\mathcal X$ and all $y,y'\in\mathcal Y$,
--
--   $$
--   \Pr_{i}\bigl[h_i(x)=y\ \text{and}\ h_i(x')=y'\bigr]=\frac1{|\mathcal Y|^2}.
--   $$
--
--   Equivalently, the values at any two distinct points are uniform and independent. Examples are the convolution family $x\mapsto (a\circ x)\oplus b$ and the multiplication family $x\mapsto$ middle bits of $ax+b$.
--
--   **Formalization Note** The family is indexed, so repeated functions are allowed; the probability is the number of indices with the property divided by $|\iota|$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definition 4.1, p.17

import Mathlib

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- A **strongly universal hash function family** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definition 4.1, p.17: "H is a strongly
universal hash function family iff for every x ≠ x′ ∈ X and every y, y′ ∈ Y,
Pr_{h∈H}[h(x) = y and h(x′) = y′] = 1/|Y|^2"). The family is indexed by a finite type `ι` and
`h` is drawn uniformly from the index set, so multiplicities are allowed.

**Formalization Note** The probability is the count of indices `i` with `H i x = y ∧ H i x′ = y′`
divided by `|ι|`. -/
def IsStronglyUniversal {ι α β : Type} [Fintype ι] [Fintype β] [DecidableEq β]
    (H : ι → α → β) : Prop :=
  ∀ x x' : α, x ≠ x' → ∀ y y' : β,
    ((Finset.univ.filter fun i => H i x = y ∧ H i x' = y').card : ℝ) / Fintype.card ι =
      1 / (Fintype.card β : ℝ) ^ 2

end QNoiseStab.Supplement


