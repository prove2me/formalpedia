-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_parityFn
-- name    : SelectiveDPT_Supplement_parityFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:25:47.906472+00:00
-- url     : https://prove2.me/theorems/32075927-48ce-488d-8fb4-ab9582e51ab9
-- title:
--   $\mathsf{PARITY}_n$ and the uniform distribution on $\{0,1\}^n$
-- statement:
--   For $x \in \{0,1\}^n$, $\mathsf{PARITY}_n(x) = x_1 \oplus \cdots \oplus x_n$, computed in $\mathbb Z_2$. The domain is all of $\{0,1\}^n$, and the hard distribution is uniform, $\mu_{\mathrm{P}}(x) = 2^{-n}$.
--
--   These are the function and the input distribution of the direct product theorems for $\mathsf{PARITY}_n$ (Theorems 1.7, 1.10(iii), 5.8).
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §1, p.4 (PARITY_n); proof of Theorem 1.7, p.32 (uniform hard distribution)

import Mathlib

namespace SelectiveDPT.Supplement

/-- `PARITY_n(x) = x_1 ⊕ ⋯ ⊕ x_n` for `x ∈ {0,1}^n` (arXiv:2609.26678, §1, p.4, the `PARITY_n`
problem; §4.1.3, pp.31–32), computed in `ZMod 2`. The domain is all of `{0,1}^n`. -/
def parityFn (n : ℕ) (x : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, x i

/-- The hard distribution of `PARITY_n` (arXiv:2609.26678, proof of Theorem 1.7, p.32: "Our hard
input distribution will be `|+⟩^{⊗([m]×[n])}`, which corresponds to a uniformly random choice of
input vectors"): uniform on `{0,1}^n`, `μ(x) = 2^{−n}`. -/
noncomputable def parityDist (n : ℕ) (_x : Fin n → ZMod 2) : ℝ :=
  1 / (2 : ℝ) ^ n

end SelectiveDPT.Supplement


