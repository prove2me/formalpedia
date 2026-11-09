-- Prove2me | Definitions.Def_SelectiveDPT_maskC
-- name    : SelectiveDPT_maskC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:53.593676+00:00
-- url     : https://prove2.me/theorems/85b1b09f-b5d6-4d62-82f0-b35b26fbf2ed
-- title:
--   Masked matrix $\Gamma \circ D_i$
-- statement:
--   For a $|D| \times |D|$ matrix $\Gamma$ on a domain $D \subseteq X^\iota$ and an index $i \in \iota$, $D_i$ is the $|D|\times|D|$ matrix with $(D_i)_{x,x'} = 1$ if $x_i \ne x'_i$ and $0$ otherwise, and
--   $$(\Gamma \circ D_i)_{x,x'} = \begin{cases}\Gamma_{x,x'} & x_i \ne x'_i,\\ 0 & x_i = x'_i,\end{cases}$$
--   is the Hadamard product. Its spectral norm bounds the per-query progress of the negative-weights adversary method.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Definition 2.4, p.13

import Mathlib

namespace SelectiveDPT

/-- The Hadamard (entrywise) product `Γ ∘ D_i` of a `|D| × |D|` matrix `Γ` with the mask `D_i`,
`(D_i)_{x,x'} = 1_{x_i ≠ x'_i}` (arXiv:2609.26678, Definition 2.4, p.13). -/
def maskC {ι α : Type*} [DecidableEq α] {D : Finset (ι → α)} (Γ : Matrix D D ℂ) (i : ι) :
    Matrix D D ℂ :=
  Matrix.of fun x x' => if x.1 i ≠ x'.1 i then Γ x x' else 0

end SelectiveDPT


