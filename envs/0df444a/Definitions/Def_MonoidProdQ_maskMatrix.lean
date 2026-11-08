-- Prove2me | Definitions.Def_MonoidProdQ_maskMatrix
-- name    : MonoidProdQ_maskMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:06.332352+00:00
-- url     : https://prove2.me/theorems/6451ff72-bff4-4089-a31e-bf743417d066
-- title:
--   Masked adversary matrix $\Gamma\circ\Delta_i$
-- statement:
--   For a matrix $\Gamma$ indexed by a promise domain $D\subseteq\Sigma^I$ and a position $i\in I$, let $(\Delta_i)_{xy}=1[x_i\ne y_i]$. The **masked matrix** is the entrywise product
--
--   $$(\Gamma\circ\Delta_i)_{xy}=\begin{cases}\Gamma_{xy}, & x_i\ne y_i,\\ 0, & x_i=y_i.\end{cases}$$
--
--   Its spectral norm measures how much a single query to position $i$ can distinguish the inputs weighted by $\Gamma$. Letters are compared as elements of $\Sigma$, not through an encoding.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Adversary bounds, p.24

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, "Adversary bounds", p.24: the Hadamard product `Γ ∘ Δᵢ` with
`(Δᵢ)_{xy} = 1[xᵢ ≠ yᵢ]`: the entries of `Γ` at pairs of inputs whose letters at position `i`
differ are kept, the others set to `0`. Letters are compared as elements of the input alphabet,
not through any encoding. -/
def maskMatrix {I Sig : Type*} [DecidableEq Sig] {D : Finset (I → Sig)} (Γ : Matrix D D ℝ)
    (i : I) : Matrix D D ℝ :=
  Matrix.of fun x y => if (x : I → Sig) i ≠ (y : I → Sig) i then Γ x y else 0

end MonoidProdQ


