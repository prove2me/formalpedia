-- Prove2me | Definitions.Def_ICSCompute_piTensor
-- name    : ICSCompute_piTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:06.742982+00:00
-- url     : https://prove2.me/theorems/b8803947-6cb3-43ed-b07d-d22a961a2d45
-- title:
--   Tensor product $\bigotimes_i M_i$ of a finite family of operators
-- statement:
--   For operators $M_i$ on registers $K_i$, indexed by a finite set $I$, the tensor product $\bigotimes_{i\in I} M_i$ acts on $\bigotimes_i K_i$ with matrix entries
--   $$\Big(\bigotimes_i M_i\Big)_{x,y} = \prod_{i} (M_i)_{x_i, y_i}.$$
--   The empty tensor product is the $1\times1$ identity.
--
--   The construction is used for the local operations $\bigotimes_i \mathrm{CJ}(A_i)$ in the indefinite operator, for $U(x) = \bigotimes_i U_{i,h_i(x)}$, and for the blocks $\bigotimes_i B^{u_i,v_i}_{i,a_i}$ of the validity proof.
--
--   **Formalization Note** The tensor factors are indexed by dependent functions on the finite index type; the order of factors plays no role at the level of entries.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 4.3, p.18; §6.1, pp.31–35 (PDF pp.20, 33–37)

import Mathlib

namespace ICSCompute

/-- **Tensor product `⨂ᵢ Mᵢ` of a family of operators** (Shmueli, *What Can Be Computed with
Indefinite Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606,
used in Definition 4.3, p.18, and throughout §6.1, pp.31–35).

For operators `Mᵢ` on the registers `Kᵢ`, `⨂ᵢ Mᵢ` acts on `⨂ᵢ Kᵢ` with matrix entries
`(⨂ᵢ Mᵢ)_{x, y} = ∏ᵢ (Mᵢ)_{xᵢ, yᵢ}`.

**Formalization Note** The tensor product of a family indexed by a finite type `ι` is indexed by
the dependent functions `(i : ι) → κ i`; the order of the factors plays no role at the level of
entries. An empty family gives the `1 × 1` identity (the empty product is `1`). -/
def piTensor {ι : Type*} [Fintype ι] {κ : ι → Type*} (M : (i : ι) → Matrix (κ i) (κ i) ℂ) :
    Matrix ((i : ι) → κ i) ((i : ι) → κ i) ℂ :=
  Matrix.of fun x y => ∏ i, M i (x i) (y i)

end ICSCompute


