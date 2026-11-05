-- Prove2me | Definitions.Def_MosonyiPetz_blockAlgebra
-- name    : MosonyiPetz_blockAlgebra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:16.601805+00:00
-- url     : https://prove2.me/theorems/2741f0ef-6e50-4621-85d0-85ef611968ad
-- title:
--   The algebra $\{\sum_iA_i\otimes I_m\otimes E_{ii}\}\subset M_d\otimes M_m\otimes M_K$
-- statement:
--   For $d,m,K\in\mathbb N$, the set
--
--   $$\mathcal A_{d,m,K}=\Big\{\sum_{i=1}^KA_i\otimes I_m\otimes E_{ii}:\ A_i\in M_d\Big\}\subset M_d\otimes M_m\otimes M_K,$$
--
--   where $E_{ij}$ are the matrix units of $M_K$. It is the algebra $\bigoplus_{j=1}^KM_d$ with all multiplicities $m$ and all dimensions $d$, written in the coordinates of p.7; Proposition 4 describes the unitaries normalizing it.
--
--   **Formalization Note** Tensor products are Kronecker products on the index type `(Fin d × Fin m) × Fin K`; $E_{ii}$ is `Matrix.single i i 1`.
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, p.7

import Mathlib

open scoped Matrix Kronecker

namespace MosonyiPetz

/-- **The algebra ⊕_{j=1}^K M_d ⊗ I_m in the coordinates M_d ⊗ M_m ⊗ M_K.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, p.7: "we can suppose that all the blocks in A have the same multiplicity m and the same
dimension d, consequently A is isomorphic to ⊕_{j=1}^K Md. In this case dim(H) = mdK, and B is
isomorphic to Md ⊗ Mm ⊗ MK. Elements of A have the form Σ_i Ai ⊗ Im ⊗ Eii, where Ai is an element
of Md and {Eij : 1 ≤ i, j ≤ K} are the standard matrix units of MK."

`blockAlgebra d m K` is the set of matrices `Σ_{i} A_i ⊗ I_m ⊗ E_{ii}` on
`(ℂ^d ⊗ ℂ^m) ⊗ ℂ^K`, `A_i` ranging over `d × d` complex matrices.

**Formalization Note.** The tensor product is the Kronecker product `⊗ₖ`, with index type
`(Fin d × Fin m) × Fin K`; `E_{ii}` is `Matrix.single i i 1`. -/
def blockAlgebra (d m K : ℕ) : Set (Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ) :=
  {x | ∃ A : Fin K → Matrix (Fin d) (Fin d) ℂ,
    x = ∑ i, (A i ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ Matrix.single i i (1 : ℂ)}

end MosonyiPetz


