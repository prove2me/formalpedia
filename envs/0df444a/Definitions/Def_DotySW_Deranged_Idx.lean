-- Prove2me | Definitions.Def_DotySW_Deranged_Idx
-- name    : DotySW_Deranged_Idx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:37.446333+00:00
-- url     : https://prove2.me/theorems/86fa393f-5abe-4fbf-8a78-d2a12d3edd8f
-- title:
--   Basis labels of $N$ tensor positions over $\mathbb C^n$
-- statement:
--   Let $V=\mathbb C^n$ with standard basis $e_1,\dots,e_n$ and dual basis $e_1^*,\dots,e_n^*$. The labels of a tensor space with $N$ positions are the functions $u$ from the $N$ positions to the $n$ basis indices. For mixed tensor space $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$, where $N=r+s$, the label $u$ stands for the basis vector
--
--   $$
--   e_{u(0)}\otimes\cdots\otimes e_{u(r-1)}\otimes e^*_{u(r)}\otimes\cdots\otimes e^*_{u(r+s-1)}.
--   $$
--
--   Every construction of this mission is written in these coordinates.
--
--   **Formalization Note** Positions are numbered from $0$. The paper's position $-j$ with $1\le j\le s$ is position $r+j-1$ here.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, unnumbered, p. 9

import Mathlib

namespace DotySW.Deranged

/-- **Basis labels of a tensor space with `N` positions.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, unnumbered, p. 9.

`Idx n N` labels the standard basis of `N` tensor positions over `V = ℂ^n`. For mixed tensor
space `V^{r,s}` (with `N = r + s`) the label `u` stands for
`e_{u 0} ⊗ ⋯ ⊗ e_{u (r-1)} ⊗ e*_{u r} ⊗ ⋯ ⊗ e*_{u (r+s-1)}`.

**Formalization Note** Positions are 0-based; the paper's position `-j` (`1 ≤ j ≤ s`) is the
0-based position `r + j - 1` (`Fin.natAdd r`). A vector of `V^{r,s}` is a function
`Idx n (r + s) → ℂ` of coordinates in this basis. -/
abbrev Idx (n N : ℕ) : Type := Fin N → Fin n

end DotySW.Deranged


