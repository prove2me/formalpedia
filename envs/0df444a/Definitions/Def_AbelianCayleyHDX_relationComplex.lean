-- Prove2me | Definitions.Def_AbelianCayleyHDX_relationComplex
-- name    : AbelianCayleyHDX_relationComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:16.650133+00:00
-- url     : https://prove2.me/theorems/a1899f4b-dfeb-4dd6-9f31-de139d6b1b4d
-- title:
--   The complex $X_H$ of a relation matrix
-- statement:
--   Let $H$ be a binary matrix with columns $[M]$, $\Gamma_H = \mathbb F_2^M / R_H$ and $s_i = e_i + R_H$. The complex $X_H$ has vertex set $\Gamma_H$, Cayley generators $S_H = \{s_i : i \in [M]\}$, and for every row with support $\{i, j, k\}$ and every $g \in \Gamma_H$ the triangle
--   $$\{g,\ g + s_i,\ g + s_i + s_j\},$$
--   with the uniform distribution on the triangles. Different orderings of $i, j, k$ give the same translation orbit.
--
--   **Formalization Note** $\Gamma_H$ is identified with $\mathbb F_2^n$ through an $\mathbb F_2$-linear map $\varphi : \mathbb F_2^M \to \mathbb F_2^n$ (the paper uses $v + R_H \mapsto Bv$ for a matrix $B$ whose rows are a basis of $\ker H$, p.9), so $s_i = \varphi(e_i)$; the theorems assume $\varphi$ onto with kernel $R_H$. All ordered pairs $i \ne j$ from the support of a row are used.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The complex `X_H`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9): for a binary matrix `H` with columns `κ`
and the generators `s_i = e_i + R_H` of `Γ_H = 𝔽₂^κ / R_H`, the triangles
`{g, g + s_i, g + s_i + s_j}` for every row with support `{i, j, k}` and every `g ∈ Γ_H`.

**Formalization Note** `Γ_H` is identified with `𝔽₂ⁿ` by an `𝔽₂`-linear map `φ : 𝔽₂^κ → 𝔽₂ⁿ`
(in the paper `v + R_H ↦ Bv`, p.9; the hypotheses that `φ` is onto with kernel `R_H` are stated
where used), so `s_i = φ(e_i)`. The triangle set is the set of `{g, g + s_i, g + s_i + s_j}` over
all rows `r`, all `g` and all ordered pairs `i ≠ j` in the support of row `r` (every ordering of the
support is allowed, as the paper notes they give the same orbits). -/
def relationComplex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (H : Matrix ι κ (ZMod 2)) (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n) : Finset (Finset (Vec n)) :=
  ((Finset.univ : Finset (ι × Vec n × κ × κ)).filter
      (fun x => x.2.2.1 ≠ x.2.2.2 ∧ H x.1 x.2.2.1 ≠ 0 ∧ H x.1 x.2.2.2 ≠ 0)).image
    (fun x => ({x.2.1, x.2.1 + φ (Pi.single x.2.2.1 1),
      x.2.1 + φ (Pi.single x.2.2.1 1) + φ (Pi.single x.2.2.2 1)} : Finset (Vec n)))

end AbelianCayleyHDX


