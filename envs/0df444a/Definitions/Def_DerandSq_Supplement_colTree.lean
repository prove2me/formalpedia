-- Prove2me | Definitions.Def_DerandSq_Supplement_colTree
-- name    : DerandSq_Supplement_colTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:03:39.846193+00:00
-- url     : https://prove2.me/theorems/0e75ca06-a9a4-4e26-b522-e17bd87030d5
-- title:
--   Colour-$i$ tree operator $t_i = \sum_j \lambda(m_{i,j})$ on $\ell^2(\Gamma_{\vec d, r})$
-- statement:
--   Fix $r$ colours and degrees $d_1, \dots, d_r$, and let
--
--   $$
--   \Gamma = \Gamma_{\vec d, r} = \mathop{\ast}_{i=1}^{r} \mathop{\ast}_{j=1}^{d_i} \mathbb Z_2
--   $$
--
--   be the free product of $D = d_1 + \cdots + d_r$ copies of $\mathbb Z_2$, with canonical free involutive generators $m_{i,j}$. For each colour $i$,
--
--   $$
--   t_i = \sum_{j=1}^{d_i} \lambda(m_{i,j})
--   $$
--
--   on $\ell^2(\Gamma)$, where $\lambda$ is the left-regular representation. The Cayley graph of $\Gamma$ is the infinite $D$-regular tree in which every vertex has $d_i$ neighbours of colour $i$, and $t_i$ is the adjacency operator of its colour-$i$ edges. The tuple $t = (t_1, \dots, t_r)$ is the limit of the permutation-conjugated adjacency matrices of §5.
--
--   **Formalization Note** $\Gamma$ is the published `DerandSq.Gam D`; $m_{i,j}$ is the generator with index `finSigmaFinEquiv ⟨i, j⟩`, so the generators are split into consecutive blocks of sizes $d_1, \dots, d_r$. Colours and labels are 0-based.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §5, p.24

import Mathlib
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_leftReg

namespace DerandSq.Supplement

/-- The colour-`i` tree operator `t_i = ∑_{j=1}^{d_i} λ(m_{i,j})` of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §5, p.24, on
`ℓ²(Γ)` with `Γ = Γ_{d,r} = ∗_{i=1}^r ∗_{j=1}^{d_i} Z_2` and `m_{i,j}` its canonical free
involutive generators.

**Formalization Note** `Γ_{d,r}` is the published `DerandSq.Gam D` (`Z_2^{∗D}`) with
`D = ∑_i d_i`; the generator `m_{i,j}` is `DerandSq.mGen (finSigmaFinEquiv ⟨i, j⟩)`, so the
`D` generators are split into consecutive blocks of sizes `d_1, …, d_r` (any bijection gives an
isomorphic group). Colours and labels are 0-based (`Fin r`, `Fin (d i)`). -/
noncomputable def colTree {r : ℕ} (d : Fin r → ℕ) (i : Fin r) :
    DerandSq.L2 (DerandSq.Gam (∑ i, d i)) →L[ℂ] DerandSq.L2 (DerandSq.Gam (∑ i, d i)) :=
  ∑ j : Fin (d i), DerandSq.leftReg (DerandSq.mGen (finSigmaFinEquiv ⟨i, j⟩))

end DerandSq.Supplement


