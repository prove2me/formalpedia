-- Prove2me | Definitions.Def_DerandSq_dsTree
-- name    : DerandSq_dsTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:53.88654+00:00
-- url     : https://prove2.me/theorems/f08f808e-d301-490a-be24-d7d627ba7dcd
-- title:
--   $T_d \circledS H$, the derandomized square of the infinite tree
-- statement:
--   Let $T_d$ be the infinite $d$-regular tree, realized as the Cayley graph of $\Gamma_d$: the neighbours of $v$ are $v m_1, \dots, v m_d$. At every tree vertex $c$ place a copy of $H$ on its $d$ neighbours, with an edge $\{c m_i, c m_j\}$ for every edge $\{i, j\}$ of $H$. The graph formed by all these edges is **$T_d \circledS H$**, the derandomized square of $T_d$ via $H$. Equivalently, for $g, h \in \Gamma_d$,
--   $$
--   g \sim h \iff h = g\, m_i m_j \text{ for some } \{i, j\} \in E(H).
--   $$
--   Each vertex has $dk$ neighbours when $H$ is $k$-regular.
--
--   **Formalization Note** Vertices are elements of $\Gamma_d$ with right multiplication, as in the paper's labelling ("if $w = vi$ then $wi = v$").
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §4.2, p.22

import Mathlib
import Definitions.Def_DerandSq_mGen

namespace DerandSq

/-- `T_d Ⓢ H`, the derandomized square of the infinite `d`-regular tree `T_d` via `H`, as a graph
on `Γ_d` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §4.2, p.22). The tree `T_d` is the Cayley graph of `Γ_d` with neighbours
`v m_1, …, v m_d` of `v` ("if w = vi then wi = v"); at every tree vertex `c` a copy of `H` is
placed on the neighbours of `c`, with edges `{c m_i, c m_j}` for `{i, j} ∈ E(H)`. Equivalently
`g ~ h` iff `h = g m_i m_j` for some edge `{i, j}` of `H` (take `c = g m_i`).

**Formalization Note** The vertex set is `Γ_d` with right multiplication, as in the paper's
labelling; `g ≠ h` holds automatically for a simple `H`. -/
def dsTree {d : ℕ} (H : SimpleGraph (Fin d)) : SimpleGraph (Gam d) where
  Adj g h := g ≠ h ∧ ∃ i j, H.Adj i j ∧ h = g * mGen i * mGen j
  symm := ⟨by
    rintro g h ⟨hne, i, j, hij, rfl⟩
    refine ⟨hne.symm, j, i, hij.symm, ?_⟩
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc (mGen j), mGen_mul_self, one_mul,
      mGen_mul_self, mul_one]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end DerandSq


