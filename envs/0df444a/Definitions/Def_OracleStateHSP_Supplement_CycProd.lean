-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_CycProd
-- name    : OracleStateHSP_Supplement_CycProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:05:31.757597+00:00
-- url     : https://prove2.me/theorems/c671c92a-265d-4745-93b9-3440db104795
-- title:
--   The finite abelian group $\mathbb Z_{M_1} \times \dots \times \mathbb Z_{M_n}$ (eq. (10))
-- statement:
--   For $n \in \mathbb N$ and moduli $M_1, \dots, M_n$, the group
--   $$
--   G = \mathbb Z_{M_1} \times \mathbb Z_{M_2} \times \dots \times \mathbb Z_{M_n}
--   $$
--   has as elements the tuples $g = (g_1, \dots, g_n)$ with $g_l \in [M_l] = \{0, \dots, M_l - 1\}$, added componentwise modulo $M_l$. By the fundamental theorem of finite abelian groups every finite abelian group is of this form. The dual group $\hat G$ is labelled by tuples $\lambda = (\lambda_1, \dots, \lambda_n)$ of the same shape, so it is represented by the same type.
--
--   **Formalization Note** $\mathbb Z_{M_l}$ is `ZMod (M l)` and the index $l$ runs over $0, \dots, n-1$. The theorems using this type assume every $M_l \ge 1$ (`NeZero`), which makes $G$ finite.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (10), p.15

import Mathlib

namespace OracleStateHSP

namespace Supplement

/-- The finite abelian group `G ≅ Z_(M_1) × ⋯ × Z_(M_n)` of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (10), p.15: an element is
a tuple `g = (g_1, …, g_n)` with `g_l ∈ [M_l]`, added componentwise modulo `M_l`. The dual group
`Ĝ` is labelled by tuples `λ` of the same shape (p.15), so it is the same type.

**Formalization Note.** `Z_(M_l)` is `ZMod (M l)`; indices `l` are `0, …, n − 1`. The theorems
that use this type assume `NeZero (M l)` for every `l` (every modulus `M_l ≥ 1`), which makes the
group finite. Quantifying over `n` and `M` covers every finite abelian group up to isomorphism. -/
abbrev CycProd (n : ℕ) (M : Fin n → ℕ) : Type := (l : Fin n) → ZMod (M l)

end Supplement

end OracleStateHSP


