-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_padSub
-- name    : OracleStateHSP_Supplement_padSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:11:43.030625+00:00
-- url     : https://prove2.me/theorems/dfdc7bc3-0acb-46ae-b3e4-20aad723930c
-- title:
--   Padded hidden subgroups $H = \mathbb Z_2^r \oplus \tilde H$ (eq. (72))
-- statement:
--   Let $r, m \in \mathbb N$ and $G = \mathbb Z_2^r \oplus \mathbb Z_2^{2m}$. For a subgroup $\tilde H \le \mathbb Z_2^{2m}$, the padded subgroup is
--   $$
--   H = \{(h_1, h_2) : h_1 \in \mathbb Z_2^r,\ h_2 \in \tilde H\} \le G .
--   $$
--   In the hard family, $\tilde H$ ranges over the $m$-dimensional subspaces of $\mathbb Z_2^{2m}$, so $|H| = 2^{r+m}$ and $|G/H| = 2^m$; the padding $\mathbb Z_2^r$ carries no information.
--
--   **Formalization Note** $\mathbb Z_2^r$ and $\mathbb Z_2^{2m}$ are the published `K r` and `V (2m)`. Over $\mathbb Z_2$ every additive subgroup is a subspace, so the $m$-dimensional subspaces are the subgroups with $2^m$ elements.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (72), p.44

import Mathlib
import Definitions.Def_OracleStateHSP_K
import Definitions.Def_OracleStateHSP_V

namespace OracleStateHSP

namespace Supplement

/-- The hidden subgroups of the hard family of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (72), p.44: for a subgroup
`H̃ ≤ Z_2^(2m)`, `H = {(h_1, h_2) : h_1 ∈ Z_2^r, h_2 ∈ H̃} ≤ G = Z_2^r ⊕ Z_2^(2m)`.

**Formalization Note.** `Z_2^r` and `Z_2^(2m)` are the published `K r` and `V (2m)`
(`Fin _ → ZMod 2`); `H = ⊤ × H̃`. In the theorem `H̃` ranges over the `m`-dimensional subspaces
of `Z_2^(2m)`, i.e. the additive subgroups of cardinality `2^m` (over `Z_2` every additive subgroup
is a subspace). -/
def padSub (r m : ℕ) (Ht : AddSubgroup (V (2 * m))) : AddSubgroup (K r × V (2 * m)) :=
  (⊤ : AddSubgroup (K r)).prod Ht

end Supplement

end OracleStateHSP


