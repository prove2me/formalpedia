-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_regShift
-- name    : OracleStateHSP_Supplement_regShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:11:03.133618+00:00
-- url     : https://prove2.me/theorems/8d29f2f5-d147-4ef2-9bc2-759ff1d302ab
-- title:
--   Left-regular representation $R(g)|x\rangle|a\rangle = |x+g\rangle|a\rangle$ (eq. (69))
-- statement:
--   Let $G$ be a finite abelian group and work on $\mathbb C^{|G|} \otimes \mathbb C^2$, a group register with orthonormal basis $\{|x\rangle : x \in G\}$ and a flag qubit. The left-regular representation acts as a shift on the group register and trivially on the flag:
--   $$
--   R(g)\,|x\rangle|a\rangle = |x + g\rangle|a\rangle \qquad (x, g \in G,\ a \in \{0, 1\}).
--   $$
--
--   **Formalization Note** The basis is indexed by $G \times \{0, 1\}$ and $R(g)$ is the permutation matrix with entry $1$ at $((x+g, a), (x, a))$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (69), p.43

import Mathlib

namespace OracleStateHSP

namespace Supplement

/-- The left-regular representation on the group register of `C^|G| ⊗ C²` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (69),
p.43): `R(g)|x⟩|a⟩ = |x + g⟩|a⟩`, a shift on the group register acting trivially on the flag qubit.

**Formalization Note.** The basis of `C^|G| ⊗ C²` is `G × Fin 2`; the matrix entry at
`((y, b), (x, a))` is `1` if `y = x + g` and `b = a`, else `0`. -/
def regShift {G : Type*} [AddGroup G] [DecidableEq G] (g : G) :
    Matrix (G × Fin 2) (G × Fin 2) ℂ :=
  fun p q => if p.1 = q.1 + g ∧ p.2 = q.2 then 1 else 0

end Supplement

end OracleStateHSP


