-- Prove2me | Definitions.Def_MatchVec3_OffDiagIn
-- name    : MatchVec3_OffDiagIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:50.664574+00:00
-- url     : https://prove2.me/theorems/e2b64ff2-e5c4-440b-a73d-a4bf3172e2d9
-- title:
--   All off-diagonal inner products lie in $\{\alpha,\beta\}$
-- statement:
--   The lists $U,V$ have **off-diagonal residues in $\{\alpha,\beta\}$** if $\langle u_i,v_j\rangle\in\{\alpha,\beta\}$ for all $i\neq j$.
--
--   It does not assert that both values occur. Together with a zero diagonal this makes the family 3-restricted.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 2.3, p.9

import Mathlib

namespace MatchVec3

/-- All off-diagonal inner products lie in `{α, β}` (Aggarwal, Obremski, STOC 2027 submission
(manuscript sha256 44199413…), Lemma 2.3, p.9: "with off-diagonal residues α, β").

**Formalization Note** It does not assert that both values occur. Together with a zero diagonal this
makes the family 3-restricted. -/
def OffDiagIn {m n K : ℕ} (U V : Fin K → Fin n → ZMod m) (α β : ZMod m) : Prop :=
  ∀ i j, i ≠ j → U i ⬝ᵥ V j = α ∨ U i ⬝ᵥ V j = β

end MatchVec3


